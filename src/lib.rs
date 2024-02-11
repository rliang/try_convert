#![doc = include_str!("../README.md")]
#![warn(clippy::all, clippy::pedantic, clippy::nursery, clippy::cargo)]
#![allow(clippy::too_many_lines)]

mod attrs;
mod error;
use attrs::{
    get_attributes, ContainerAttribute, FieldAttribute, FilterFieldAttribute, FromFieldAttribute,
    VariantAttribute,
};
use convert_case::{Case, Casing};
use error::TryFromErrorBuilder;
use itertools::Itertools;
use proc_macro::TokenStream;
use quote::{format_ident, quote, ToTokens};
use std::string::ToString;
use syn::{
    parse::Error, parse2, parse_macro_input, parse_quote, spanned::Spanned, Data, DeriveInput,
    Expr, Fields, GenericArgument, Ident, Pat, PathArguments, PathSegment, Type, TypePath, Variant,
};

/// Converts a given token stream to `PascalCase`, which is suitable for use as an enum variant or struct field name.
///
/// # Arguments
///
/// * `tokens` - A reference to the token stream to be converted to `PascalCase`.
///
/// # Returns
///
/// A string containing the `PascalCase` representation of the given token stream.
///
/// # Example
///
/// ```
/// let token_stream = quote! { some_field::Name<i32> };
/// let pascal_case = to_pascal_case(&token_stream);
/// assert_eq!(pascal_case, "SomeFieldNameI32");
/// ```
fn to_pascal_case(tokens: &impl ToTokens) -> Ident {
    let s = tokens
        .to_token_stream()
        .into_iter()
        .filter_map(|token| parse2::<Ident>(token.into()).ok())
        .map(|ident| ident.to_string())
        .map(|s| s.strip_prefix("r#").map(ToString::to_string).unwrap_or(s))
        .join("_")
        .to_case(Case::Pascal);
    format_ident!("{s}")
}

/// Extracts the inner type from a given type.
///
/// # Arguments
///
/// * `from` - The type from which the inner type is to be extracted.
///
/// # Returns
///
/// The inner type of the given type, if it exists.
fn get_inner_type(from: Type) -> Result<Type, Error> {
    let Type::Path(TypePath { path, .. }) = from else {
        return Err(Error::new(from.span(), "expected a path"));
    };
    let Some(PathSegment {
        arguments: PathArguments::AngleBracketed(abga),
        ..
    }) = path.segments.iter().last().cloned()
    else {
        return Err(Error::new(
            path.span(),
            "expected an angle-bracketed generic argument",
        ));
    };
    let Some(GenericArgument::Type(ty)) = abga.args.into_iter().next() else {
        return Err(Error::new(path.span(), "expected a generic type argument"));
    };
    Ok(ty)
}

/// Processes the fields of a given struct or enum.
///
/// # Arguments
///
/// * `constructor` - The constructor to be used for the `TryFrom` trait, e.g., `Self` or `Self::Variant`.
/// * `from_var_ident` - The name of the variable to be tranformed, if it exists (i.e., is a struct).
/// * `fields` - A reference to the fields to be processed.
/// * `error_name` - The name of the error type to be used for the `TryFrom` trait.
/// * `error_builder` - A reference to the error builder to be used for the `TryFrom` trait.
///
/// # Returns
///
/// An expression to construct the given struct or enum from the given fields.
fn process_fields(
    constructor: impl ToTokens,
    from_var_ident: Option<&Ident>,
    fields: &Fields,
    error_name: &Ident,
    error_builder: &mut TryFromErrorBuilder,
) -> Result<Expr, Error> {
    let mut field_names = vec![];
    let mut field_values = vec![];

    for (i, field) in fields.iter().enumerate() {
        let syn::Field {
            attrs,
            ident,
            ty: to_ty,
            ..
        } = field;

        let mut attrs = get_attributes(attrs)
            .map(FieldAttribute::try_from)
            .collect::<Result<Vec<_>, _>>()?;
        attrs.push(FieldAttribute::From(FromFieldAttribute {
            ty: to_ty.clone(),
            map: false,
            unwrap: false,
            error: None,
            description: None,
        }));

        let (from_accessor, local_alias, mut title) = ident.clone().map_or_else(
            || {
                // no ident, so we just give it any name based on the index
                let ident = format_ident!("f{i}");
                let title = format_ident!("F{i}");
                // to access the other field, if it has a container name, we use it, otherwise,
                // we assume that the field is unstructured as the local alias
                let accessor: Expr = from_var_ident.as_ref().map_or_else(
                    || parse_quote! { #ident },
                    |container_name| parse_quote! { #container_name.#i },
                );
                (accessor, ident, title)
            },
            |ident| {
                let title = to_pascal_case(&ident);
                // to access the other field, if it has a container name, we use it, otherwise,
                // we assume that the field is unstructured as the ident
                let accessor: Expr = from_var_ident.as_ref().map_or_else(
                    || parse_quote! { #ident },
                    |container_name| parse_quote! { #container_name.#ident },
                );
                (accessor, ident, title)
            },
        );
        field_names.push(local_alias);

        let mut expr = attrs
            .iter()
            .find_map(|attr| match attr {
                FieldAttribute::Get(expr) => Some(expr.clone()),
                _ => None,
            })
            .unwrap_or(from_accessor);

        let find_next_type = |attrs: &[FieldAttribute]| {
            attrs
                .iter()
                .find_map(|attr| match attr {
                    FieldAttribute::From(FromFieldAttribute { ty, .. }) => Some(ty.clone()),
                    _ => None,
                })
                .unwrap_or_else(|| to_ty.clone())
        };
        for (i, field_attr) in attrs.iter().enumerate() {
            match field_attr {
                FieldAttribute::Get(_) => {}
                FieldAttribute::Filter(FilterFieldAttribute {
                    expr: filter,
                    error,
                    description,
                }) => {
                    let to = find_next_type(&attrs[i + 1..]);
                    expr = parse_quote! { Some::<#to>(#expr).filter(#filter).ok_or(#error_name::#error)? };
                    error_builder.add_variant(error, &None, description.clone());
                }
                FieldAttribute::From(transform) => {
                    let to = find_next_type(&attrs[i + 1..]);
                    let mut from = transform.ty.clone();

                    if transform.unwrap {
                        let error = transform
                            .error
                            .clone()
                            .unwrap_or_else(|| format_ident!("{title}IsNone"));
                        error_builder.add_variant(&error, &None, None);
                        from = get_inner_type(from)?;
                        expr =
                            parse_quote! { #expr.into_iter().next().ok_or(#error_name::#error)? };
                    }

                    if from.to_token_stream().to_string() == to.to_token_stream().to_string() {
                        continue;
                    }

                    title = format_ident!("{title}To{}", to_pascal_case(&to));
                    let error = transform.error.as_ref().unwrap_or(&title);

                    expr = if transform.map {
                        parse_quote! { #expr.into_iter().map(TryFrom::try_from).collect::<Result<#to, _>>() }
                    } else {
                        parse_quote! { <#to as TryFrom<#from>>::try_from(#expr) }
                    };
                    expr = parse_quote! { #expr.map_err(#error_name::#error)? };

                    let (from, to) = if transform.map {
                        (get_inner_type(from.clone())?, get_inner_type(to.clone())?)
                    } else {
                        (from.clone(), to.clone())
                    };
                    error_builder.add_variant(
                        error,
                        &Some(parse_quote! { <#to as TryFrom<#from>>::Error }),
                        transform.description.clone(),
                    );
                }
            }
        }

        field_values.push(expr);
    }
    Ok(match fields {
        Fields::Named(_) => parse_quote! {
            {
                #(
                    let #field_names = #field_values.into();
                )*
                #constructor { #(#field_names),* }
            }
        },
        Fields::Unnamed(_) => parse_quote! {
            {
                #(
                    let #field_names = #field_values.into();
                )*
                #constructor ( #(#field_names),* )
            }
        },
        Fields::Unit => parse_quote! { #constructor },
    })
}

fn implement(
    DeriveInput {
        vis,
        ident,
        generics,
        data,
        attrs,
    }: &DeriveInput,
) -> Result<impl Into<TokenStream>, Error> {
    let container = get_attributes(attrs)
        .map(ContainerAttribute::try_from)
        .next()
        .transpose()?
        .ok_or_else(|| Error::new(ident.span(), "Expected a `try_convert` attribute."))?;
    let from_type = container.from;
    let error_name = container
        .error
        .unwrap_or_else(|| format_ident!("{ident}From{}Error", to_pascal_case(&from_type)));
    let mut error_builder = TryFromErrorBuilder::new(error_name.clone(), vis.clone());

    let (impl_generics, ty_generics, where_clause) = generics.split_for_impl();

    match data {
        Data::Struct(data) => {
            let from_var_ident = format_ident!("from");
            let self_constructor = process_fields(
                quote! { Self },
                Some(&from_var_ident),
                &data.fields,
                &error_name,
                &mut error_builder,
            )?;

            error_builder.build().map_or_else(|| Ok(quote! {
                impl #impl_generics From<#from_type> for #ident #ty_generics #where_clause {
                    fn from(#from_var_ident: #from_type) -> Self {
                        #self_constructor
                    }
                }
            }), |error| Ok(quote! {
                #error

                #[automatically_derived]
                impl #impl_generics TryFrom<#from_type> for #ident #ty_generics #where_clause {
                    type Error = #error_name;

                    fn try_from(#from_var_ident: #from_type) -> Result<Self, Self::Error> {
                        Ok(#self_constructor)
                    }
                }
            }))
        }
        Data::Enum(data) => {
            let mut from_variants = vec![];
            for variant in &data.variants {
                let Variant {
                    attrs,
                    ident: variant,
                    fields,
                    ..
                } = variant;
                let attr = get_attributes(attrs)
                    .map(VariantAttribute::try_from)
                    .collect::<Result<Vec<_>, _>>()?
                    .into_iter()
                    .next();
                let arm = if let Some(VariantAttribute { from_arm, .. }) = attr {
                    quote! { #from_arm  }
                } else if matches!(fields, Fields::Unit) {
                    quote! { #from_type::#variant  }
                } else {
                    return Err({
                        Error::new(
                            variant.span(),
                            "expected a `try_convert(from = \"...\")` attribute for variant with fields",
                        )
                    });
                };
                let constructor = process_fields(
                    quote! { Self::#variant },
                    None,
                    fields,
                    &error_name,
                    &mut error_builder,
                )?;
                from_variants.push(quote! { #arm => #constructor });
            }
            let excluded_arms = container
                .exclude
                .into_iter()
                .map(|arm| {
                    let error_ident = match &arm {
                        Pat::Ident(s) => to_pascal_case(&s.ident),
                        Pat::Path(s) => to_pascal_case(&s.path),
                        Pat::Struct(s) => to_pascal_case(&s.path),
                        Pat::TupleStruct(s) => to_pascal_case(&s.path),
                        _ => return Err(Error::new(arm.span(), "expected a path or pattern")),
                    };
                    error_builder.add_variant(&error_ident, &None, None);
                    Ok(quote! { #from_type::#arm => return Err(#error_name::#error_ident) })
                })
                .collect::<Result<Vec<_>, _>>()?;
            let constructor = quote! {
                match from {
                    #(#excluded_arms,)*
                    #(#from_variants,)*
                }
            };
            error_builder.build().map_or_else(|| Ok(quote! {
                #[automatically_derived]
                impl #impl_generics From<#from_type> for #ident #ty_generics #where_clause {
                    fn from(from: #from_type) -> Self { #constructor }
                }
            }), |error| Ok(quote! {
                #error
                #[automatically_derived]
                impl #impl_generics TryFrom<#from_type> for #ident #ty_generics #where_clause {
                    type Error = #error_name;

                    fn try_from(from: #from_type) -> Result<Self, Self::Error> {
                        Ok(#constructor)
                    }
                }
            }))
        }
        Data::Union(_) => Err(Error::new(
            ident.span(),
            "`TryConvert` cannot be derived for unions",
        )),
    }
}

#[proc_macro_derive(TryConvert, attributes(try_convert))]
pub fn try_convert(input: TokenStream) -> TokenStream {
    match implement(&parse_macro_input!(input as DeriveInput)) {
        Ok(tokens) => tokens.into(),
        Err(err) => err.to_compile_error().into(),
    }
}
