#![doc = include_str!("../README.md")]
#![warn(clippy::all, clippy::pedantic, clippy::nursery, clippy::cargo)]
#![allow(clippy::too_many_lines)]

use convert_case::{Case, Casing};
use itertools::Itertools;
use proc_macro::TokenStream;
use quote::{format_ident, quote, ToTokens};
use std::{collections::HashMap, string::ToString};
use syn::{
    parse::{Error, ParseBuffer},
    parse2, parse_macro_input, parse_quote,
    punctuated::Punctuated,
    spanned::Spanned,
    Attribute, Data, DeriveInput, Expr, ExprLit, Fields, GenericArgument, Ident, Lit, LitBool,
    LitStr, Meta, MetaNameValue, Pat, PathArguments, PathSegment, Token, Type, TypePath, Variant,
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

/// Retrieves all attributes with the `try_convert` identifier.
///
/// # Arguments
///
/// * `attrs` - A reference to the list of attributes to be filtered.
///
/// # Returns
///
/// An iterator over the attributes with the `try_convert` identifier.
///
fn get_attributes(attrs: &[Attribute]) -> impl Iterator<Item = &Attribute> + '_ {
    attrs
        .iter()
        .filter(|attr| attr.path().is_ident("try_convert"))
}

/// Extracts the properties of a given attribute.
///
/// The properties are collected in the form of key-value pairs,
/// where the key is an identifier and the value is one or multiple literals.
///
/// # Arguments
///
/// * `attr` - A reference to the attribute whose properties are to be extracted.
///
/// # Returns
///
/// A map containing the properties of the given attribute.
///
fn get_attribute_properties(attr: &Attribute) -> Result<HashMap<String, Vec<Lit>>, Error> {
    attr.meta
        .require_list()?
        .parse_args_with(Punctuated::<Meta, Token![,]>::parse_terminated)?
        .into_iter()
        .map(|meta: Meta| {
            let key = meta.path().require_ident()?.to_string();
            let val = match meta {
                Meta::Path(_) => vec![Lit::Bool(parse_quote!(true))],
                Meta::NameValue(MetaNameValue { path, value, .. }) => {
                    if let Expr::Lit(ExprLit { lit, .. }) = value {
                        vec![lit]
                    } else {
                        return Err(Error::new(path.span(), "expected a literal"));
                    }
                }
                Meta::List(list) => list
                    .parse_args_with(Punctuated::<Lit, Token![,]>::parse_terminated)?
                    .into_iter()
                    .collect(),
            };
            Ok((key, val))
        })
        .collect::<Result<HashMap<String, Vec<Lit>>, _>>()
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

/// Generates an error variant for the `TryFrom` trait.
///
/// If the `thiserror` feature is enabled, the error variant is generated with the `#[error]` attribute.
/// If the description is not provided, the error variant is generated with the name of the identifier in lowercase.
///
/// # Arguments
///
/// * `ident` - The identifier to be used for the error variant.
/// * `fields` - The fields to be used for the error variant.
/// * `description` - The description to be used for the error variant.
///
/// # Returns
///
/// The error variant for the `TryFrom` trait.
fn generate_error_variant(
    ident: &Ident,
    fields: &Option<impl ToTokens>,
    description: Option<LitStr>,
) -> impl ToTokens {
    if cfg!(feature = "thiserror") {
        let description = description
            .unwrap_or_else(|| LitStr::new(&ident.to_string().to_case(Case::Lower), ident.span()));
        let description = if fields.is_some() {
            LitStr::new(
                &format!("{}: {{0:?}}", description.value()),
                description.span(),
            )
        } else {
            description
        };
        quote! {
            #[error(#description)]
            #ident #fields
        }
    } else {
        quote! { #ident #fields }
    }
}

/// Represents the properties of the `from` attribute.
struct FromFieldAttribute {
    /// The type from which the `TryFrom` trait is to be derived.
    ty: Type,
    /// A boolean indicating whether the source type should be iterated over.
    map: bool,
    /// A boolean indicating whether the source type should be unwrapped.
    unwrap: bool,
    /// The error name to be used for the `TryFrom` trait.
    error: Option<Ident>,
    /// The description of the error to be used for the `TryFrom` trait.
    description: Option<LitStr>,
}

/// Represents the properties of the `filter` attribute.
struct FilterFieldAttribute {
    /// The expression to be used for filtering the source type.
    expr: Expr,
    /// The error name to be used for the `TryFrom` trait.
    error: Ident,
    /// The description of the error to be used for the `TryFrom` trait.
    description: Option<LitStr>,
}

/// Represents the properties of the `try_convert` attribute for a container type.
enum FieldAttribute {
    /// The `get` attribute.
    Get(Expr),
    /// The `from` attribute.
    From(FromFieldAttribute),
    /// The `filter` attribute.
    Filter(FilterFieldAttribute),
}

impl TryFrom<&Attribute> for FieldAttribute {
    type Error = Error;

    fn try_from(attr: &Attribute) -> Result<Self, Error> {
        let mut value = get_attribute_properties(attr)?;
        if let Some(get) = value.remove("get") {
            let [Lit::Str(ref lit)] = get[..] else {
                return Err(Error::new(
                    attr.span(),
                    "expected a string literal for `get`",
                ));
            };
            if !value.is_empty() {
                return Err(Error::new(
                    attr.span(),
                    format!(
                        "unexpected arguments: {:?}",
                        value.keys().collect::<Vec<_>>()
                    ),
                ));
            }
            return Ok(Self::Get(lit.parse::<Expr>()?));
        }
        if let Some(from) = value.remove("from") {
            let [Lit::Str(ref lit)] = from[..] else {
                return Err(Error::new(
                    attr.span(),
                    "expected a string literal for `from`",
                ));
            };
            let ty = lit.parse::<Type>()?;
            let map = if let Some(map) = value.remove("map") {
                let [Lit::Bool(LitBool { value, .. })] = map[..] else {
                    return Err(Error::new(attr.span(), "expected a boolean for `map`"));
                };
                value
            } else {
                false
            };
            let unwrap = if let Some(unwrap) = value.remove("unwrap") {
                let [Lit::Bool(LitBool { value, .. })] = unwrap[..] else {
                    return Err(Error::new(attr.span(), "expected a boolean for `unwrap`"));
                };
                value
            } else {
                false
            };
            if map && unwrap {
                return Err(Error::new(
                    attr.span(),
                    "expected only one of `map` or `unwrap`",
                ));
            }
            let error = if let Some(error) = value.remove("error") {
                let [Lit::Str(ref lit)] = error[..] else {
                    return Err(Error::new(
                        attr.span(),
                        "expected a string literal for `error`",
                    ));
                };
                Some(lit.parse::<Ident>()?)
            } else {
                None
            };
            let description = if let Some(description) = value.remove("description") {
                let [Lit::Str(ref lit)] = description[..] else {
                    return Err(Error::new(
                        attr.span(),
                        "expected a string literal for `description`",
                    ));
                };
                Some(lit.clone())
            } else {
                None
            };
            if !value.is_empty() {
                return Err(Error::new(
                    attr.span(),
                    format!(
                        "unexpected arguments: {:?}",
                        value.keys().collect::<Vec<_>>()
                    ),
                ));
            }
            return Ok(Self::From(FromFieldAttribute {
                ty,
                map,
                unwrap,
                error,
                description,
            }));
        }
        if let Some(filter) = value.remove("filter") {
            let [Lit::Str(ref lit)] = filter[..] else {
                return Err(Error::new(
                    attr.span(),
                    "expected a string literal for `filter`",
                ));
            };
            let expr = lit.parse::<Expr>()?;
            let error = if let Some(error) = value.remove("error") {
                let [Lit::Str(ref lit)] = error[..] else {
                    return Err(Error::new(
                        attr.span(),
                        "expected a string literal for `error`",
                    ));
                };
                lit.parse::<Ident>()?
            } else {
                return Err(Error::new(
                    attr.span(),
                    "an `error` argument must be specified for `filter`",
                ));
            };
            let description = if let Some(description) = value.remove("description") {
                let [Lit::Str(ref lit)] = description[..] else {
                    return Err(Error::new(
                        attr.span(),
                        "expected a string literal for `description`",
                    ));
                };
                Some(lit.clone())
            } else {
                None
            };
            if !value.is_empty() {
                return Err(Error::new(
                    attr.span(),
                    format!(
                        "unexpected arguments: {:?}",
                        value.keys().collect::<Vec<_>>()
                    ),
                ));
            }
            return Ok(Self::Filter(FilterFieldAttribute {
                expr,
                error,
                description,
            }));
        }
        Err(Error::new(
            attr.span(),
            "expected one of `get`, `from`, or `filter`",
        ))
    }
}

/// Represents the properties of the `from` attribute for a variant type.
struct VariantAttribute {
    /// The pattern to be used for the `TryFrom` trait.
    from_arm: Pat,
}

impl TryFrom<&Attribute> for VariantAttribute {
    type Error = Error;

    fn try_from(attr: &Attribute) -> Result<Self, Error> {
        let mut props = get_attribute_properties(attr)?;
        let Some(from_arm) = props.remove("from") else {
            return Err(Error::new(
                attr.span(),
                "expected a `from` argument for the `try_convert` attribute",
            ));
        };
        let [Lit::Str(ref from_arm_lit)] = from_arm[..] else {
            return Err(Error::new(
                attr.span(),
                "expected a string literal for `from`",
            ));
        };
        let from_arm = from_arm_lit.parse_with(|x: &ParseBuffer| Pat::parse_multi(x))?;
        if !props.is_empty() {
            return Err(Error::new(attr.span(), "expected no other arguments"));
        }
        Ok(Self { from_arm })
    }
}

/// Represents the properties of the `try_convert` attribute for a container type.
struct ContainerAttribute {
    /// The type from which the `TryFrom` trait is to be derived.
    from: Type,
    /// The error name to be used for the `TryFrom` trait.
    error: Option<Ident>,
    /// The patterns to be excluded from the `TryFrom` trait.
    exclude: Vec<Pat>,
}

impl TryFrom<&Attribute> for ContainerAttribute {
    type Error = Error;

    fn try_from(attr: &Attribute) -> Result<Self, Error> {
        let mut props = get_attribute_properties(attr)?;
        let value = props.remove("from").ok_or_else(|| {
            Error::new(
                attr.span(),
                "expected a `from` argument for the `try_convert` attribute",
            )
        })?;
        let [Lit::Str(ref lit)] = value[..] else {
            return Err(Error::new(
                attr.span(),
                "expected a string literal for `from`",
            ));
        };
        let from = lit.parse::<Type>()?;
        let error = if let Some(error) = props.remove("error") {
            let [Lit::Str(ref lit)] = error[..] else {
                return Err(Error::new(
                    attr.span(),
                    "expected a string literal for `error`",
                ));
            };
            Some(lit.parse::<Ident>()?)
        } else {
            None
        };
        let exclude = if let Some(list) = props.remove("exclude") {
            list.into_iter()
                .map(|expr| {
                    let Lit::Str(lit) = expr else {
                        return Err(Error::new(
                            expr.span(),
                            "expected string literals for `exclude`",
                        ));
                    };
                    lit.parse_with(|x: &ParseBuffer| Pat::parse_single(x))
                })
                .collect::<Result<Vec<_>, _>>()?
        } else {
            vec![]
        };
        Ok(Self {
            from,
            error,
            exclude,
        })
    }
}

/// Processes the fields of a given struct or enum.
///
/// # Arguments
///
/// * `constructor` - The constructor to be used for the `TryFrom` trait, e.g., `Self` or `Self::Variant`.
/// * `from_var_ident` - The name of the variable to be tranformed, if it exists (i.e., is a struct).
/// * `fields` - A reference to the fields to be processed.
/// * `error_name` - The name of the error type to be used for the `TryFrom` trait.
///
/// # Returns
///
/// A tuple containing the constructor expression and the error variants for the `TryFrom` trait.
fn process_fields(
    constructor: impl ToTokens,
    from_var_ident: Option<&Ident>,
    fields: &Fields,
    error_name: &Ident,
) -> Result<(impl ToTokens, Vec<impl ToTokens>), Error> {
    let mut field_names = vec![];
    let mut field_values = vec![];
    let mut error_variants = vec![];

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
                let accessor = from_var_ident.as_ref().map_or_else(
                    || quote! { #ident },
                    |container_name| quote! { #container_name.#i },
                );
                (accessor, ident, title)
            },
            |ident| {
                let title = to_pascal_case(&ident);
                // to access the other field, if it has a container name, we use it, otherwise,
                // we assume that the field is unstructured as the ident
                let accessor = from_var_ident.as_ref().map_or_else(
                    || quote! { #ident },
                    |container_name| quote! { #container_name.#ident },
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
            .map_or(from_accessor, |expr| quote! { #expr });

        let mut last_transform: Option<FromFieldAttribute> = None;
        for field_attr in attrs {
            match field_attr {
                FieldAttribute::Get(_) => {}
                FieldAttribute::Filter(FilterFieldAttribute {
                    expr: filter,
                    error,
                    description,
                }) => {
                    expr = quote! { Some(#expr).filter(#filter).ok_or(#error_name::#error)? };
                    error_variants.push(generate_error_variant(&error, &None, description));
                }
                FieldAttribute::From(next_transform) => {
                    let to = next_transform.ty.clone();
                    let Some(transform) = last_transform.replace(next_transform) else {
                        continue;
                    };
                    let mut from = transform.ty;

                    if transform.unwrap {
                        let error = transform
                            .error
                            .clone()
                            .unwrap_or_else(|| format_ident!("{title}IsNone"));
                        error_variants.push(generate_error_variant(&error, &None, None));
                        from = get_inner_type(from)?;
                        expr = quote! { #expr.into_iter().next().ok_or(#error_name::#error)? };
                    }

                    if from.to_token_stream().to_string() == to.to_token_stream().to_string() {
                        continue;
                    }

                    title = format_ident!("{title}To{}", to_pascal_case(&to));
                    let error = transform.error.as_ref().unwrap_or(&title);

                    expr = if transform.map {
                        quote! { #expr.into_iter().map(TryFrom::try_from).collect::<Result<#to, _>>() }
                    } else {
                        quote! { <#to as TryFrom<#from>>::try_from(#expr) }
                    };
                    expr = quote! { #expr.map_err(#error_name::#error)? };

                    let (from, to) = if transform.map {
                        (get_inner_type(from.clone())?, get_inner_type(to.clone())?)
                    } else {
                        (from.clone(), to.clone())
                    };
                    error_variants.push(generate_error_variant(
                        error,
                        &Some(quote! { (<#to as TryFrom<#from>>::Error) }),
                        transform.description,
                    ));
                }
            }
        }

        field_values.push(expr);
    }
    let constructor = match fields {
        Fields::Named(_) => quote! {
            {
                #(
                    let #field_names = #field_values.into();
                )*
                #constructor { #(#field_names),* }
            }
        },
        Fields::Unnamed(_) => quote! {
            {
                #(
                    let #field_names = #field_values.into();
                )*
                #constructor ( #(#field_names),* )
            }
        },
        Fields::Unit => quote! { #constructor },
    };
    Ok((constructor, error_variants))
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

    let (impl_generics, ty_generics, where_clause) = generics.split_for_impl();

    match data {
        Data::Struct(data) => {
            let from_var_ident = format_ident!("from");
            let (self_constructor, error_variants) = process_fields(
                quote! { Self },
                Some(&from_var_ident),
                &data.fields,
                &error_name,
            )?;

            if error_variants.is_empty() {
                Ok(quote! {
                    impl #impl_generics From<#from_type> for #ident #ty_generics #where_clause {
                        fn from(#from_var_ident: #from_type) -> Self {
                            #self_constructor
                        }
                    }
                })
            } else {
                Ok(quote! {
                    #[derive(Debug, thiserror::Error)]
                    #vis enum #error_name {
                        #(#error_variants),*
                    }

                    #[automatically_derived]
                    impl #impl_generics TryFrom<#from_type> for #ident #ty_generics #where_clause {
                        type Error = #error_name;

                        fn try_from(#from_var_ident: #from_type) -> Result<Self, Self::Error> {
                            Ok(#self_constructor)
                        }
                    }
                })
            }
        }
        Data::Enum(data) => {
            let mut error_variants = vec![];
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
                let (constructor, errors) =
                    process_fields(quote! { Self::#variant }, None, fields, &error_name)?;
                error_variants.extend(errors.into_iter().map(|x| quote! { #x }));
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
                    error_variants.push(if cfg!(feature = "thiserror") {
                        let description =
                            LitStr::new(&error_ident.to_string().to_case(Case::Lower), arm.span());
                        quote! {
                            #[error(#description)]
                            #error_ident
                        }
                    } else {
                        quote! { #error_ident }
                    });
                    Ok(quote! { #from_type::#arm => return Err(#error_name::#error_ident) })
                })
                .collect::<Result<Vec<_>, _>>()?;
            let constructor = quote! {
                match from {
                    #(#excluded_arms,)*
                    #(#from_variants,)*
                }
            };
            if error_variants.is_empty() {
                Ok(quote! {
                    #[automatically_derived]
                    impl #impl_generics From<#from_type> for #ident #ty_generics #where_clause {
                        fn from(from: #from_type) -> Self { #constructor }
                    }
                })
            } else {
                let error = if cfg!(feature = "thiserror") {
                    quote! {
                        #[derive(Debug, thiserror::Error)]
                        #vis enum #error_name {
                            #(#error_variants),*
                        }
                    }
                } else {
                    quote! {
                        #[derive(Debug)]
                        #vis enum #error_name {
                            #(#error_variants),*
                        }
                    }
                };
                Ok(quote! {
                    #error

                    #[automatically_derived]
                    impl #impl_generics TryFrom<#from_type> for #ident #ty_generics #where_clause {
                        type Error = #error_name;

                        fn try_from(from: #from_type) -> Result<Self, Self::Error> {
                            Ok(#constructor)
                        }
                    }
                })
            }
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
