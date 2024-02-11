use std::{collections::HashMap, string::ToString};
use syn::{
    parse::{Error, ParseBuffer},
    parse_quote,
    punctuated::Punctuated,
    spanned::Spanned,
    Attribute, Expr, ExprLit, Ident, Lit, LitBool, LitStr, Meta, MetaNameValue, Pat, Token, Type,
};

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
pub fn get_attributes(attrs: &[Attribute]) -> impl Iterator<Item = &Attribute> + '_ {
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

/// Represents the properties of the `from` attribute.
pub struct FromFieldAttribute {
    /// The type from which the `TryFrom` trait is to be derived.
    pub ty: Type,
    /// A boolean indicating whether the source type should be iterated over.
    pub map: bool,
    /// A boolean indicating whether the source type should be unwrapped.
    pub unwrap: bool,
    /// The error name to be used for the `TryFrom` trait.
    pub error: Option<Ident>,
    /// The description of the error to be used for the `TryFrom` trait.
    pub description: Option<LitStr>,
}

/// Represents the properties of the `filter` attribute.
pub struct FilterFieldAttribute {
    /// The expression to be used for filtering the source type.
    pub expr: Expr,
    /// The error name to be used for the `TryFrom` trait.
    pub error: Ident,
    /// The description of the error to be used for the `TryFrom` trait.
    pub description: Option<LitStr>,
}

/// Represents the properties of the `try_convert` attribute for a container type.
pub enum FieldAttribute {
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
pub struct VariantAttribute {
    /// The pattern to be used for the `TryFrom` trait.
    pub from_arm: Pat,
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
pub struct ContainerAttribute {
    /// The type from which the `TryFrom` trait is to be derived.
    pub from: Type,
    /// The error name to be used for the `TryFrom` trait.
    pub error: Option<Ident>,
    /// The patterns to be excluded from the `TryFrom` trait.
    pub exclude: Vec<Pat>,
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
