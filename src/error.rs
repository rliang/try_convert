use convert_case::{Case, Casing};
use quote::{quote, ToTokens};
use syn::{parse_quote, Attribute, Field, Ident, LitStr, Variant, Visibility};

pub struct TryFromErrorBuilder {
    ident: Ident,
    vis: Visibility,
    variants: Vec<Variant>,
}

impl TryFromErrorBuilder {
    pub fn new(ident: Ident, vis: Visibility) -> Self {
        Self {
            vis,
            ident,
            variants: Vec::new(),
        }
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
    pub fn add_variant(
        &mut self,
        ident: &Ident,
        field: &Option<Field>,
        description: Option<LitStr>,
    ) {
        let mut variant: Variant = field.as_ref().map_or_else(
            || parse_quote!( #ident ),
            |field| parse_quote!( #ident ( #field ) ),
        );
        #[cfg(feature = "thiserror")]
        {
            let mut description = description.unwrap_or_else(|| {
                LitStr::new(&ident.to_string().to_case(Case::Lower), ident.span())
            });
            if field.is_some() {
                description = LitStr::new(
                    &format!("{}: {{0:?}}", description.value()),
                    description.span(),
                );
            };
            variant.attrs.push(parse_quote!( #[error(#description)] ));
        };
        self.variants.push(variant);
    }

    pub fn build(self) -> Option<impl ToTokens> {
        let ident = self.ident;
        let vis = self.vis;
        let variants = self.variants;
        if variants.is_empty() {
            return None;
        }
        #[cfg(feature = "thiserror")]
        let attr: Attribute = parse_quote!( #[derive(Debug, thiserror::Error)] );
        #[cfg(not(feature = "thiserror"))]
        let attr: Attribute = parse_quote!( #[derive(Debug)] );
        Some(quote! {
            #attr
            #vis enum #ident {
                #(#variants),*
            }
        })
    }
}
