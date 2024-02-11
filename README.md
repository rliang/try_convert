# `try_convert`

[![crates.io](https://img.shields.io/crates/v/try_convert.svg)](https://crates.io/crates/try_convert)
[![docs.rs](https://docs.rs/try_convert/badge.svg)](https://docs.rs/try_convert)

Auto-generate TryFrom and an error type, with minimal boilerplate.

## Usage

Add this to your `Cargo.toml`:

```toml
[dependencies]
try_convert = "0.1"
thiserror = "1.0" # Optional, but recommended
```

## Features

- `thiserror` (enabled by default): Use `thiserror` to derive `Error` for the error type.

## Container attributes

- `#[derive(TryConvert)]`: Derive `TryFrom` for a struct or enum.
- `#[try_convert(from = "source::Struct")]`: Derive `TryFrom<source::Struct>` for the annotated type.
- `#[try_convert(from = "source::Enum", exclude("D { .. }", "E ( .. )"))]`: Derive `TryFrom<source::Enum>` for the annotated type, excluding patterns `D { .. }` and `E (..)`.
- `#[try_convert(from = "source::Enum", error = "MyEnumError")]`: Derive `TryFrom<source::Enum>` for the annotated type, using `MyEnumError` as the error type.
- `#[try_convert(from = "source::Struct", error = "MyEnumError", description = "the struct is invalid")]`: Derive `TryFrom<source::Struct>` for the annotated type, using `MyEnumError` as the error type, with the description "the struct is invalid".

When `error` is not specified, the error type will be generated as `AnnotatedTypeFromSourceTypeError`.

## Field attributes

- `#[try_convert(from = "i32")]`: Uses `TryFrom<i32>` to convert the annotated field. You can also specify `error` and `description` to override the default error variant and message. If `error` is not specified, the error variant will be `<field>To<type>`.
- `#[try_convert(unwrap, from = "Option<i32>")]`: Tries to unwrap the source field, generating an error if it's `None`. You can also specify `error` and `description` to override the default error variant and message. If `error` is not specified, the error variant will be `SomeFieldIsNone`.
- `#[try_convert(map, from = "Vec<i32>")]`: Maps every element of the source `Vec` to the target type, using `TryFrom`. You can also specify `error` and `description` to override the default error variant and message.
- `#[try_convert(filter = "|x| x.is_empty()", error = "EmptyString", description = "the string is empty")]`: Filters the source field, generating an error if the filter returns `false`. `error` is required.
- `#[try_convert(get = "from.some_string")]`: Gets the value from the source field `some_string`. Precedes all other operations. Can only be specified once.

These attributes can be chained together to perform multiple operations on a single field.

## Variant attributes

- `#[try_convert(from = "source::Enum::A(f0)")]`: When the source is `source::Enum::A(f0)`, convert to the annotated variant.

## Example

The following code:

```rust
mod source {
    pub struct Struct {
        pub some_passthrough: usize,
        pub some_string: String,
        pub some_option: Option<i32>,
        pub some_vec: Option<Vec<i32>>,
        pub some_enum: Enum,
    }

    pub(crate) enum Enum {
        A(String),
        B { a: i32, b: i32 },
        C,
        D { c: i32 },
        E,
    }
}

use try_convert::TryConvert;

#[derive(TryConvert)]
#[try_convert(from = "source::Struct")]
pub struct MyStruct {
    some_passthrough: usize,
    #[try_convert(unwrap, from = "Option<i32>")]
    some_option: i32,
    #[try_convert(unwrap, from = "Option<Vec<i32>>")]
    #[try_convert(map, from = "Vec<i32>", error = "CustomErrorVariant")]
    some_vec: Vec<i16>,
    #[try_convert(from = "source::Enum")]
    some_enum: MyEnum,
    #[try_convert(get = "from.some_string")]
    #[try_convert(
        filter = "|x| !x.is_empty()",
        error = "EmptyString",
        description = "the string is empty"
    )]
    some_renamed_string: String,
}

#[derive(TryConvert)]
#[try_convert(from = "source::Enum", exclude("D { .. }", "E"), error = "MyEnumError")]
pub(crate) enum MyEnum {
    #[try_convert(from = "source::Enum::A(f0)")]
    A(String),
    #[try_convert(from = "source::Enum::B { a, b }")]
    B {
        #[try_convert(from = "i32")]
        a: i8,
        #[try_convert(get = "b")]
        #[try_convert(from = "i32")]
        renamed: i16,
    },
    C,
}
```

Will expand to:

```rust
#[derive(Debug, thiserror::Error)]
pub enum MyStructFromSourceStructError {
    #[error("some option is none")]
    SomeOptionIsNone,
    #[error("some vec is none")]
    SomeVecIsNone,
    #[error("custom error variant: {0:?}")]
    CustomErrorVariant(<i16 as TryFrom<i32>>::Error),
    #[error("some enum to my enum: {0:?}")]
    SomeEnumToMyEnum(<MyEnum as TryFrom<source::Enum>>::Error),
    #[error("the string is empty")]
    EmptyString,
}

impl TryFrom<source::Struct> for MyStruct {
    type Error = MyStructFromSourceStructError;

    fn try_from(from: source::Struct) -> Result<Self, Self::Error> {
        Ok({
            let some_passthrough = from.some_passthrough.into();
            let some_option = from
                .some_option
                .ok_or(MyStructFromSourceStructError::SomeOptionIsNone)?
                .into();
            let some_vec = from
                .some_vec
                .ok_or(MyStructFromSourceStructError::SomeVecIsNone)?
                .into_iter()
                .map(TryFrom::try_from)
                .collect::<Result<Vec<i16>, _>>()
                .map_err(MyStructFromSourceStructError::CustomErrorVariant)?
                .into();
            let some_enum = <MyEnum as TryFrom<source::Enum>>::try_from(from.some_enum)
                .map_err(MyStructFromSourceStructError::SomeEnumToMyEnum)?
                .into();
            let some_renamed_string = Some(from.some_string)
                .filter(|x| !x.is_empty())
                .ok_or(MyStructFromSourceStructError::EmptyString)?
                .into();
            Self {
                some_passthrough,
                some_option,
                some_vec,
                some_enum,
                some_renamed_string,
            }
        })
    }
}

#[derive(Debug, thiserror::Error)]
pub(crate) enum MyEnumError {
    #[error("a to i 8: {0:?}")]
    AToI8(<i8 as TryFrom<i32>>::Error),
    #[error("renamed to i 16: {0:?}")]
    RenamedToI16(<i16 as TryFrom<i32>>::Error),
    #[error("d")]
    D,
    #[error("e")]
    E,
}

impl TryFrom<source::Enum> for MyEnum {
    type Error = MyEnumError;

    fn try_from(from: source::Enum) -> Result<Self, Self::Error> {
        Ok(
            match from {
                source::Enum::D { .. } => return Err(MyEnumError::D),
                source::Enum::E => return Err(MyEnumError::E),
                source::Enum::A(f0) => {
                    let f0 = f0.into();
                    Self::A(f0)
                }
                source::Enum::B { a, b } => {
                    let a = <i8 as TryFrom<i32>>::try_from(a)
                        .map_err(MyEnumError::AToI8)?
                        .into();
                    let renamed = <i16 as TryFrom<i32>>::try_from(b)
                        .map_err(MyEnumError::RenamedToI16)?
                        .into();
                    Self::B { a, renamed }
                }
                source::Enum::C => Self::C,
            },
        )
    }
}
```
