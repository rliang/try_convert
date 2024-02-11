#[cfg(test)]
mod tests {
    mod source {
        pub struct Struct {
            pub some_passthrough: usize,
            pub some_string: String,
            pub some_option: Option<i32>,
            pub some_vec: Option<Vec<i32>>,
            pub some_enum: Enum,
        }

        #[allow(dead_code)]
        pub enum Enum {
            A(String),
            B { a: i32, b: i32 },
            C,
            D { c: i32 },
            E,
        }
    }

    use try_convert::TryConvert;

    #[derive(TryConvert, PartialEq, Eq, Debug)]
    #[try_convert(from = "source::Struct")]
    pub struct MyStruct {
        some_passthrough: usize,
        #[try_convert(unwrap, from = "Option<i32>")]
        some_option: i32,
        #[try_convert(unwrap, from = "Option<Vec<i32>>")]
        #[try_convert(
            filter = "|x| !x.is_empty()",
            error = "EmptyString",
            description = "the string is empty"
        )]
        #[try_convert(map, from = "Vec<i32>", error = "CustomErrorVariant")]
        some_vec: Vec<i16>,
        #[try_convert(from = "source::Enum")]
        some_enum: MyEnum,
        #[try_convert(get = "from.some_string")]
        some_renamed_string: String,
    }

    #[derive(TryConvert, PartialEq, Eq, Debug)]
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

    #[test]
    fn test_try_convert() {
        let source = source::Struct {
            some_passthrough: 42,
            some_string: "hello".to_string(),
            some_option: Some(42),
            some_vec: Some(vec![1, 2, 3]),
            some_enum: source::Enum::B { a: 1, b: 2 },
        };

        let result = MyStruct::try_from(source).unwrap();
        assert_eq!(result.some_passthrough, 42);
        assert_eq!(result.some_option, 42);
        assert_eq!(result.some_vec, vec![1, 2, 3]);
        assert_eq!(result.some_enum, MyEnum::B { a: 1, renamed: 2 });
        assert_eq!(result.some_renamed_string, "hello");
    }

    #[test]
    fn test_try_convert_error() {
        let source = source::Struct {
            some_passthrough: 42,
            some_string: "".to_string(),
            some_option: Some(42),
            some_vec: Some(vec![]),
            some_enum: source::Enum::B { a: 1, b: 2 },
        };

        let result = MyStruct::try_from(source);
        assert!(result.is_err());
        assert_eq!(result.unwrap_err().to_string(), "the string is empty");
    }
}
