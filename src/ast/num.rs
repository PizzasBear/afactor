use std::{fmt, num::NonZero};

use either::*;

use crate::{
    code::{CodeIter, Span, Spanned},
    Error, Result,
};

use super::AstParse;

const DECIMAL_FORMAT: u128 = lexical_core::NumberFormatBuilder::new()
    .digit_separator(NonZero::new(b'_'))
    .no_special(true)
    .internal_digit_separator(true)
    .build();
const BINARY_FORMAT: u128 = lexical_core::NumberFormatBuilder::rebuild(DECIMAL_FORMAT)
    .base_prefix(NonZero::new(b'b'))
    .mantissa_radix(2)
    .build();
const OCTAL_FORMAT: u128 = lexical_core::NumberFormatBuilder::rebuild(DECIMAL_FORMAT)
    .base_prefix(NonZero::new(b'o'))
    .mantissa_radix(2)
    .build();
const HEX_FORMAT: u128 = lexical_core::NumberFormatBuilder::rebuild(DECIMAL_FORMAT)
    .base_prefix(NonZero::new(b'x'))
    .mantissa_radix(16)
    .required_exponent_notation(true)
    .exponent_base(NonZero::new(2))
    .exponent_radix(NonZero::new(10))
    .build();

// #[test]
// fn test_lexical() {
//     let num = lexical_core::parse_with_options::<f64, { lexical_core::format::C11_HEX_LITERAL }>(
//         b"3.31p3",
//         &lexical_core::parse_float_options::HEX_FLOAT,
//     )
//     .unwrap();
//     assert_eq!(num, (0x331 * (1 << 3)) as f64 / 0x100 as f64);
// }

#[derive(Debug, Clone)]
pub struct AstUint(Span, u64);

impl AstUint {
    pub fn value(&self) -> u64 {
        self.1
    }
}

impl Spanned for AstUint {
    fn span(&self) -> Span {
        self.0
    }
}

impl<'a> AstParse<'a> for AstUint {
    fn parse(code: &mut CodeIter<'a>) -> Result<Self> {
        match AstNum::parse(code)? {
            AstNum::Uint(num) => Ok(num),
            AstNum::Float(num) => Err(Error::ExpectedButFound(
                num.span(),
                "an integer".into(),
                format!("the floating point number {}", num.value()).into(),
            )),
        }
    }
}

impl fmt::Display for AstUint {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Display::fmt(&self.1, f)
    }
}

#[derive(Debug, Clone)]
pub struct AstFloat(Span, f64);

impl AstFloat {
    pub fn value(&self) -> f64 {
        self.1
    }
}

impl Spanned for AstFloat {
    fn span(&self) -> Span {
        self.0
    }
}

impl<'a> AstParse<'a> for AstFloat {
    fn parse(code: &mut CodeIter<'a>) -> Result<Self> {
        let pos = code.pos();
        let radix: u32 = match (code.peek(), code.peek1().map(|ch| ch.to_ascii_lowercase())) {
            (Some('0'), Some('b')) => 2,
            (Some('0'), Some('o')) => 8,
            (Some('0'), Some('x')) => 16,
            _ => 10,
        };
        let (num, len) = match radix {
            10 => lexical_core::parse_partial_with_options::<f64, DECIMAL_FORMAT>(
                code.as_bytes(),
                &lexical_core::parse_float_options::STANDARD,
            ),
            16 => lexical_core::parse_partial_with_options::<f64, HEX_FORMAT>(
                code.as_bytes(),
                &lexical_core::parse_float_options::HEX_FLOAT,
            ),
            _ => return Err(Error::FloatRadix(pos, radix)),
        }
        .map_err(|err| Error::Lexical(pos, err))?;

        code.skipn_bytes(len);
        Ok(Self(pos.up_to(code), num))
    }
}

impl fmt::Display for AstFloat {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Display::fmt(&self.1, f)
    }
}

#[derive(Debug, Clone)]
pub enum AstNum {
    Uint(AstUint),
    Float(AstFloat),
}

impl AstNum {
    pub fn value(&self) -> Either<u64, f64> {
        match self {
            AstNum::Uint(num) => Left(num.value()),
            AstNum::Float(num) => Right(num.value()),
        }
    }
}

impl Spanned for AstNum {
    fn span(&self) -> Span {
        match self {
            AstNum::Uint(num) => num.span(),
            AstNum::Float(num) => num.span(),
        }
    }
}

impl<'a> AstParse<'a> for AstNum {
    fn parse(code: &mut CodeIter<'a>) -> Result<Self> {
        let pos = code.pos();
        let radix: u32 = match (code.peek(), code.peek1().map(|ch| ch.to_ascii_lowercase())) {
            (Some('0'), Some('b')) => 2,
            (Some('0'), Some('o')) => 8,
            (Some('0'), Some('x')) => 16,
            _ => 10,
        };
        let (num, len) = match radix {
            _ if code.peek().is_some_and(|ch| ch == '.') => Ok((0, 0)),
            2 => lexical_core::parse_partial_with_options::<u64, BINARY_FORMAT>(
                code.as_bytes(),
                &lexical_core::parse_integer_options::STANDARD,
            ),
            8 => lexical_core::parse_partial_with_options::<u64, OCTAL_FORMAT>(
                code.as_bytes(),
                &lexical_core::parse_integer_options::STANDARD,
            ),
            16 => lexical_core::parse_partial_with_options::<u64, HEX_FORMAT>(
                code.as_bytes(),
                &lexical_core::parse_integer_options::STANDARD,
            ),
            10 => lexical_core::parse_partial_with_options::<u64, DECIMAL_FORMAT>(
                code.as_bytes(),
                &lexical_core::parse_integer_options::STANDARD,
            ),
            _ => unreachable!(),
        }
        .map_err(|err| Error::Lexical(pos, err))?;

        if !code.as_str()[len..].starts_with(&['p', 'e', '.']) {
            code.skipn_bytes(len);
            Ok(Self::Uint(AstUint(pos.up_to(code), num)))
        } else {
            let (num, len) = match radix {
                10 => lexical_core::parse_partial_with_options::<f64, DECIMAL_FORMAT>(
                    code.as_bytes(),
                    &lexical_core::parse_float_options::STANDARD,
                ),
                16 => lexical_core::parse_partial_with_options::<f64, HEX_FORMAT>(
                    code.as_bytes(),
                    &lexical_core::parse_float_options::HEX_FLOAT,
                ),
                _ => return Err(Error::FloatRadix(pos, radix)),
            }
            .map_err(|err| Error::Lexical(pos, err))?;

            code.skipn_bytes(len);
            Ok(Self::Float(AstFloat(pos.up_to(code), num)))
        }
    }
}

impl fmt::Display for AstNum {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match &self {
            Self::Uint(num) => fmt::Display::fmt(num, f),
            Self::Float(num) => fmt::Display::fmt(num, f),
        }
    }
}
