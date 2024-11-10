use std::fmt;

use crate::{
    code::{CodeIter, Span, Spanned},
    Error, Result,
};

use super::{is_ident_start, AstName, AstParse};

#[derive(Debug, Clone)]
pub enum AstTypeKind<'a> {
    Name(AstName<'a>),
    Array(Box<AstType<'a>>),
    GcPtr(Box<AstType<'a>>),
    StackPtr(Box<AstType<'a>>),
}
impl fmt::Display for AstTypeKind<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            AstTypeKind::Name(name) => fmt::Display::fmt(name, f),
            AstTypeKind::Array(ty) => {
                f.write_str("[]")?;
                fmt::Display::fmt(ty, f)?;
                Ok(())
            }
            AstTypeKind::GcPtr(ty) => {
                f.write_str("*")?;
                fmt::Display::fmt(ty, f)
            }
            AstTypeKind::StackPtr(ty) => {
                f.write_str("&")?;
                fmt::Display::fmt(ty, f)
            }
        }
    }
}

#[derive(Debug, Clone)]
pub struct AstType<'a> {
    span: Span,
    pub kind: AstTypeKind<'a>,
}
impl<'a> AstType<'a> {
    pub fn new(span: Span, kind: AstTypeKind<'a>) -> Self {
        Self { span, kind }
    }
}
impl Spanned for AstType<'_> {
    fn span(&self) -> Span {
        self.span
    }
}
impl fmt::Display for AstType<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Display::fmt(&self.kind, f)
    }
}

impl<'a> AstParse<'a> for AstType<'a> {
    fn parse(code: &mut CodeIter<'a>) -> Result<Self> {
        code.skip_whitespace();

        let pos = code.pos();
        if code.take_char_if(|ch| ch == '*').is_some() {
            Ok(AstType::new(
                pos.up_to(code),
                AstTypeKind::GcPtr(Box::new(code.parse()?)),
            ))
        } else if code.take_char_if(|ch| ch == '&').is_some() {
            Ok(AstType::new(
                pos.up_to(code),
                AstTypeKind::StackPtr(Box::new(code.parse()?)),
            ))
        } else if code.take_char_if(|ch| ch == '[').is_some() {
            let err_pos = code.pos();
            code.skip_whitespace();
            if code.take_char_if(|ch| ch == ']').is_none() {
                return Err(Error::Expected(err_pos, "`]`".into()));
            }
            Ok(AstType::new(
                pos.up_to(code),
                AstTypeKind::Array(Box::new(code.parse()?)),
            ))
        } else if code.peek().is_some_and(is_ident_start) {
            let name = AstName::parse(code)?;
            Ok(AstType::new(name.span(), AstTypeKind::Name(name)))
        } else {
            return Err(Error::Expected(code.pos(), "a type".into()));
        }
    }
}
