use std::{fmt, rc::Rc};

use crate::{
    code::{CodeIter, Span, Spanned},
    Error, Result,
};

use super::AstParse;

/// Cheap clones
#[derive(Debug, Clone)]
pub struct AstStr(Span, Rc<str>);

impl AstStr {
    pub fn as_str(&self) -> &str {
        &self.1
    }
}

impl Spanned for AstStr {
    fn span(&self) -> Span {
        self.0
    }
}

impl<'a> AstParse<'a> for AstStr {
    fn parse(code: &mut CodeIter<'a>) -> Result<Self> {
        code.skip_whitespace();

        let start = code.pos();
        code.take_char_if(|ch| ch == '"')
            .ok_or(Error::Expected(code.pos(), "`\"`".into()))?;

        if code.as_str().starts_with("\"\"") {
            return Err(Error::Todo(code.pos().to_span()));
        }

        let mut out = String::new();

        loop {
            match code.next_char().ok_or(Error::UnexpectedEnd(code.pos()))? {
                '\\' => match code.next_char().ok_or(Error::UnexpectedEnd(code.pos()))? {
                    'n' => out.push('\n'),
                    'r' => out.push('\r'),
                    't' => out.push('\t'),
                    '0' => out.push('\0'),
                    ch @ ('\\' | '\"' | '\'') => out.push(ch),
                    _ => return Err(Error::Expected(code.pos(), "Valid string escape".into())),
                },
                '\"' => break,
                ch => out.push(ch),
            }
        }

        Ok(Self(start.to(code.pos()), out.into()))
    }
}

impl fmt::Display for AstStr {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Debug::fmt(self.as_str(), f)
    }
}

pub(super) fn peek_str(code: &CodeIter) -> bool {
    code.peek().is_some_and(|ch| ch == '"')
}
