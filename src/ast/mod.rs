use std::fmt;

use crate::{
    code::{CodeIter, Span},
    Error, Result,
};

pub mod expr;
pub mod ident;
pub mod item;
pub mod num;
pub mod stmt;
pub mod str;
pub mod ty;

pub use self::{expr::*, ident::*, item::*, num::*, stmt::*, str::*, ty::*};

pub trait AstParse<'a>: Sized {
    fn parse(code: &mut CodeIter<'a>) -> Result<Self>;
}

impl<'a> CodeIter<'a> {
    pub fn parse<T: AstParse<'a>>(&mut self) -> Result<T> {
        T::parse(self)
    }
}

fn parse_separated<'a, T>(
    code: &mut CodeIter<'a>,
    open: char,
    close: char,
    mut parse_elem: impl FnMut(&mut CodeIter<'a>) -> Result<T>,
) -> Result<(Span, Vec<T>, Span)> {
    code.skip_whitespace();
    let pos = code.pos();
    code.take_char_if(|ch| ch == open)
        .ok_or_else(|| Error::Expected(code.pos(), format!("`{}`", open.escape_debug()).into()))?;
    let open_span = pos.up_to(code);
    code.with_newline_whitespace_in(true, |code| {
        let mut args = vec![];
        let mut sep = false;
        loop {
            let pos = code.pos();
            code.skip_whitespace();
            if code.peek().is_some_and(|ch| ch == close) {
                let pos = code.pos();
                code.next_char();
                return Ok((open_span, args, pos.up_to(code)));
            } else if !sep {
                args.push(parse_elem(code)?);
                sep = true;
            } else if sep && code.take_char_if(|ch| ch == ',').is_some() {
                sep = false;
            } else {
                return Err(Error::Expected(
                    pos,
                    format!("`{}` or `,`", close.escape_debug()).into(),
                ));
            }
        }
    })
}

#[derive(Debug, Clone)]
pub struct AstModule<'a> {
    pub items: Vec<item::AstItem<'a>>,
}

impl<'a> AstParse<'a> for AstModule<'a> {
    fn parse(code: &mut CodeIter<'a>) -> Result<Self> {
        let mut items = vec![];
        loop {
            code.skip_whitespace_and_newlines();
            if code.is_empty() {
                break;
            }
            items.push(code.parse()?);
        }

        Ok(Self { items })
    }
}

impl fmt::Display for AstModule<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        use fmt::Write;
        for item in &self.items {
            fmt::Display::fmt(item, f)?;
            f.write_char('\n')?;
        }
        Ok(())
    }
}
