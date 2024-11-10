use std::fmt;

use crate::{
    code::{CodeIter, Span},
    Error, Result,
};

use super::{kw, AstExpr, AstName, AstParse, AstType};

#[derive(Debug, Clone)]
pub struct AstLetStmt<'a> {
    pub let_kw: kw![let],
    pub name: AstName<'a>,
    pub ty: Option<AstType<'a>>,
    pub value: AstExpr<'a>,
}

#[derive(Debug, Clone)]
pub enum AstStmtKind<'a> {
    Expr(AstExpr<'a>),
    Let(AstLetStmt<'a>),
}

#[derive(Debug, Clone)]
pub struct AstStmt<'a> {
    pub span: Span,
    pub kind: AstStmtKind<'a>,
}

impl<'a> AstStmt<'a> {
    pub fn new(span: Span, kind: AstStmtKind<'a>) -> Self {
        Self { span, kind }
    }
}

impl fmt::Display for AstLetStmt<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str("let ")?;
        fmt::Display::fmt(&self.name, f)?;
        f.write_str(" = ")?;
        fmt::Display::fmt(&self.value, f)?;

        Ok(())
    }
}

impl fmt::Display for AstStmtKind<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            AstStmtKind::Expr(expr) => fmt::Display::fmt(expr, f),
            AstStmtKind::Let(decl) => fmt::Display::fmt(decl, f),
        }
    }
}

impl fmt::Display for AstStmt<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Display::fmt(&self.kind, f)
    }
}

// val v = 4;
// var v = 5;

impl<'a> AstParse<'a> for AstStmt<'a> {
    fn parse(code: &mut CodeIter<'a>) -> Result<Self> {
        code.skip_whitespace();
        let code = &mut code.with_newline_whitespace(false);

        let start = code.pos();
        let stmt = if let Ok(let_kw) = code.parse::<kw![let]>() {
            code.skip_whitespace();

            let name = AstName::parse(code)?;

            let ty = code
                .take_char_if(|ch| ch == ':')
                .map(|_| code.parse())
                .transpose()?;

            let pos = code.pos();
            code.skip_whitespace();
            if !code.next_char().is_some_and(|ch| ch == '=') {
                return Err(Error::Expected(
                    pos,
                    From::from(match ty {
                        Some(_) => "`=`",
                        None => "`=` or `:`",
                    }),
                ));
            }

            let value = code.parse()?;

            AstStmt::new(
                start.up_to(code),
                AstStmtKind::Let(AstLetStmt {
                    let_kw,
                    name,
                    ty,
                    value,
                }),
            )
        } else {
            let expr = code.parse()?;
            AstStmt::new(start.up_to(code), AstStmtKind::Expr(expr))
        };

        parse_endline(code)?;

        Ok(stmt)
    }
}

pub(super) fn parse_endline(code: &mut CodeIter) -> Result<()> {
    code.skip_whitespace();
    match code.take_char_if(|ch| matches!(ch, '\n' | ';')).is_some()
        || code.peek().is_none_or(|ch| matches!(ch, '}' | ']' | ')'))
    {
        true => Ok(()),
        false => Err(Error::Expected(
            code.pos(),
            "statement closing, e.g. newline, semicolon, closing brace".into(),
        )),
    }
}

#[derive(Debug, Clone)]
pub struct AstBlock<'a> {
    pub span: Span,
    pub stmts: Vec<AstStmt<'a>>,
}

impl fmt::Display for AstBlock<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str("{\n")?;
        let mut adapter = crate::pad_adapter::PadAdapter::new(f);
        for stmt in &self.stmts {
            write!(adapter, "{stmt}\n")?;
        }
        f.write_str("}")?;
        Ok(())
    }
}

impl<'a> AstParse<'a> for AstBlock<'a> {
    fn parse(code: &mut CodeIter<'a>) -> Result<Self> {
        let expected_pos = code.pos();
        code.skip_whitespace();

        let start = code.pos();
        code.take_char_if(|ch| ch == '{')
            .ok_or(Error::Expected(expected_pos, "`{`".into()))?;

        let mut code = code.with_newline_whitespace(false);

        let mut stmts = vec![];
        loop {
            code.skip_whitespace_and_newlines();
            if code.take_char_if(|ch| ch == '}').is_some() {
                break Ok(Self {
                    stmts,
                    span: start.up_to(&code),
                });
            } else if code.peek().is_none() {
                return Err(Error::Expected(code.pos(), "`}`".into()));
            } else {
                stmts.push(code.parse()?);
            }
        }
    }
}
