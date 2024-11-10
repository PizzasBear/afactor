use std::fmt;

use crate::{
    code::{CodeIter, Span, Spanned},
    Error, Result,
};

use super::{
    is_ident_start, kw, parse_endline, parse_separated, peek_str, ty, AstBlock, AstName, AstParse,
    AstStr, AstType,
};

#[derive(Debug, Clone)]
pub struct AstStructFieldDef<'a> {
    pub name: AstName<'a>,
    pub ty: ty::AstType<'a>,
}

impl fmt::Display for AstStructFieldDef<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Display::fmt(&self.name, f)?;
        f.write_str(": ")?;
        fmt::Display::fmt(&self.ty, f)
    }
}

impl<'a> AstParse<'a> for AstStructFieldDef<'a> {
    fn parse(code: &mut CodeIter<'a>) -> Result<Self> {
        code.skip_whitespace_and_newlines();
        let name = AstName::parse(code)?;
        code.skip_whitespace();
        if code.take_char_if(|ch| ch == ':').is_none() {
            return Err(Error::Expected(code.pos(), "`:`".into()));
        }

        let ty = code.parse()?;
        Ok(Self { name, ty })
    }
}

#[derive(Debug, Clone)]
pub struct AstStructDef<'a> {
    pub struct_kw: kw![struct],
    pub name: AstName<'a>,
    pub fields: Vec<AstStructFieldDef<'a>>,
}

impl fmt::Display for AstStructDef<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        use fmt::Write;

        fmt::Display::fmt(&self.struct_kw, f)?;
        f.write_char(' ')?;
        fmt::Display::fmt(&self.name, f)?;
        f.write_str(" {")?;
        for field in &self.fields {
            f.write_str("\n    ")?;
            fmt::Display::fmt(field, f)?;
        }
        f.write_str("\n}\n")?;

        Ok(())
    }
}

impl<'a> AstParse<'a> for AstStructDef<'a> {
    fn parse(code: &mut CodeIter<'a>) -> Result<Self> {
        code.skip_whitespace_and_newlines();

        let code = &mut code.with_newline_whitespace(false);
        let struct_kw = code.parse()?;
        code.skip_whitespace();
        let name: AstName = code.parse()?;

        code.skip_whitespace();
        if code.take_char_if(|ch| ch == '{').is_none() {
            return Err(Error::Expected(code.pos(), "`{`".into()));
        }

        let mut fields = vec![];

        loop {
            code.skip_whitespace_and_newlines();
            if code.take_char_if(|ch| ch == '}').is_some() {
                break;
            } else if !code.peek().is_some_and(is_ident_start) {
                return Err(Error::Expected(
                    code.pos(),
                    "a field name or a closing brace `}`".into(),
                ));
            }

            fields.push(code.parse()?);
            code.skip_whitespace();
            if code.take_char_if(|ch| ch == '\n' || ch == ',').is_none()
                && code.peek().is_none_or(|ch| ch != '}')
            {
                return Err(Error::Expected(
                    code.pos(),
                    "a newline, a comma `,` or a closing brace `}`".into(),
                ));
            }
        }

        if (u16::MAX as usize) < fields.len() {
            return Err(Error::TooManyFields(
                name.span(),
                name.as_str().to_owned(),
                fields.len(),
            ));
        }

        Ok(Self {
            struct_kw,
            name,
            fields,
        })
    }
}

#[derive(Debug, Clone)]
pub struct AstParam<'a> {
    pub name: AstName<'a>,
    pub ty: ty::AstType<'a>,
}

impl fmt::Display for AstParam<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Display::fmt(&self.name, f)?;
        f.write_str(": ")?;
        fmt::Display::fmt(&self.ty, f)
    }
}

impl<'a> AstParse<'a> for AstParam<'a> {
    fn parse(code: &mut CodeIter<'a>) -> Result<Self> {
        let name = AstName::parse(code)?;
        code.skip_whitespace();
        if code.take_char_if(|ch| ch == ':').is_none() {
            return Err(Error::Expected(code.pos(), "`:`".into()));
        }

        let ty = code.parse()?;
        Ok(Self { name, ty })
    }
}

#[derive(Debug, Clone)]
pub struct AstFuncDecl<'a> {
    pub name: AstName<'a>,
    pub params: Vec<AstParam<'a>>,
    pub ret_ty: Option<AstType<'a>>,
}

impl fmt::Display for AstFuncDecl<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        use fmt::Write;

        fmt::Display::fmt(&self.name, f)?;
        f.write_char('(')?;
        if let Some((first, params)) = self.params.split_first() {
            fmt::Display::fmt(first, f)?;
            for param in params {
                f.write_str(", ")?;
                fmt::Display::fmt(param, f)?;
            }
        }
        f.write_char(')')?;

        if let Some(ty) = &self.ret_ty {
            f.write_char(' ')?;
            fmt::Display::fmt(ty, f)?;
        }

        Ok(())
    }
}

impl<'a> AstParse<'a> for AstFuncDecl<'a> {
    fn parse(code: &mut CodeIter<'a>) -> Result<Self> {
        code.skip_whitespace();
        let name = AstName::parse(code)?;

        let (_, params, _) = parse_separated(code, '(', ')', CodeIter::parse)?;

        code.skip_whitespace();
        Ok(Self {
            name,
            params,
            ret_ty: match code.peek() {
                Some('{' | ';' | '\n' | '+' | ']' | ')' | '}' | '>') => None,
                _ => Some(code.parse()?),
            },
        })
    }
}

#[derive(Debug, Clone)]
pub struct AstImportFunc<'a> {
    pub _span: Span,
    pub import_kw: kw![import],
    pub extern_kw: kw![extern],
    pub module: AstStr,
    pub field: Option<(AstStr, kw![as])>,
    pub decl: AstFuncDecl<'a>,
}

impl fmt::Display for AstImportFunc<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        use fmt::Write;

        fmt::Display::fmt(&self.import_kw, f)?;
        f.write_char(' ')?;
        fmt::Display::fmt(&self.extern_kw, f)?;
        f.write_char(' ')?;
        fmt::Display::fmt(&self.module, f)?;
        f.write_char('.')?;
        if let Some((field, kw)) = &self.field {
            fmt::Display::fmt(&field, f)?;
            f.write_char(' ')?;
            fmt::Display::fmt(&kw, f)?;
            f.write_char(' ')?;
        }
        fmt::Display::fmt(&self.decl, f)?;
        Ok(())
    }
}

#[derive(Debug, Clone)]
pub struct AstFunc<'a> {
    pub span: Span,
    pub export: Option<(kw![export], Option<AstStr>)>,
    pub fn_kw: kw![fn],
    pub decl: AstFuncDecl<'a>,
    pub block: AstBlock<'a>,
}

impl fmt::Display for AstFunc<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        use fmt::Write;

        if let Some((kw, name)) = &self.export {
            fmt::Display::fmt(kw, f)?;
            f.write_char(' ')?;
            if let Some(name) = name {
                fmt::Display::fmt(name, f)?;
                f.write_char(' ')?;
            }
        }
        fmt::Display::fmt(&self.fn_kw, f)?;
        f.write_char(' ')?;
        fmt::Display::fmt(&self.decl, f)?;
        f.write_char(' ')?;
        fmt::Display::fmt(&self.block, f)?;

        Ok(())
    }
}

#[derive(Debug, Clone)]
pub enum AstItemKind<'a> {
    StructDef(AstStructDef<'a>),
    Func(AstFunc<'a>),
    Import(AstImportFunc<'a>),
}

impl fmt::Display for AstItemKind<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::StructDef(struct_def) => fmt::Display::fmt(struct_def, f),
            Self::Func(func) => fmt::Display::fmt(func, f),
            Self::Import(import) => fmt::Display::fmt(import, f),
        }
    }
}

#[derive(Debug, Clone)]
pub struct AstItem<'a> {
    pub span: Span,
    pub kind: AstItemKind<'a>,
}

impl fmt::Display for AstItem<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Display::fmt(&self.kind, f)
    }
}

impl<'a> AstItem<'a> {
    pub fn new(span: Span, kind: AstItemKind<'a>) -> Self {
        Self { span, kind }
    }
}

impl<'a> AstParse<'a> for AstItem<'a> {
    fn parse(code: &mut CodeIter<'a>) -> Result<Self> {
        code.skip_whitespace();

        let code = &mut code.with_newline_whitespace(false);
        let start = code.pos();
        let export = match code.parse::<kw![export]>() {
            Err(_) => None,
            Ok(kw) => {
                code.skip_whitespace();
                Some((kw, peek_str(code).then(|| code.parse()).transpose()?))
            }
        };

        code.skip_whitespace();
        let item = if let Ok(fn_kw) = code.parse::<kw![fn]>() {
            code.skip_whitespace();

            let decl: AstFuncDecl = code.parse()?;

            code.skip_whitespace();

            let block = code.with_newline_whitespace_in(true, |code| code.parse())?;

            let func = AstFunc {
                span: decl.name.span(),
                export,
                fn_kw,
                decl,
                block,
            };

            AstItem::new(start.up_to(code), AstItemKind::Func(func))
        } else if let Ok(import_kw) = code.parse::<kw![import]>() {
            if export.is_some() {
                return Err(Error::Expected(code.pos(), "an exportable item".into()));
            }

            code.skip_whitespace();
            let extern_kw = code.parse()?;

            code.skip_whitespace();
            let module: AstStr = code.parse()?;

            code.skip_whitespace();
            code.take_char_if(|ch| ch == '.')
                .ok_or(Error::Expected(code.pos(), "`.`".into()))?;

            code.skip_whitespace();
            let field = match peek_str(code) {
                false => None,
                true => {
                    let field: AstStr = code.parse()?;
                    code.skip_whitespace();
                    Some((field, code.parse()?))
                }
            };

            let decl: AstFuncDecl = code.parse()?;

            AstItem::new(
                start.up_to(code),
                AstItemKind::Import(AstImportFunc {
                    _span: import_kw.span(),
                    import_kw,
                    extern_kw,
                    module: module.into(),
                    field,
                    decl,
                }),
            )
        } else if let Ok(_struct_kw) = code.clone().parse::<kw![struct]>() {
            let struct_def = code.parse()?;
            AstItem::new(start.up_to(code), AstItemKind::StructDef(struct_def))
        } else {
            return Err(Error::Todo(code.pos().to_span()));
        };

        parse_endline(code)?;

        Ok(item)
    }
}
