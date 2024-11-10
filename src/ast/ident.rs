use std::fmt;

use unicode_ident::*;

use crate::{
    code::{CodeIter, Span, Spanned},
    Error, Result,
};

use super::AstParse;

macro_rules! def_keywords {
    () => {};
    ($($name:ident($kw:tt)),+ $(,)?) => {
        const RESERVED_IDENTIFIERS: &[&str] = &[$(stringify!($kw)),+];

        pub mod keywords {
            use super::*;
            $(
                #[derive(Debug, Clone, Copy)]
                #[repr(transparent)]
                pub struct $name(pub Span);

                impl $name {
                    pub const IDENT: &str = stringify!($kw);
                    const EXPECTED: &str = concat!("the keyword `", stringify!($kw), "`");

                    pub const fn as_str(&self) -> &'static str {
                        Self::IDENT
                    }
                }

                impl Spanned for $name {
                    fn span(&self) -> Span {
                        self.0
                    }
                }

                impl AstParse<'_> for $name {
                    fn parse(code: &mut CodeIter) -> Result<Self> {
                        if code.as_str().starts_with(Self::IDENT)
                            && code.as_str()[Self::IDENT.len()..].starts_with(|ch| !is_xid_continue(ch))
                        {
                            let start = code.pos();
                            code.skipn_bytes(Self::IDENT.len());
                            Ok(Self(start.up_to(code)))
                        } else {
                            Err(Error::Expected(code.pos(), Self::EXPECTED.into()))
                        }
                    }
                }


                impl TryFrom<AstIdent<'_>> for $name {
                    type Error = Error;

                    fn try_from(AstIdent(span, ident): AstIdent<'_>) -> Result<Self> {
                        match ident {
                            Self::IDENT => Ok(Self(span)),
                            _ => Err(Error::Expected(span.start(), Self::EXPECTED.into())),
                        }
                    }
                }

                impl fmt::Display for $name {
                    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
                        f.write_str(self.as_str())
                    }
                }
            )+
        }

        #[macro_export]
        macro_rules! kw {
            $([$kw] => { $crate::ast::ident::keywords::$name };)+
        }
        pub use kw;

        #[derive(Debug, Clone)]
        pub enum AstKeyword {
            $($name(keywords::$name)),+
        }

        impl AstKeyword {
            pub fn as_str(&self) -> &'static str {
                match self {
                    $(Self::$name(kw) => kw.as_str(),)+
                }
            }
        }

        impl Spanned for AstKeyword {
            fn span(&self) -> Span {
                match self {
                    $(Self::$name(kw) => kw.span(),)+
                }
            }
        }

        impl TryFrom<AstIdent<'_>> for AstKeyword {
            type Error = Error;
            fn try_from(AstIdent(span, ident): AstIdent) -> Result<Self> {
                match ident {
                    $(stringify!($kw) => Ok(Self::$name(keywords::$name(span))),)+
                    _ => Err(Error::Expected(span.start(), "a keyword".into()))
                }
            }
        }

        impl fmt::Display for AstKeyword {
            fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
                f.write_str(self.as_str())
            }
        }
    };
}

impl AstParse<'_> for AstKeyword {
    fn parse(code: &mut CodeIter<'_>) -> Result<Self> {
        match AstIdent::parse(code) {
            Ok(ident) => ident.try_into(),
            Err(Error::Expected(pos, _)) => Err(Error::Expected(pos, "a keyword".into())),
            Err(err) => Err(err),
        }
    }
}

def_keywords!(
    Underscore(_), Let(let), Fn(fn), As(as), Mut(mut), Stack(stack), New(new),
    Shared(shared), Share(share), Import(import), Export(export), For(for),
    If(if), Else(else), Elif(elif), While(while), Loop(loop), Break(break),
    Continue(continue), Do(do), Impl(impl), Struct(struct), Trait(trait),
    Box(box), Unique(unique), Const(const), Pub(pub), Match(match),
    Switch(switch), Case(case), Use(use), Extern(extern), Return(return),
    True(true), False(false),
);

pub(super) fn is_ident_start(ch: char) -> bool {
    is_xid_start(ch) || ch == '_'
}

// pub fn next_ident<'a>(code: &mut CodeIter<'a>) -> &'a str {
//     let start = code.clone();
//     if code
//         .take_char_if(|ch| is_xid_start(ch) || ch == '_')
//         .is_some()
//     {
//         while code.take_char_if(is_xid_continue).is_some() {}
//     }
//     start.as_str_until(code.pos())
// }

#[derive(Debug, Clone)]
pub struct AstIdent<'a>(pub Span, pub &'a str);

impl<'a> AstIdent<'a> {
    pub fn as_str(&self) -> &'a str {
        self.1
    }
}

impl Spanned for AstIdent<'_> {
    fn span(&self) -> Span {
        self.0
    }
}

impl<'a> AstParse<'a> for AstIdent<'a> {
    fn parse(code: &mut CodeIter<'a>) -> Result<Self> {
        let start = code.clone();
        if code
            .take_char_if(|ch| is_xid_start(ch) || ch == '_')
            .is_none()
        {
            return Err(Error::Expected(start.pos(), "an identifier".into()));
        }
        while code.take_char_if(is_xid_continue).is_some() {}
        Ok(Self(
            start.pos().up_to(code),
            start.as_str_until(code.pos()),
        ))
    }
}

impl fmt::Display for AstIdent<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(self.as_str())
    }
}

#[derive(Debug, Clone)]
pub struct AstName<'a>(Span, &'a str);

impl<'a> AstName<'a> {
    pub fn as_str(&self) -> &'a str {
        self.1
    }
}

impl Spanned for AstName<'_> {
    fn span(&self) -> Span {
        self.0
    }
}

impl<'a> TryFrom<AstIdent<'a>> for AstName<'a> {
    type Error = Error;
    fn try_from(AstIdent(span, ident): AstIdent<'a>) -> Result<Self> {
        match RESERVED_IDENTIFIERS.iter().copied().find(|&s| s == ident) {
            Some(ident) => Err(Error::ReservedIdent(span.start(), ident)),
            None => Ok(Self(span, ident)),
        }
    }
}

impl<'a> AstParse<'a> for AstName<'a> {
    fn parse(code: &mut CodeIter<'a>) -> Result<Self> {
        AstIdent::parse(code)?.try_into()
    }
}

impl fmt::Display for AstName<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(self.as_str())
    }
}
