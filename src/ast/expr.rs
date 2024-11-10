use std::fmt;

use either::*;

use crate::{
    code::{CodeIter, Span, Spanned},
    Error, Result,
};

use super::{
    is_ident_start, kw, parse_separated, str::AstStr, AstBlock, AstFloat, AstName, AstNum,
    AstParse, AstUint,
};

#[derive(Debug, Clone, Copy)]
pub enum AstInfixOp {
    Add,
    Sub,
    Mul,
    Div,
    Mod,
    Assign,
}

impl AstInfixOp {
    fn precedence_level(&self) -> u8 {
        match self {
            AstInfixOp::Assign => 1,
            AstInfixOp::Add => 2,
            AstInfixOp::Sub => 2,
            AstInfixOp::Mul => 3,
            AstInfixOp::Div => 3,
            AstInfixOp::Mod => 3,
        }
    }
    fn from_char(ch: char) -> Option<Self> {
        match ch {
            '=' => Some(Self::Assign),
            '+' => Some(Self::Add),
            '-' => Some(Self::Sub),
            '*' => Some(Self::Mul),
            '/' => Some(Self::Div),
            '%' => Some(Self::Mod),
            _ => None,
        }
    }
}

impl fmt::Display for AstInfixOp {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        use fmt::Write;
        match self {
            AstInfixOp::Assign => f.write_char('='),
            AstInfixOp::Add => f.write_char('+'),
            AstInfixOp::Sub => f.write_char('-'),
            AstInfixOp::Mul => f.write_char('*'),
            AstInfixOp::Div => f.write_char('/'),
            AstInfixOp::Mod => f.write_char('%'),
        }
    }
}

#[derive(Debug, Clone, Copy)]
pub enum AstPrefixOp {
    Neg,
    Not,
    Deref,
    Ref,
}

impl AstPrefixOp {
    fn from_char(ch: char) -> Option<Self> {
        match ch {
            '-' => Some(Self::Neg),
            '!' => Some(Self::Not),
            '*' => Some(Self::Deref),
            '&' => Some(Self::Ref),
            _ => None,
        }
    }
    fn precedence_level(&self) -> u8 {
        match self {
            Self::Neg => 5,
            Self::Not => 5,
            Self::Deref => 5,
            Self::Ref => 5,
        }
    }
}

impl fmt::Display for AstPrefixOp {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Neg => write!(f, "-"),
            Self::Not => write!(f, "!"),
            Self::Ref => write!(f, "&"),
            Self::Deref => write!(f, "*"),
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum AstIntSuffix {
    Auto,
    U8,
    U16,
    U32,
    U64,
    I8,
    I16,
    I32,
    I64,
}

impl fmt::Display for AstIntSuffix {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(match self {
            Self::Auto => "",
            Self::U8 => "u8",
            Self::U16 => "u16",
            Self::U32 => "u32",
            Self::U64 => "u64",
            Self::I8 => "i8",
            Self::I16 => "i16",
            Self::I32 => "i32",
            Self::I64 => "i64",
        })
    }
}

impl AstParse<'_> for AstIntSuffix {
    fn parse(code: &mut CodeIter<'_>) -> Result<Self> {
        if code.as_str().starts_with("u8") {
            code.skipn_bytes(2);
            Ok(Self::U8)
        } else if code.as_str().starts_with("u16") {
            code.skipn_bytes(3);
            Ok(Self::U16)
        } else if code.as_str().starts_with("u32") {
            code.skipn_bytes(3);
            Ok(Self::U32)
        } else if code.as_str().starts_with("u64") {
            code.skipn_bytes(3);
            Ok(Self::U64)
        } else if code.as_str().starts_with("i8") {
            code.skipn_bytes(2);
            Ok(Self::I8)
        } else if code.as_str().starts_with("i16") {
            code.skipn_bytes(3);
            Ok(Self::I16)
        } else if code.as_str().starts_with("i32") {
            code.skipn_bytes(3);
            Ok(Self::I32)
        } else if code.as_str().starts_with("i64") {
            code.skipn_bytes(3);
            Ok(Self::I64)
        } else {
            Ok(Self::Auto)
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum AstFloatSuffix {
    Auto,
    F32,
    F64,
}

impl fmt::Display for AstFloatSuffix {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(match self {
            Self::Auto => "",
            Self::F32 => "f32",
            Self::F64 => "f64",
        })
    }
}

impl AstParse<'_> for AstFloatSuffix {
    fn parse(code: &mut CodeIter<'_>) -> Result<Self> {
        if code.as_str().starts_with("f32") {
            code.skipn_bytes(3);
            Ok(Self::F32)
        } else if code.as_str().starts_with("f64") {
            code.skipn_bytes(3);
            Ok(Self::F64)
        } else {
            Ok(Self::Auto)
        }
    }
}

#[derive(Debug, Clone)]
pub struct AstLabel<'a> {
    pub span: Span,
    pub name: AstName<'a>,
}

fn peek_label(code: &CodeIter) -> bool {
    code.peek().is_some_and(|ch| ch == '\'')
        && code.peek1().is_some_and(is_ident_start)
        && code.peek2().is_none_or(|ch| ch != '\'')
}

impl fmt::Display for AstLabel<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        use fmt::Write;

        f.write_char('\'')?;
        f.write_str(self.name.as_str())?;

        Ok(())
    }
}

impl<'a> AstParse<'a> for AstLabel<'a> {
    fn parse(code: &mut CodeIter<'a>) -> Result<Self> {
        let expected_pos = code.pos();
        code.skip_whitespace();
        let start = code.pos();
        code.take_char_if(|ch| ch == '\'').ok_or(Error::Expected(
            expected_pos,
            "a label (e.g. `'label`)".into(),
        ))?;

        Ok(Self {
            name: code.parse()?,
            span: start.up_to(code),
        })
    }
}

#[derive(Debug, Clone)]
pub struct AstIfExpr<'a> {
    pub if_kw: kw![if],
    pub cond: Box<AstExpr<'a>>,
    pub then_branch: Box<AstExpr<'a>>,
    pub else_branch: Option<(kw![else], Box<AstExpr<'a>>)>,
}

impl fmt::Display for AstIfExpr<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        use fmt::Write;
        use AstExprKind as K;

        f.write_str(self.if_kw.as_str())?;
        f.write_char(' ')?;
        fmt::Display::fmt(&self.cond, f)?;
        let colon = !matches!(self.then_branch.kind, K::Block(None, _));
        match colon {
            true => f.write_str(": ")?,
            false => f.write_char(' ')?,
        }
        fmt::Display::fmt(&self.then_branch, f)?;

        if let Some((else_kw, else_expr)) = &self.else_branch {
            match colon {
                true => f.write_char('\n')?,
                false => f.write_char(' ')?,
            }
            f.write_str(else_kw.as_str())?;
            match else_expr.kind {
                K::Block(None, _) | K::If(_) => f.write_char(' ')?,
                _ => f.write_str(": ")?,
            }
            fmt::Display::fmt(&else_expr, f)?;
        }

        Ok(())
    }
}

impl<'a> AstParse<'a> for AstIfExpr<'a> {
    fn parse(code: &mut CodeIter<'a>) -> Result<Self> {
        code.skip_whitespace();
        let if_kw = code.parse()?;
        let cond = Box::new(code.with_newline_whitespace_in(true, |code| code.parse())?);
        let expected_pos = code.pos();
        code.skip_whitespace();
        let colon = code.take_char_if(|ch| ch == ':').is_some();
        if !colon || code.peek().is_none_or(|ch| ch != '{') {
            return Err(Error::Expected(
                expected_pos,
                "a then branch - a colon and an expression or a block".into(),
            ));
        }
        let then_branch = Box::new(code.parse()?);
        let mut lookahead = code.clone();
        lookahead.skip_whitespace_and_newlines();
        let else_branch = match lookahead.parse::<kw![else]>() {
            Ok(_) => {
                code.skip_whitespace_and_newlines();
                let else_kw = lookahead.parse()?;
                code.skip_whitespace();
                let colon = code.take_char_if(|ch| ch == ':').is_some();
                if !colon || code.as_str().starts_with('{') || code.as_str().starts_with("if") {
                    return Err(Error::Expected(
                        expected_pos,
                        "an else branch - a colon and an expression, a block, or another if".into(),
                    ));
                }
                Some((else_kw, Box::new(code.parse()?)))
            }
            Err(_) => None,
        };

        Ok(Self {
            if_kw,
            cond,
            then_branch,
            else_branch,
        })
    }
}

#[derive(Debug, Clone)]
pub enum AstExprKind<'a> {
    Bool(Either<kw![true], kw![false]>),
    Var(AstName<'a>),
    Int(AstUint, AstIntSuffix),
    Float(AstFloat, AstFloatSuffix),
    Str(AstStr),
    Return(kw![return], Option<Box<AstExpr<'a>>>),
    Break(kw![break], Option<AstLabel<'a>>, Option<Box<AstExpr<'a>>>),
    Continue(kw![continue], Option<AstLabel<'a>>),
    Loop(kw![loop], Option<AstLabel<'a>>, AstBlock<'a>),
    Block(Option<AstLabel<'a>>, AstBlock<'a>),
    If(AstIfExpr<'a>),
    InfixOp(AstInfixOp, Box<AstExpr<'a>>, Box<AstExpr<'a>>),
    PrefixOp(AstPrefixOp, Box<AstExpr<'a>>),
    FieldAccess(Box<AstExpr<'a>>, AstName<'a>),
    FunctionCall(Box<AstExpr<'a>>, Vec<AstExpr<'a>>),
    MethodCall(Box<AstExpr<'a>>, AstName<'a>, Vec<AstExpr<'a>>),
}

#[derive(Clone)]
pub struct AstExpr<'a> {
    span: Span,
    pub kind: AstExprKind<'a>,
}

impl<'a> AstExpr<'a> {
    pub const fn new(span: Span, kind: AstExprKind<'a>) -> Self {
        Self { span, kind }
    }
}

impl Spanned for AstExpr<'_> {
    fn span(&self) -> Span {
        self.span
    }
}

impl fmt::Display for AstExpr<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Display::fmt(&self.kind, f)
    }
}

impl fmt::Debug for AstExpr<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{:?} @ ", self.span)?;
        fmt::Debug::fmt(&self.kind, f)?;
        Ok(())
    }
}

impl fmt::Display for AstExprKind<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        use fmt::Write;

        match self {
            Self::Bool(kw) => f.write_str(kw.either(|kw| kw.as_str(), |kw| kw.as_str())),
            Self::Int(n, suf) => {
                fmt::Display::fmt(n, f)?;
                fmt::Display::fmt(suf, f)?;
                Ok(())
            }
            Self::Float(n, suf) => {
                fmt::Display::fmt(n, f)?;
                fmt::Display::fmt(suf, f)?;
                Ok(())
            }
            Self::Str(s) => fmt::Display::fmt(s, f),
            Self::InfixOp(op, left, right) => {
                f.write_char('(')?;
                fmt::Display::fmt(left, f)?;
                f.write_char(' ')?;
                fmt::Display::fmt(op, f)?;
                f.write_char(' ')?;
                fmt::Display::fmt(right, f)?;
                f.write_char(')')?;
                Ok(())
            }
            Self::PrefixOp(op, value) => {
                f.write_char('(')?;
                fmt::Display::fmt(op, f)?;
                fmt::Display::fmt(value, f)?;
                f.write_char(')')?;
                Ok(())
            }
            Self::Return(ret, val) => {
                f.write_char('(')?;
                f.write_str(ret.as_str())?;
                if let Some(val) = val {
                    f.write_char(' ')?;
                    fmt::Display::fmt(val, f)?;
                }
                f.write_char(')')?;
                Ok(())
            }
            Self::Break(br, lbl, val) => {
                f.write_char('(')?;
                f.write_str(br.as_str())?;
                if let Some(lbl) = lbl {
                    f.write_char(' ')?;
                    fmt::Display::fmt(lbl, f)?;
                }
                if let Some(val) = val {
                    f.write_char(' ')?;
                    fmt::Display::fmt(val, f)?;
                }
                f.write_char(')')?;
                Ok(())
            }
            Self::Continue(cont, lbl) => {
                f.write_str(cont.as_str())?;
                if let Some(lbl) = lbl {
                    f.write_char(' ')?;
                    fmt::Display::fmt(lbl, f)?;
                }
                Ok(())
            }
            Self::Loop(lp, lbl, block) => {
                if let Some(lbl) = lbl {
                    fmt::Display::fmt(lbl, f)?;
                    f.write_str(": ")?;
                }
                f.write_str(lp.as_str())?;
                f.write_char(' ')?;
                fmt::Display::fmt(block, f)
            }
            Self::Block(lbl, block) => {
                if let Some(lbl) = lbl {
                    fmt::Display::fmt(lbl, f)?;
                    f.write_str(": ")?;
                }
                fmt::Display::fmt(block, f)
            }
            Self::If(if_expr) => fmt::Display::fmt(if_expr, f),
            Self::FieldAccess(expr, field) => {
                fmt::Display::fmt(expr, f)?;
                f.write_char('.')?;
                fmt::Display::fmt(field, f)?;
                Ok(())
            }
            Self::FunctionCall(expr, args) => {
                fmt::Display::fmt(expr, f)?;
                f.write_char('(')?;
                if let Some((first, rest)) = args.split_first() {
                    fmt::Display::fmt(first, f)?;
                    for arg in rest {
                        f.write_str(", ")?;
                        fmt::Display::fmt(arg, f)?;
                    }
                }
                f.write_char(')')?;
                Ok(())
            }
            Self::MethodCall(expr, method, args) => {
                fmt::Display::fmt(expr, f)?;
                f.write_char('.')?;
                fmt::Display::fmt(method, f)?;
                f.write_char('(')?;
                if let Some((first, rest)) = args.split_first() {
                    fmt::Display::fmt(first, f)?;
                    for arg in rest {
                        f.write_str(", ")?;
                        fmt::Display::fmt(arg, f)?;
                    }
                }
                f.write_char(')')?;
                Ok(())
            }
            Self::Var(name) => fmt::Display::fmt(name, f),
        }
    }
}

fn parse_expr_precedented<'a>(
    code: &mut CodeIter<'a>,
    precedence_level: u8,
) -> Result<AstExpr<'a>> {
    code.skip_whitespace();
    let start_pos = code.pos();
    let ch = code.peek().ok_or(Error::UnexpectedEnd(code.pos()))?;

    let mut expr;
    if ch.is_ascii_digit() || ch == '.' {
        let mut start = code.clone();
        let num = code.parse()?;
        let end_pos = code.pos();

        expr = match num {
            AstNum::Uint(num) => match AstFloatSuffix::parse(code) {
                Err(_) | Ok(AstFloatSuffix::Auto) => AstExpr::new(
                    start.pos().up_to(code),
                    AstExprKind::Int(num, code.parse()?),
                ),
                Ok(suf) => {
                    let num: AstFloat = start.parse()?;
                    assert_eq!(start.pos(), end_pos);
                    AstExpr::new(num.span().start().up_to(code), AstExprKind::Float(num, suf))
                }
            },
            AstNum::Float(num) => AstExpr::new(
                start.pos().up_to(code),
                AstExprKind::Float(num, code.parse()?),
            ),
        };
    } else if let Ok(ret_kw) = <kw![return]>::parse(code) {
        code.skip_whitespace();
        if matches!(code.peek(), None | Some('}' | ']' | ')' | ';' | '\n' | ',')) {
            return Ok(AstExpr::new(
                ret_kw.span(),
                AstExprKind::Return(ret_kw, None),
            ));
        }
        expr = parse_expr_precedented(code, 0)?;
        expr = AstExpr::new(
            start_pos.up_to(code),
            AstExprKind::Return(ret_kw, Some(Box::new(expr))),
        );
    } else if let Ok(br_kw) = <kw![break]>::parse(code) {
        code.skip_whitespace();
        let label = peek_label(code).then(|| code.parse()).transpose()?;
        code.skip_whitespace();
        if matches!(code.peek(), None | Some('}' | ']' | ')' | ';' | '\n' | ',')) {
            return Ok(AstExpr::new(
                br_kw.span(),
                AstExprKind::Break(br_kw, label, None),
            ));
        }
        expr = parse_expr_precedented(code, 0)?;
        expr = AstExpr::new(
            start_pos.up_to(code),
            AstExprKind::Break(br_kw, label, Some(Box::new(expr))),
        );
    } else if let Ok(cont_kw) = <kw![continue]>::parse(code) {
        code.skip_whitespace();
        let label = peek_label(code).then(|| code.parse()).transpose()?;
        expr = AstExpr::new(cont_kw.span(), AstExprKind::Continue(cont_kw, label));
    } else if peek_label(code) {
        let label = code.parse()?;
        let expected_pos = code.pos();
        code.skip_whitespace();
        code.take_char_if(|ch| ch == ':')
            .ok_or(Error::Expected(expected_pos, "a colon".into()))?;
        let expected_pos = code.pos();
        code.skip_whitespace();
        if let Ok(loop_kw) = <kw![loop]>::parse(code) {
            let block = code.parse()?;
            expr = AstExpr::new(
                start_pos.up_to(code),
                AstExprKind::Loop(loop_kw, Some(label), block),
            );
        } else {
            return Err(Error::Expected(
                expected_pos,
                "a labelable expression".into(),
            ));
        }
    } else if let Ok(loop_kw) = <kw![loop]>::parse(code) {
        let block = code.parse()?;
        expr = AstExpr::new(
            start_pos.up_to(code),
            AstExprKind::Loop(loop_kw, None, block),
        );
    } else if let Some(op) = AstPrefixOp::from_char(ch) {
        code.next_char();
        expr = parse_expr_precedented(code, op.precedence_level())?;
        expr = AstExpr::new(
            start_pos.up_to(code),
            AstExprKind::PrefixOp(op, Box::new(expr)),
        );
    } else if ch == '(' {
        code.next_char();
        expr = code.with_newline_whitespace_in(true, |code| {
            let expr = AstExpr::parse(code)?;
            code.skip_whitespace();
            let pos = code.pos();
            if code.next_char() != Some(')') {
                return Err(Error::Expected(pos, "')'".into()));
            }
            Ok(expr)
        })?;
    } else if ch == '"' {
        let s: AstStr = code.parse()?;
        expr = AstExpr::new(s.span(), AstExprKind::Str(s));
    } else if code.peek().is_some_and(is_ident_start) {
        let name = AstName::parse(code)?;
        expr = AstExpr::new(name.span(), AstExprKind::Var(name));
    } else {
        return Err(Error::Todo(code.pos().to_span()));
    };

    loop {
        code.skip_whitespace();

        let pos = code.pos();
        let Some(ch) = code.peek() else {
            break;
        };
        if let Some(op) = AstInfixOp::from_char(ch) {
            if op.precedence_level() < precedence_level {
                break;
            }
            code.next_char();
            expr = AstExpr::new(
                pos.up_to(code),
                AstExprKind::InfixOp(
                    op,
                    Box::new(expr),
                    Box::new(parse_expr_precedented(code, op.precedence_level() + 1)?),
                ),
            );
        } else if ch == '.' {
            code.next_char();
            code.skip_whitespace();
            let name = AstName::parse(code)?;
            code.skip_whitespace();
            if !code.peek().is_some_and(|ch| ch == '(') {
                expr = AstExpr::new(name.span(), AstExprKind::FieldAccess(Box::new(expr), name));
                continue;
            }
            let (_, args, _) = parse_separated(code, '(', ')', CodeIter::parse)?;
            expr = AstExpr::new(
                name.span(),
                AstExprKind::MethodCall(Box::new(expr), name, args),
            )
        } else if ch == '(' {
            let (span, args, _) = parse_separated(code, '(', ')', CodeIter::parse)?;
            expr = AstExpr::new(span, AstExprKind::FunctionCall(Box::new(expr), args))
        } else {
            break;
        }
    }

    Ok(expr)
}

impl<'a> AstParse<'a> for AstExpr<'a> {
    fn parse(code: &mut CodeIter<'a>) -> Result<Self> {
        parse_expr_precedented(code, 0)
    }
}
