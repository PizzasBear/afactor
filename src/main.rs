use std::{borrow::Cow, fs, path::PathBuf, str};

pub mod ast;
pub mod code;
pub mod encoder;
pub mod ir;
pub mod pad_adapter;

use code::Spanned;

#[derive(thiserror::Error, Debug)]
pub enum Error {
    #[error("Arrived at an unexpected end at {0:?}")]
    UnexpectedEnd(code::Pos),
    #[error("At {0:?}, {1}")]
    Lexical(code::Pos, lexical_core::Error),
    #[error("Expected {1} at {0:?}")]
    Expected(code::Pos, Cow<'static, str>),
    #[error("Expected {1} but found {2} at {0:?}")]
    ExpectedButFound(code::Span, Cow<'static, str>, Cow<'static, str>),
    #[error("Reserved identifier `{1}` at {0:?}")]
    ReservedIdent(code::Pos, &'static str),
    #[error("Float literal cannot parse the base {1} at {0:?}")]
    FloatRadix(code::Pos, u32),
    #[error("Name `{1:?}` redefined at {0:?}")]
    NameRedefined(code::Span, String),
    #[error("Use of undeclared {1}, `{2}`, at {0:?}")]
    UseOfUndeclared(code::Span, Cow<'static, str>, String),
    #[error("{1} must be sized at {0:?}")]
    MustBeSized(code::Span, Cow<'static, str>),
    #[error("Recursive struct `{1}` through field `{2}` without indirection at {0:?}")]
    RecursiveStruct(code::Span, String, String),
    #[error("Expected type `{1}` but recieved type `{2}` at {0:?}")]
    TypeMismatch(code::Span, String, String),
    #[error("Struct `{1}` has too many fields ({2}, more than 65535) at {0:?}")]
    TooManyFields(code::Span, String, usize),
    #[error("Type `{1}` doesn't have field `{2}` at {0:?}")]
    DoesNotHaveField(code::Span, String, String),
    #[error("Couldn't infer type at {0:?}")]
    CouldNotInferType(code::Span),
    #[error("Cannot assign to the expression at {0:?}")]
    CannotAssignExpr(code::Span),

    #[error("Not yet implemented at {0:?}")]
    Todo(code::Span),
}

impl Spanned for Error {
    fn span(&self) -> code::Span {
        match self {
            Self::UnexpectedEnd(pos) => pos.to_span(),
            Self::Lexical(pos, _) => pos.to_span(),
            Self::Expected(pos, _) => pos.to_span(),
            Self::ExpectedButFound(span, _, _) => *span,
            Self::ReservedIdent(pos, _) => pos.to_span(),
            Self::FloatRadix(pos, _) => pos.to_span(),
            Self::NameRedefined(span, _) => *span,
            Self::UseOfUndeclared(span, _, _) => *span,
            Self::MustBeSized(span, _) => *span,
            Self::RecursiveStruct(span, _, _) => *span,
            Self::TypeMismatch(span, _, _) => *span,
            Self::TooManyFields(span, _, _) => *span,
            Self::DoesNotHaveField(span, _, _) => *span,
            Self::CouldNotInferType(span) => *span,
            Self::CannotAssignExpr(span) => *span,

            Self::Todo(span) => *span,
        }
    }
}

pub type Result<T, E = Error> = std::result::Result<T, E>;

fn main() {
    println!("Hello, world!");
    let path = PathBuf::from("./tmp.afac");
    let source = code::Source {
        name: path.file_stem().unwrap().to_string_lossy().into_owned(),
        code: fs::read_to_string(&path).unwrap(),
        path,
    };
    let mut code = code::CodeIter::new(&source);
    let ast_module: ast::AstModule = match code.parse() {
        Ok(x) => x,
        Err(err) => {
            println!("ERROR: {err}");
            println!("{}", err.span().display(&source));
            return;
        }
    };
    println!("AST_MODULE:");
    println!("{ast_module}");
    println!("---");
    println!();

    let ir_module = match ir::proc_module(&ast_module) {
        Ok(x) => x,
        Err(err) => {
            println!("ERROR: {err}");
            println!("{}", err.span().display(&source));
            return;
        }
    };
    println!("IR_MODULE: {ir_module:#?}");

    // for def in &mut ir_module.type_defs {
    //     def.on_heap = match def.kind {
    //         ir::IrTypeDefKind::Alias(_) => false,
    //         _ => true,
    //     };
    // }

    let bytes = encoder::compile(&ir_module);
    fs::write("out.wasm", &bytes).unwrap();

    let color_writer = termcolor::StandardStream::stdout(termcolor::ColorChoice::Auto);
    wasmprinter::Config::new()
        .fold_instructions(true)
        .print(&bytes, &mut wasmprinter::PrintTermcolor(color_writer))
        .unwrap();
}
