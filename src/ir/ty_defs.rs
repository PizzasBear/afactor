use std::{fmt, mem, num::NonZero};

use ahash::HashMap;

use crate::{
    ast::{AstStructDef, AstStructFieldDef, AstType},
    code::Spanned,
};

#[derive(Debug, Clone, Copy)]
pub enum IrPrimitive {
    None,
    Bool,
    U8,
    U16,
    U32,
    U64,
    I8,
    I16,
    I32,
    I64,
    F32,
    F64,
}

impl IrPrimitive {
    pub const fn byte_size(self) -> u32 {
        match self {
            IrPrimitive::None => 0,
            IrPrimitive::Bool | IrPrimitive::U8 | IrPrimitive::I8 => 1,
            IrPrimitive::U16 | IrPrimitive::I16 => 2,
            IrPrimitive::U32 | IrPrimitive::I32 | IrPrimitive::F32 => 4,
            IrPrimitive::U64 | IrPrimitive::I64 | IrPrimitive::F64 => 8,
        }
    }
    pub fn is_integer(self) -> bool {
        use IrPrimitive::*;
        matches!(self, U8 | U16 | U32 | U64 | I8 | I16 | I32 | I64)
    }
    pub const fn is_float(self) -> bool {
        use IrPrimitive::*;
        matches!(self, F32 | F64)
    }
    pub fn is_number(self) -> bool {
        self.is_integer() || self.is_float()
    }
}

impl fmt::Display for IrPrimitive {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(match self {
            Self::None => "none",
            Self::Bool => "bool",
            Self::U8 => "u8",
            Self::U16 => "u16",
            Self::U32 => "u32",
            Self::U64 => "u64",
            Self::I8 => "i8",
            Self::I16 => "i16",
            Self::I32 => "i32",
            Self::I64 => "i64",
            Self::F32 => "f32",
            Self::F64 => "f64",
        })
    }
}

#[derive(Clone)]
pub struct IrStructDefField<'a> {
    pub ast: &'a AstStructFieldDef<'a>,
    pub ty: IrType,
}

impl fmt::Debug for IrStructDefField<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("IrStructDefField")
            .field("ast.name", &self.ast.name)
            .field("ty", &self.ty)
            .finish()
    }
}

#[derive(Clone)]
pub struct IrStructDef<'a> {
    pub ast: &'a AstStructDef<'a>,
    pub fields: Vec<IrStructDefField<'a>>,
    pub field_name_map: HashMap<&'a str, u32>,
}

impl fmt::Debug for IrStructDef<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("IrStructDef")
            .field("ast.name", &self.ast.name)
            .field("fields", &self.fields)
            .field("field_name_map", &self.field_name_map)
            .finish()
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum TypeBound {
    Any,
    // Unsized bounds:
    Array,
    // Sized bounds:
    Sized,
    Ptr,
    StackPtr,
    GcPtr,
    Number,
    Integer,
    Float,
}

impl TypeBound {
    pub fn take(&mut self) -> Self {
        mem::replace(self, Self::Any)
    }

    pub fn intersection(mut self, mut other: Self) -> Option<Self> {
        use TypeBound::*;

        if self == other {
            return Some(self);
        } else if (other as u32) < self as u32 {
            (self, other) = (other, self);
        }
        let all = [
            Any, Array, Sized, Ptr, StackPtr, GcPtr, Number, Integer, Float,
        ];
        debug_assert!(all.is_sorted_by_key(|&b| b as u32));
        match (self, other) {
            (Any, _) => Some(other),
            // Array
            (Sized, _) => Some(other),
            (Ptr, StackPtr | GcPtr) => Some(other),
            // StackPtr, GcPtr
            (Number, Integer | Float) => Some(other),
            // Integer, Float
            (Array | Ptr | StackPtr | GcPtr | Number | Integer | Float, _) => None,
        }
    }

    pub fn type_repr(self) -> &'static str {
        match self {
            TypeBound::Any => "<any_type>",
            TypeBound::Array => "[]<any_type>",
            TypeBound::Sized => "<sized_type>",
            TypeBound::Ptr => "<any_ptr_type>",
            TypeBound::StackPtr => "&<any_type>",
            TypeBound::GcPtr => "*<any_type>",
            TypeBound::Number => "<number_type>",
            TypeBound::Integer => "<interger_type>",
            TypeBound::Float => "<float_type>",
        }
    }
}

#[derive(Clone)]
pub enum IrTypeDefKind<'a> {
    Primitive(IrPrimitive),
    Struct(IrStructDef<'a>),
    Array(Option<&'a AstType<'a>>, IrType),
    GcPtr(IrType),
    StackPtr(IrType),
    Alias(IrType),
    Undetermined(TypeBound),
}

impl fmt::Debug for IrTypeDefKind<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            IrTypeDefKind::Primitive(prim) => fmt::Debug::fmt(prim, f),
            IrTypeDefKind::Struct(def) => fmt::Debug::fmt(def, f),
            IrTypeDefKind::Array(ast, ty) => f
                .debug_struct("Array")
                .field("ast.span", &ast.map(|ast| ast.span()))
                .field("el_ty", ty)
                .finish(),
            IrTypeDefKind::GcPtr(ty) => write!(f, "GcPtr({ty:?})"),
            IrTypeDefKind::StackPtr(ty) => write!(f, "StackPtr({ty:?})"),
            IrTypeDefKind::Alias(ty) => write!(f, "Alias({ty:?})"),
            IrTypeDefKind::Undetermined(bound) => write!(f, "Undetermined({bound:?})"),
        }
    }
}

#[derive(Debug, Clone)]
pub struct IrTypeDef<'a> {
    // pub on_heap: bool,
    pub sized: bool,
    // pub zst: bool,
    pub kind: IrTypeDefKind<'a>,
}

impl<'a> IrTypeDef<'a> {
    pub fn new(kind: IrTypeDefKind<'a>) -> Self {
        Self {
            // on_heap: false,
            // zst: matches!(kind, IrTypeDefKind::Primitive(IrPrimitive::None)),
            sized: !matches!(kind, IrTypeDefKind::Array(..)),
            kind,
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub struct IrLifetime(pub u32);

impl IrLifetime {
    pub const STATIC: Self = Self(0);
}

#[derive(Clone, Copy, PartialEq, Eq, Hash)]
pub struct IrType(NonZero<u32>);

impl IrType {
    pub const fn from_idx(idx: usize) -> Self {
        Self(match NonZero::new(idx as u32 + 1) {
            Some(idx) => idx,
            None => panic!(),
        })
    }
    pub const fn idx(self) -> usize {
        self.0.get() as usize - 1
    }

    pub const fn from_primitive(prim: IrPrimitive) -> Self {
        Self::from_idx(prim as _)
    }

    pub const fn into_primitive(self) -> Option<IrPrimitive> {
        match self.0.get() {
            0 => Some(IrPrimitive::None),
            1 => Some(IrPrimitive::U8),
            2 => Some(IrPrimitive::U16),
            3 => Some(IrPrimitive::U32),
            4 => Some(IrPrimitive::U64),
            5 => Some(IrPrimitive::I8),
            6 => Some(IrPrimitive::I16),
            7 => Some(IrPrimitive::I32),
            8 => Some(IrPrimitive::I64),
            9 => Some(IrPrimitive::F32),
            10 => Some(IrPrimitive::F64),
            _ => None,
        }
    }

    pub fn repr_into(self, defs: &[IrTypeDef], out: &mut String) {
        use fmt::Write;

        let def = &defs[self.idx()];
        match &def.kind {
            IrTypeDefKind::Primitive(prim) => write!(out, "{prim}").unwrap(),
            IrTypeDefKind::Struct(def) => write!(out, "{}", def.ast.name).unwrap(),
            IrTypeDefKind::Array(Some(ast), _) => write!(out, "{ast}").unwrap(),
            IrTypeDefKind::Array(_, ty) => {
                out.push_str("[]");
                ty.repr_into(defs, out);
            }
            IrTypeDefKind::GcPtr(ty) => {
                out.push('*');
                ty.repr_into(defs, out);
            }
            IrTypeDefKind::StackPtr(ty) => {
                out.push('&');
                ty.repr_into(defs, out);
            }
            IrTypeDefKind::Alias(ty) => ty.repr_into(defs, out),
            IrTypeDefKind::Undetermined(bound) => out.push_str(bound.type_repr()),
        }
    }

    pub fn repr(self, defs: &[IrTypeDef]) -> String {
        let mut out = String::new();
        self.repr_into(defs, &mut out);
        out
    }
}

impl From<IrPrimitive> for IrType {
    fn from(prim: IrPrimitive) -> Self {
        Self::from_primitive(prim)
    }
}

impl fmt::Debug for IrType {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "IrType({})", self.idx())
    }
}
