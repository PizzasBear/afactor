use std::{fmt, mem, num::NonZero, ops};

use ahash::{HashMap, HashMapExt};
use either::*;

use crate::{
    ast::*,
    code::{Span, Spanned},
    Error, Result,
};

mod ty_defs;

pub use ty_defs::*;

#[derive(Debug, Clone, Copy)]
pub enum IrNumBinOp {
    Add,
    Sub,
    Mul,
    Div,
    Mod,
}

#[derive(Debug, Clone, Copy)]
pub enum IrNumUnOp {
    Neg,
    Not,
}

#[derive(Debug, Clone)]
pub enum IrPlaceExpr {
    Local(IrLocal, IrType),
    Deref(Box<IrValueExpr>, IrType),
    FieldAccess(Box<IrPlaceExpr>, u32, IrType),
    Index(Box<IrPlaceExpr>, Box<IrValueExpr>, IrType),
}

impl IrPlaceExpr {
    pub fn ty(&self) -> IrType {
        match *self {
            Self::Local(_, ty) => ty,
            Self::Deref(_, ty) => ty,
            Self::FieldAccess(_, _, ty) => ty,
            Self::Index(_, _, ty) => ty,
        }
    }

    fn applied_on(&self, func: &mut IrFuncDef) {
        let use_n = func.stmts.len() as _;
        match self {
            &Self::Local(l, _) => func.local_mut(l).last_use = use_n,
            Self::Deref(e, _) => e.applied_on(func),
            Self::FieldAccess(e, _, _) => e.applied_on(func),
            Self::Index(a, i, _) => {
                i.applied_on(func);
                a.applied_on(func);
            }
        }
    }
}

#[derive(Debug, Clone)]
pub enum IrValueExpr {
    None,
    IConst(IrType, u64),
    FConst(IrType, f64),
    NumBinOp(IrType, IrNumBinOp, Box<IrValueExpr>, Box<IrValueExpr>),
    NumUnOp(IrType, IrNumUnOp, Box<IrValueExpr>),
    ArrayLen(Box<IrValueExpr>),
    TakeStackRef(Box<IrPlaceExpr>, IrType),
    Copy(Box<IrPlaceExpr>, IrType),
}

impl IrValueExpr {
    pub fn ty(&self) -> IrType {
        match *self {
            Self::None => IrPrimitive::None.into(),
            Self::IConst(ty, _) => ty,
            Self::FConst(ty, _) => ty,
            Self::NumBinOp(ty, ..) => ty,
            Self::NumUnOp(ty, ..) => ty,
            Self::ArrayLen(_) => IrPrimitive::U32.into(),
            Self::TakeStackRef(_, ty) => ty,
            Self::Copy(_, ty) => ty,
        }
    }

    fn applied_on(&self, func: &mut IrFuncDef) {
        match self {
            Self::None => {}
            Self::IConst(_, _) => {}
            Self::FConst(_, _) => {}
            Self::NumBinOp(_, _, l, r) => {
                l.applied_on(func);
                r.applied_on(func);
            }
            Self::NumUnOp(_, _, e) => e.applied_on(func),
            Self::ArrayLen(e) => e.applied_on(func),
            Self::TakeStackRef(e, _) => e.applied_on(func),
            Self::Copy(e, _) => e.applied_on(func),
        }
    }
}

#[derive(Debug, Clone)]
pub enum IrStmt {
    Assign(Box<IrPlaceExpr>, Box<IrValueExpr>),
    FuncCall(IrLocal, IrFunc, Box<[IrValueExpr]>),
    Loop(Option<IrLocal>, u32),
    Block(Option<IrLocal>, u32),
    If(Option<IrLocal>, Box<IrValueExpr>, u32),
    Else(Option<IrLocal>, u32),
    End(u32),
    Return(Box<IrValueExpr>),
    Break(u32, Option<Box<IrValueExpr>>),
    Continue(u32),
}

#[derive(Debug, Clone)]
pub struct IrLocalDef<'a> {
    pub name: Option<&'a AstName<'a>>,
    pub ty: IrType,

    pub is_param: bool,
    pub stack_refd: bool,

    pub def_stmt: u32,
    pub last_use: u32,
}

#[derive(Clone, Copy, PartialEq, Eq, Hash)]
pub struct IrLocal(NonZero<u32>);

impl IrLocal {
    pub const fn from_idx(idx: usize) -> Self {
        debug_assert!(idx < u32::MAX as usize);
        match NonZero::new(idx as u32 + 1) {
            Some(inner) => Self(inner),
            None => panic!(),
        }
    }
    pub const fn idx(self) -> usize {
        (self.0.get() - 1) as _
    }
}

impl fmt::Debug for IrLocal {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "IrLocal({})", self.idx())
    }
}

#[derive(Clone, Copy, PartialEq, Eq, Hash)]
pub struct IrFunc(u32);

impl IrFunc {
    pub fn from_idx(idx: usize) -> Self {
        debug_assert!(idx <= u32::MAX as usize);
        Self(idx as _)
    }
    pub fn idx(self) -> usize {
        self.0 as _
    }
}

impl fmt::Debug for IrFunc {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "IrFunc({})", self.idx())
    }
}

#[derive(Clone)]
pub struct IrParam<'a> {
    pub ast: &'a AstParam<'a>,
    pub local: IrLocalDef<'a>,
}

impl fmt::Debug for IrParam<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        use fmt::Write;

        f.write_str("IrParam(")?;
        fmt::Debug::fmt(&self.local, f)?;
        f.write_char(')')?;

        Ok(())
    }
}

#[derive(Debug, Clone)]
pub struct IrImportFunc<'a> {
    pub ast: &'a AstImportFunc<'a>,
    pub module: &'a str,
    pub field: &'a str,
    pub params: Vec<IrParam<'a>>,
    pub ret_ty: IrType,
}

#[derive(Clone)]
pub struct IrFuncDef<'a> {
    pub ast: &'a AstFunc<'a>,
    pub export: Option<&'a str>,
    pub params: Vec<IrParam<'a>>,
    pub ret_ty: IrType,
    pub locals: Vec<IrLocalDef<'a>>,
    pub stmts: Vec<IrStmt>,
}

impl<'a> IrFuncDef<'a> {
    pub fn num_locals(&self) -> usize {
        self.params.len() + self.locals.len()
    }
    pub fn local(&self, i: IrLocal) -> &IrLocalDef<'a> {
        if let Some(p) = self.params.get(i.idx()) {
            &p.local
        } else {
            &self.locals[i.idx() - self.params.len()]
        }
    }
    pub fn local_mut(&mut self, i: IrLocal) -> &mut IrLocalDef<'a> {
        let params_len = self.params.len();
        if let Some(p) = self.params.get_mut(i.idx()) {
            &mut p.local
        } else {
            &mut self.locals[i.idx() - params_len]
        }
    }
}

impl fmt::Debug for IrFuncDef<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("IrFuncDef")
            .field("ast.decl.name", &self.ast.decl.name)
            .field("export", &self.export)
            .field("params", &self.params)
            .field("locals", &self.locals)
            .field("stmts", &self.stmts)
            .finish()
    }
}

#[derive(Clone)]
pub struct IrModule<'a> {
    pub type_defs: Vec<IrTypeDef<'a>>,
    pub imports: Vec<IrImportFunc<'a>>,
    pub funcs: Vec<IrFuncDef<'a>>,
}

impl<'a> ops::Index<IrType> for IrModule<'a> {
    type Output = IrTypeDef<'a>;
    fn index(&self, ty: IrType) -> &IrTypeDef<'a> {
        &self.type_defs[ty.idx()]
    }
}

impl<'a> ops::IndexMut<IrType> for IrModule<'a> {
    fn index_mut(&mut self, ty: IrType) -> &mut IrTypeDef<'a> {
        &mut self.type_defs[ty.idx()]
    }
}

struct DebugSliceAsMap<'a, T>(&'a [T]);

impl<T: fmt::Debug> fmt::Debug for DebugSliceAsMap<'_, T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_map().entries(self.0.iter().enumerate()).finish()
    }
}

impl fmt::Debug for IrModule<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("IrModule")
            .field("type_defs", &DebugSliceAsMap(&self.type_defs))
            .field("funcs", &DebugSliceAsMap(&self.funcs))
            .finish()
    }
}

#[derive(Debug)]
struct GlobalProcState<'a> {
    // Type definitions
    type_defs: Vec<IrTypeDef<'a>>,
    type_name_map: HashMap<&'a str, IrType>,
    // Type processing
    array_map: HashMap<IrType, IrType>,
    stack_ptr_map: HashMap<IrType, IrType>,
    gc_ptr_map: HashMap<IrType, IrType>,
    // Imports definitions
    imports: Vec<IrImportFunc<'a>>,
    // Function definitions
    funcs: Vec<IrFuncDef<'a>>,
    func_name_map: HashMap<&'a str, IrFunc>,
    // Function processing
    cur_func_i: IrFunc,
    local_name_map: HashMap<&'a str, Vec<IrLocal>>,
    local_name_stack: Vec<&'a str>,
    undetermined_types: HashMap<IrType, Span>,
}

impl<'a> GlobalProcState<'a> {
    fn new_undetermined_type(&mut self, span: Span, bound: TypeBound) -> IrType {
        let ty = IrType::from_idx(self.type_defs.len());
        let def = IrTypeDef::new(IrTypeDefKind::Undetermined(bound));
        (self.type_defs).push(def);
        self.undetermined_types.insert(ty, span);
        ty
    }
    fn array_type_of(&mut self, ast: Either<&'a AstType, Span>, el_ty: IrType) -> Result<IrType> {
        if !self[el_ty].sized {
            return Err(Error::MustBeSized(
                ast.right_or_else(|ast| ast.span()),
                "Array items".into(),
            ));
        }

        let entry = self.array_map.entry(el_ty);
        Ok(*entry.or_insert_with(|| {
            (self.type_defs).push(IrTypeDef::new(IrTypeDefKind::Array(ast.left(), el_ty)));
            IrType::from_idx(self.type_defs.len() - 1)
        }))
    }
    fn stack_ptr_to(&mut self, ty: IrType) -> IrType {
        let entry = self.stack_ptr_map.entry(ty);
        *entry.or_insert_with(|| {
            (self.type_defs).push(IrTypeDef::new(IrTypeDefKind::StackPtr(ty)));
            IrType::from_idx(self.type_defs.len() - 1)
        })
    }
    fn gc_ptr_to(&mut self, ty: IrType) -> IrType {
        let entry = self.gc_ptr_map.entry(ty);
        *entry.or_insert_with(|| {
            (self.type_defs).push(IrTypeDef::new(IrTypeDefKind::GcPtr(ty)));
            IrType::from_idx(self.type_defs.len() - 1)
        })
    }

    fn cur_func(&self) -> &IrFuncDef<'a> {
        &self.funcs[self.cur_func_i.idx()]
    }
    fn cur_func_mut(&mut self) -> &mut IrFuncDef<'a> {
        &mut self.funcs[self.cur_func_i.idx()]
    }
    fn get_local_i(&self, name: &AstName) -> Result<IrLocal> {
        self.local_name_map
            .get(name.as_str())
            .and_then(|v| v.last().copied())
            .ok_or(Error::UseOfUndeclared(
                name.span(),
                "value".into(),
                name.as_str().to_owned(),
            ))
    }
}

impl<'a> ops::Index<IrType> for GlobalProcState<'a> {
    type Output = IrTypeDef<'a>;
    fn index(&self, ty: IrType) -> &IrTypeDef<'a> {
        &self.type_defs[ty.idx()]
    }
}

impl<'a> ops::IndexMut<IrType> for GlobalProcState<'a> {
    fn index_mut(&mut self, ty: IrType) -> &mut IrTypeDef<'a> {
        &mut self.type_defs[ty.idx()]
    }
}

fn proc_type<'a>(state: &mut GlobalProcState<'a>, ast: &'a AstType) -> Result<IrType> {
    match &ast.kind {
        AstTypeKind::Name(name) => {
            let ty = *state.type_name_map.get(name.as_str()).ok_or_else(|| {
                Error::UseOfUndeclared(name.span(), "type".into(), name.as_str().to_owned())
            })?;
            let res_ty = resolve_type(state, ty);
            if res_ty != ty {
                *state.type_name_map.get_mut(name.as_str()).unwrap() = res_ty;
            }
            Ok(res_ty)
        }
        AstTypeKind::Array(el_ty) => {
            let el_ty = proc_type(state, el_ty)?;

            state.array_type_of(Left(ast), el_ty)
        }
        AstTypeKind::StackPtr(ty) => {
            let ty = proc_type(state, ty)?;
            Ok(state.stack_ptr_to(ty))
        }
        AstTypeKind::GcPtr(ty) => {
            let ty = proc_type(state, ty)?;
            Ok(state.gc_ptr_to(ty))
        }
    }
}

fn proc_type_dfs(state: &mut GlobalProcState, visited: &mut Vec<u8>, ty: IrType) -> Result<bool> {
    visited.resize(state.type_defs.len(), 0);
    match visited[ty.idx()] {
        ref mut v @ 0 => *v = 1,
        v => return Ok(1 < v),
    }

    let def = &state[ty];
    let result = match &def.kind {
        IrTypeDefKind::Struct(def) => {
            let ast = def.ast;
            let fields = (ast.fields.iter())
                .map(|ast| {
                    Ok(IrStructDefField {
                        ast,
                        ty: proc_type(state, &ast.ty)?,
                    })
                })
                .collect::<Result<Vec<_>>>()?;

            for field in &fields {
                if !proc_type_dfs(state, visited, field.ty)? {
                    return Err(Error::RecursiveStruct(
                        ast.name.span(),
                        ast.name.as_str().to_owned(),
                        field.ast.name.as_str().to_owned(),
                    ));
                }
            }

            // let (mut zst, mut sized) = (true, true);
            let mut sized = true;
            if let Some((last_field, head_fields)) = fields.split_last() {
                for field in head_fields {
                    let def = &state[field.ty];
                    if !def.sized {
                        return Err(Error::MustBeSized(
                            field.ast.name.span(),
                            format!("Field `{}`", field.ast.name).into(),
                        ));
                    }
                    // zst &= def.zst;
                }

                let def = &state[last_field.ty];
                // zst &= def.zst;
                sized &= def.sized;
            }

            let def = &mut state[ty];
            // (def.zst, def.sized) = (zst, sized);
            def.sized = sized;
            let IrTypeDefKind::Struct(def) = &mut def.kind else {
                unreachable!()
            };
            def.fields = fields;

            true
        }
        &IrTypeDefKind::Array(ast, el) => {
            let result = proc_type_dfs(state, visited, el)?;
            if !state[el].sized {
                return Err(Error::MustBeSized(
                    ast.expect("array typedef should have an AST").span(),
                    "Array items".into(),
                ));
            }
            result
        }
        &IrTypeDefKind::Alias(ty) => proc_type_dfs(state, visited, ty)?,
        IrTypeDefKind::Undetermined(_) => unreachable!(),
        IrTypeDefKind::Primitive(_) | IrTypeDefKind::GcPtr(_) | IrTypeDefKind::StackPtr(_) => true,
    };

    visited[ty.idx()] = 2;

    Ok(result)
}

fn resolve_type<'a>(state: &mut GlobalProcState<'a>, mut ty: IrType) -> IrType {
    let mut res_ty = ty;
    while let IrTypeDefKind::Alias(aliased_ty) = state[res_ty].kind {
        res_ty = aliased_ty;
    }
    while let IrTypeDefKind::Alias(aliased_ty) = &mut state[ty].kind {
        ty = mem::replace(aliased_ty, res_ty);
    }
    debug_assert_eq!(res_ty, ty);
    ty
}

#[must_use]
fn apply_bound<'a>(
    state: &mut GlobalProcState<'a>,
    ty: IrType,
    bound: TypeBound,
    span: Span,
    is_bound_span: bool,
) -> Result<IrType> {
    type TB = TypeBound;

    let ty = resolve_type(state, ty);
    let def = &mut state[ty];

    let ok = match (bound, &mut def.kind) {
        (bound, IrTypeDefKind::Undetermined(ty_bound)) => match bound.intersection(*ty_bound) {
            Some(bound) => {
                *ty_bound = bound;
                true
            }
            None => false,
        },
        (TB::Any, _) => true,
        (TB::Array, kind) => matches!(kind, IrTypeDefKind::Array(..)),
        (TB::Sized, _) => def.sized,
        (TB::Ptr, kind) => matches!(kind, IrTypeDefKind::StackPtr(..) | IrTypeDefKind::GcPtr(..)),
        (TB::StackPtr, kind) => matches!(kind, IrTypeDefKind::StackPtr(..)),
        (TB::GcPtr, kind) => matches!(kind, IrTypeDefKind::GcPtr(..)),
        (TB::Number, IrTypeDefKind::Primitive(prim)) => prim.is_number(),
        (TB::Number, _) => false,
        (TB::Integer, IrTypeDefKind::Primitive(prim)) => prim.is_integer(),
        (TB::Integer, _) => false,
        (TB::Float, IrTypeDefKind::Primitive(prim)) => prim.is_float(),
        (TB::Float, _) => false,
    };

    match ok {
        true => Ok(ty),
        false => {
            let (ty_repr, bound_repr) = (ty.repr(&state.type_defs), bound.type_repr().to_owned());
            Err(match is_bound_span {
                true => Error::TypeMismatch(span, ty_repr, bound_repr),
                false => Error::TypeMismatch(span, bound_repr, ty_repr),
            })
        }
    }
}

fn equate_types<'a>(
    state: &mut GlobalProcState<'a>,
    span1: Span,
    ty1: IrType,
    ty2: IrType,
) -> Result<IrType> {
    if ty1 == ty2 {
        return Ok(resolve_type(state, ty1));
    }

    let def1 = unsafe { &mut *(&raw mut state.type_defs[ty1.idx()]) };
    let def2 = &mut state.type_defs[ty2.idx()];

    match (&mut def1.kind, &mut def2.kind) {
        (&mut IrTypeDefKind::Alias(aliased_ty1), &mut IrTypeDefKind::Alias(aliased_ty2)) => {
            equate_types(state, span1, aliased_ty1, aliased_ty2)
        }
        (&mut IrTypeDefKind::Alias(aliased_ty1), _) => equate_types(state, span1, aliased_ty1, ty2),
        (_, &mut IrTypeDefKind::Alias(aliased_ty2)) => equate_types(state, span1, ty1, aliased_ty2),
        (IrTypeDefKind::Undetermined(bound1), _) => {
            state.undetermined_types.remove(&ty1);
            let bound1 = bound1.take();
            def1.kind = IrTypeDefKind::Alias(ty2);
            apply_bound(state, ty2, bound1, span1, true)?;
            Ok(ty2)
        }
        (_, IrTypeDefKind::Undetermined(bound2)) => {
            state.undetermined_types.remove(&ty2);
            let bound2 = bound2.take();
            def2.kind = IrTypeDefKind::Alias(ty1);
            apply_bound(state, ty1, bound2, span1, false)?;
            Ok(ty1)
        }
        (&mut IrTypeDefKind::StackPtr(ty1), &mut IrTypeDefKind::StackPtr(ty2)) => {
            let ty = equate_types(state, span1, ty1, ty2)?;
            Ok(state.stack_ptr_to(ty))
        }
        (&mut IrTypeDefKind::GcPtr(ty1), &mut IrTypeDefKind::GcPtr(ty2)) => {
            let ty = equate_types(state, span1, ty1, ty2)?;
            Ok(state.gc_ptr_to(ty))
        }
        (&mut IrTypeDefKind::Array(_, ty1), &mut IrTypeDefKind::Array(_, ty2)) => {
            let ty = equate_types(state, span1, ty1, ty2)?;
            state.array_type_of(Right(span1), ty)
        }
        (_, _) => {
            let defs = &state.type_defs;
            return Err(Error::TypeMismatch(span1, ty2.repr(defs), ty1.repr(defs)));
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Temps {
    Never,
    Basic,
    All,
}

impl Temps {
    fn should_create(self, ast: &AstExpr) -> bool {
        match self {
            Temps::Never => false,
            Temps::Basic => matches!(
                &ast.kind,
                AstExprKind::Int(..) | AstExprKind::Float(..) | AstExprKind::Bool(..)
            ),
            Temps::All => true,
        }
    }
}

fn proc_place_expr<'a>(
    state: &mut GlobalProcState<'a>,
    ast: &'a AstExpr<'a>,
    temps: Temps,
    stack_refd: bool,
) -> Result<IrPlaceExpr> {
    let expr = match (temps, &ast.kind) {
        (_, AstExprKind::Var(name)) => {
            let local_i = state.get_local_i(name)?;
            let func = state.cur_func_mut();
            let local = func.local_mut(local_i);
            local.stack_refd |= stack_refd;
            Some(IrPlaceExpr::Local(local_i, local.ty))
        }
        (_, AstExprKind::PrefixOp(AstPrefixOp::Deref, ast)) => {
            let expr = Box::new(proc_value_expr(state, ast)?);
            let bound = match stack_refd {
                true => TypeBound::StackPtr,
                false => TypeBound::Ptr,
            };
            let ty = apply_bound(state, expr.ty(), bound, ast.span(), false)?;

            match state[ty].kind {
                IrTypeDefKind::StackPtr(ty) | IrTypeDefKind::GcPtr(ty) => {
                    Some(IrPlaceExpr::Deref(expr, ty))
                }
                _ => unreachable!(),
            }
        }
        (_, AstExprKind::FieldAccess(ast, field)) => {
            let expr = Box::new(proc_place_expr(state, ast, temps, stack_refd)?);
            let ty = resolve_type(state, expr.ty());
            match &state[ty].kind {
                IrTypeDefKind::Struct(def) => {
                    if let Some(&field) = def.field_name_map.get(field.as_str()) {
                        let ty = def.fields[field as usize].ty;
                        Some(IrPlaceExpr::FieldAccess(expr, field, ty))
                    } else {
                        return Err(Error::DoesNotHaveField(
                            ast.span(),
                            ty.repr(&state.type_defs),
                            field.as_str().to_owned(),
                        ));
                    }
                }
                IrTypeDefKind::Undetermined(TypeBound::Any) => {
                    return Err(Error::CouldNotInferType(ast.span()))
                }
                _ => {
                    return Err(Error::DoesNotHaveField(
                        ast.span(),
                        ty.repr(&state.type_defs),
                        field.as_str().to_owned(),
                    ))
                }
            }
        }
        _ => None,
    };

    match expr {
        Some(expr) => Ok(expr),
        None if temps.should_create(ast) => {
            let expr = proc_value_expr(state, ast)?;
            match expr {
                IrValueExpr::Copy(place, _) => Ok(*place),
                expr => {
                    let ty = resolve_type(state, expr.ty());

                    let func = state.cur_func_mut();
                    let local = IrLocal::from_idx(func.num_locals());
                    func.locals.push(IrLocalDef {
                        name: None,
                        ty,
                        is_param: false,
                        stack_refd: false,
                        def_stmt: func.stmts.len() as _,
                        last_use: func.stmts.len() as _,
                    });
                    func.stmts.push(IrStmt::Assign(
                        Box::new(IrPlaceExpr::Local(local, ty)),
                        Box::new(expr),
                    ));
                    Ok(IrPlaceExpr::Local(local, ty))
                }
            }
        }
        None => Err(Error::ExpectedButFound(
            ast.span(),
            "a place expression".into(),
            "a value expression".into(),
        )),
    }
}

fn proc_value_expr<'a>(state: &mut GlobalProcState<'a>, ast: &'a AstExpr) -> Result<IrValueExpr> {
    match &ast.kind {
        AstExprKind::Bool(kw) => Ok(IrValueExpr::IConst(
            IrPrimitive::Bool.into(),
            kw.is_left() as _,
        )),
        // AstExprKind::None => todo!(),
        AstExprKind::Var(_) => {
            let place = proc_place_expr(state, ast, Temps::Never, false)?;
            let ty = place.ty();
            Ok(IrValueExpr::Copy(Box::new(place), ty))
        }
        AstExprKind::Int(num, suf) => {
            let ty = match suf {
                AstIntSuffix::U8 => IrPrimitive::U8.into(),
                AstIntSuffix::U16 => IrPrimitive::U16.into(),
                AstIntSuffix::U32 => IrPrimitive::U32.into(),
                AstIntSuffix::U64 => IrPrimitive::U64.into(),
                AstIntSuffix::I8 => IrPrimitive::I8.into(),
                AstIntSuffix::I16 => IrPrimitive::I16.into(),
                AstIntSuffix::I32 => IrPrimitive::I32.into(),
                AstIntSuffix::I64 => IrPrimitive::I64.into(),
                AstIntSuffix::Auto => state.new_undetermined_type(ast.span(), TypeBound::Integer),
            };
            Ok(IrValueExpr::IConst(ty, num.value()))
        }
        AstExprKind::Float(num, suf) => {
            let ty = match suf {
                AstFloatSuffix::F32 => IrPrimitive::F32.into(),
                AstFloatSuffix::F64 => IrPrimitive::F64.into(),
                AstFloatSuffix::Auto => state.new_undetermined_type(ast.span(), TypeBound::Float),
            };
            Ok(IrValueExpr::FConst(ty, num.value()))
        }
        AstExprKind::Str(_) => todo!(),
        AstExprKind::Return(ret_kw, ast) => {
            let (span, expr) = match ast {
                Some(ast) => (ast.span(), proc_value_expr(state, ast)?),
                None => (ret_kw.span(), IrValueExpr::None),
            };
            equate_types(state, span, expr.ty(), state.cur_func().ret_ty)?;
            let func = state.cur_func_mut();
            expr.applied_on(func);
            func.stmts.push(IrStmt::Return(Box::new(expr)));

            Ok(IrValueExpr::None)
        }
        AstExprKind::Break(_, _, _) => todo!(),
        AstExprKind::Continue(_, _) => todo!(),
        AstExprKind::Loop(_, _, _) => todo!(),
        AstExprKind::Block(_, _) => todo!(),
        AstExprKind::If(_) => todo!(),
        AstExprKind::InfixOp(AstInfixOp::Assign, var_ast, val_ast) => {
            // proc_assignee_expr(state, ast)
            let place = proc_place_expr(state, var_ast, Temps::Never, false)?;
            let value = proc_value_expr(state, val_ast)?;
            equate_types(state, val_ast.span(), value.ty(), place.ty())?;

            let func = state.cur_func_mut();
            place.applied_on(func);
            value.applied_on(func);
            func.stmts
                .push(IrStmt::Assign(Box::new(place), Box::new(value)));

            Ok(IrValueExpr::None)
        }
        AstExprKind::InfixOp(op, ast1, ast2) => {
            let op = match op {
                AstInfixOp::Add => IrNumBinOp::Add,
                AstInfixOp::Sub => IrNumBinOp::Sub,
                AstInfixOp::Mul => IrNumBinOp::Mul,
                AstInfixOp::Div => IrNumBinOp::Div,
                AstInfixOp::Mod => IrNumBinOp::Mod,
                AstInfixOp::Assign => unreachable!(),
            };
            let expr1 = Box::new(proc_value_expr(state, ast1)?);
            let ty = apply_bound(state, expr1.ty(), TypeBound::Number, ast1.span(), false)?;

            let expr2 = Box::new(proc_value_expr(state, ast2)?);
            let ty = equate_types(state, ast2.span(), expr2.ty(), ty)?;

            Ok(IrValueExpr::NumBinOp(ty, op, expr1, expr2))
        }
        AstExprKind::PrefixOp(AstPrefixOp::Ref, ast) => {
            let place = proc_place_expr(state, ast, Temps::Basic, true)?;
            let ty = state.stack_ptr_to(place.ty());

            Ok(IrValueExpr::TakeStackRef(Box::new(place), ty))
        }
        AstExprKind::PrefixOp(AstPrefixOp::Deref, _ast) => todo!(),
        AstExprKind::PrefixOp(op, ast) => {
            let op = match op {
                AstPrefixOp::Neg => IrNumUnOp::Neg,
                AstPrefixOp::Not => IrNumUnOp::Not,
                AstPrefixOp::Ref | AstPrefixOp::Deref => unreachable!(),
            };
            let expr = Box::new(proc_value_expr(state, ast)?);
            let ty = apply_bound(state, expr.ty(), TypeBound::Number, ast.span(), false)?;
            Ok(IrValueExpr::NumUnOp(ty, op, expr))
        }
        AstExprKind::FieldAccess(..) => {
            let place = proc_place_expr(state, ast, Temps::All, false)?;
            let ty = place.ty();
            Ok(IrValueExpr::Copy(Box::new(place), ty))
        }
        AstExprKind::FunctionCall(func, args)
            if matches!(&func.kind,
                AstExprKind::Var(name) if name.as_str() == "len"
            ) =>
        {
            let [arg] = &**args else {
                panic!("Too many arguments to len function at {:?}", func.span());
            };
            let value = proc_value_expr(state, arg)?;
            apply_bound(state, value.ty(), TypeBound::Array, func.span(), true)?;

            Ok(IrValueExpr::ArrayLen(Box::new(value)))
        }
        AstExprKind::FunctionCall(_, _) => todo!(),
        AstExprKind::MethodCall(_, _, _) => todo!(),
    }
}

fn proc_stmt<'a>(state: &mut GlobalProcState<'a>, ast: &'a AstStmt) -> Result<()> {
    match &ast.kind {
        AstStmtKind::Expr(ast) => {
            let expr = proc_value_expr(state, ast)?;
            let func = state.cur_func_mut();
            expr.applied_on(func);
            // func.stmts.push(IrStmt::Drop(expr));

            Ok(())
        }
        AstStmtKind::Let(ast) => {
            let ty = (ast.ty.as_ref())
                .map(|ast| proc_type(state, ast))
                .transpose()?;
            let expr = Box::new(proc_value_expr(state, &ast.value)?);

            let ty = match ty {
                Some(ty) => equate_types(state, ast.value.span(), expr.ty(), ty)?,
                None => resolve_type(state, expr.ty()),
            };

            let func = &mut state.funcs[state.cur_func_i.idx()];
            let local_i = IrLocal::from_idx(func.params.len() + func.locals.len());

            state.local_name_stack.push(ast.name.as_str());
            let name_locals = state.local_name_map.entry(ast.name.as_str()).or_default();
            name_locals.push(local_i);

            func.locals.push(IrLocalDef {
                name: Some(&ast.name),
                ty,
                is_param: false,
                stack_refd: false,
                def_stmt: func.stmts.len() as _,
                last_use: func.stmts.len() as _,
            });
            func.stmts.push(IrStmt::Assign(
                Box::new(IrPlaceExpr::Local(local_i, ty)),
                expr,
            ));

            Ok(())
        }
    }
}

fn proc_param<'a>(state: &mut GlobalProcState<'a>, ast: &'a AstParam<'a>) -> Result<IrParam<'a>> {
    Ok(IrParam {
        ast,
        local: IrLocalDef {
            name: Some(&ast.name),
            ty: {
                let ty = proc_type(state, &ast.ty)?;
                if !state[ty].sized {
                    return Err(Error::MustBeSized(
                        ast.ty.span(),
                        "Function return types".into(),
                    ));
                }
                ty
            },
            is_param: true,
            stack_refd: false,
            def_stmt: 0,
            last_use: 0,
        },
    })
}

pub fn proc_module<'a>(module: &'a AstModule<'a>) -> Result<IrModule<'a>> {
    let mut state = GlobalProcState {
        type_defs: vec![
            IrTypeDef::new(IrTypeDefKind::Primitive(IrPrimitive::None)),
            IrTypeDef::new(IrTypeDefKind::Primitive(IrPrimitive::Bool)),
            IrTypeDef::new(IrTypeDefKind::Primitive(IrPrimitive::U8)),
            IrTypeDef::new(IrTypeDefKind::Primitive(IrPrimitive::U16)),
            IrTypeDef::new(IrTypeDefKind::Primitive(IrPrimitive::U32)),
            IrTypeDef::new(IrTypeDefKind::Primitive(IrPrimitive::U64)),
            IrTypeDef::new(IrTypeDefKind::Primitive(IrPrimitive::I8)),
            IrTypeDef::new(IrTypeDefKind::Primitive(IrPrimitive::I16)),
            IrTypeDef::new(IrTypeDefKind::Primitive(IrPrimitive::I32)),
            IrTypeDef::new(IrTypeDefKind::Primitive(IrPrimitive::I64)),
            IrTypeDef::new(IrTypeDefKind::Primitive(IrPrimitive::F32)),
            IrTypeDef::new(IrTypeDefKind::Primitive(IrPrimitive::F64)),
        ],
        type_name_map: HashMap::from_iter([
            ("none", IrType::from_primitive(IrPrimitive::None)),
            ("bool", IrType::from_primitive(IrPrimitive::Bool)),
            ("u8", IrType::from_primitive(IrPrimitive::U8)),
            ("u16", IrType::from_primitive(IrPrimitive::U16)),
            ("u32", IrType::from_primitive(IrPrimitive::U32)),
            ("u64", IrType::from_primitive(IrPrimitive::U64)),
            ("i8", IrType::from_primitive(IrPrimitive::I8)),
            ("i16", IrType::from_primitive(IrPrimitive::I16)),
            ("i32", IrType::from_primitive(IrPrimitive::I32)),
            ("i64", IrType::from_primitive(IrPrimitive::I64)),
            ("f32", IrType::from_primitive(IrPrimitive::F32)),
            ("f64", IrType::from_primitive(IrPrimitive::F64)),
        ]),
        array_map: HashMap::new(),
        stack_ptr_map: HashMap::new(),
        gc_ptr_map: HashMap::new(),

        imports: vec![],

        funcs: vec![],
        func_name_map: HashMap::new(),
        cur_func_i: IrFunc::from_idx(0),
        local_name_map: HashMap::new(),
        local_name_stack: Vec::new(),
        undetermined_types: HashMap::new(),
    };

    for item in &module.items {
        let AstItemKind::StructDef(ast) = &item.kind else {
            continue;
        };

        if (state.type_name_map)
            .insert(ast.name.as_str(), IrType::from_idx(state.type_defs.len()))
            .is_some()
        {
            return Err(Error::NameRedefined(
                ast.name.span(),
                ast.name.as_str().to_owned(),
            ));
        }
        let def = IrTypeDef::new(IrTypeDefKind::Struct(IrStructDef {
            ast,
            fields: vec![],
            field_name_map: (ast.fields.iter().enumerate())
                .map(|(i, ast)| (ast.name.as_str(), i as _))
                .collect(),
        }));
        // def.zst = ast.fields.is_empty();
        state.type_defs.push(def);
    }

    let mut visited = vec![0u8; state.type_defs.len()];
    for ty in (0..state.type_defs.len()).map(IrType::from_idx) {
        assert!(proc_type_dfs(&mut state, &mut visited, ty)?);
    }

    for item in &module.items {
        let AstItemKind::Import(ast) = &item.kind else {
            continue;
        };

        let params = (ast.decl.params.iter())
            .map(|ast| proc_param(&mut state, ast))
            .collect::<Result<Vec<_>>>()?;

        if (state.func_name_map)
            .insert(
                ast.decl.name.as_str(),
                IrFunc::from_idx(state.imports.len()),
            )
            .is_some()
        {
            return Err(Error::NameRedefined(
                ast.decl.name.span(),
                ast.decl.name.as_str().to_owned(),
            ));
        }

        let ret_ty = match &ast.decl.ret_ty {
            Some(ast) => proc_type(&mut state, ast)?,
            None => IrPrimitive::None.into(),
        };
        state.imports.push(IrImportFunc {
            ast,
            module: ast.module.as_str(),
            field: match &ast.field {
                Some((field, _)) => field.as_str(),
                None => ast.decl.name.as_str(),
            },
            params,
            ret_ty,
        });
    }

    for item in &module.items {
        let AstItemKind::Func(ast) = &item.kind else {
            continue;
        };

        let params = (ast.decl.params.iter())
            .map(|ast| proc_param(&mut state, ast))
            .collect::<Result<Vec<_>>>()?;

        let func_i = IrFunc::from_idx(state.imports.len() + state.funcs.len());
        if (state.func_name_map)
            .insert(ast.decl.name.as_str(), func_i)
            .is_some()
        {
            return Err(Error::NameRedefined(
                ast.decl.name.span(),
                ast.decl.name.as_str().to_owned(),
            ));
        }

        let ret_ty = match &ast.decl.ret_ty {
            Some(ast) => {
                let ty = proc_type(&mut state, ast)?;
                if !state[ty].sized {
                    return Err(Error::MustBeSized(
                        ast.span(),
                        "Function return types".into(),
                    ));
                }
                ty
            }
            None => IrPrimitive::None.into(),
        };
        state.funcs.push(IrFuncDef {
            ast,
            export: (ast.export.as_ref())
                .map(|(_, n)| n.as_ref().map_or(ast.decl.name.as_str(), |n| n.as_str())),
            params,
            ret_ty,
            locals: vec![],
            stmts: vec![],
        });
    }

    for func_i in (0..state.funcs.len()).map(IrFunc::from_idx) {
        state.cur_func_i = func_i;
        state.local_name_map.clear();
        state.local_name_stack.clear();
        for (i, param) in state.funcs[func_i.idx()].params.iter().enumerate() {
            if state
                .local_name_map
                .insert(param.ast.name.as_str(), vec![IrLocal::from_idx(i)])
                .is_some()
            {
                return Err(Error::NameRedefined(
                    param.ast.name.span(),
                    param.ast.name.as_str().to_owned(),
                ));
            }
        }

        for stmt in &state.funcs[func_i.idx()].ast.block.stmts {
            proc_stmt(&mut state, stmt)?;
        }

        for (ty, span) in state.undetermined_types.drain() {
            let def = &mut state.type_defs[ty.idx()];
            let IrTypeDefKind::Undetermined(bound) = &mut def.kind else {
                unreachable!()
            };
            match bound.take() {
                TypeBound::Integer => def.kind = IrTypeDefKind::Alias(IrPrimitive::I32.into()),
                TypeBound::Float => def.kind = IrTypeDefKind::Alias(IrPrimitive::F32.into()),
                _ => return Err(Error::CouldNotInferType(span)),
            }
        }
    }
    state.local_name_map.clear();
    state.local_name_stack.clear();

    for ty in (0..state.type_defs.len()).map(IrType::from_idx) {
        let a_ty = resolve_type(&mut state, ty);
        state[ty].sized = state[a_ty].sized;
    }

    Ok(IrModule {
        type_defs: state.type_defs,
        funcs: state.funcs,
        imports: state.imports,
    })
}
