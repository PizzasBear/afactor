use std::{iter, rc::Rc};

extern crate wasm_encoder as wsme;

use wsme::{
    HeapType as WHeapType, RefType as WRefType, StorageType as WStorageType, ValType as WValType,
};

use crate::{code::Spanned, ir::*};

pub fn compile_hello_world() -> Vec<u8> {
    use wasm_encoder::*;

    let mut module = Module::new();

    let mut types = TypeSection::new();
    types.ty().function([], []);
    types.ty().function([WValType::I32; 4], [WValType::I32]);
    module.section(&types);
    let (_start_func_ty, fd_write_func_ty) = (0, 1);

    let mut imports = ImportSection::new();
    imports.import(
        "wasi_snapshot_preview1",
        "fd_write",
        EntityType::Function(fd_write_func_ty),
    );
    module.section(&imports);
    let fd_write_func = 0;

    let mut functions = FunctionSection::new();
    functions.function(_start_func_ty);
    module.section(&functions);
    let start_func = 1;

    let mut tables = TableSection::new();
    tables.table(TableType {
        element_type: WRefType::ANYREF,
        table64: false,
        minimum: 0,
        maximum: None,
        shared: false,
    });
    module.section(&tables);

    let mut memory = MemorySection::new();
    memory.memory(MemoryType {
        minimum: 1,
        maximum: None,
        memory64: false,
        shared: false,
        page_size_log2: None,
    });
    module.section(&memory);

    let mut exports = ExportSection::new();
    exports.export("_start", ExportKind::Func, start_func);
    exports.export("memory", ExportKind::Memory, 0);
    module.section(&exports);

    // (type (;7;) (func (param i32 i32 i32 i32) (result i32)))
    // (import "wasi_snapshot_preview1" "fd_write" (func (;0;) (type 7)))

    // type Errno = u32
    // struct Ciovec { buf: *u8, buf_len: u32 }
    // fd_write(fd: u32, iovs: *Ciovec, iovs_len: u32, size: *u32) -> Errno

    let mut codes = CodeSection::new();
    let mut start_func = Function::new([(1, WValType::I32)]);
    start_func.instruction(&Instruction::Loop(BlockType::Empty));
    start_func.instruction(&Instruction::I32Const(1)); // fd
    start_func.instruction(&Instruction::I32Const(32)); // iovs
    start_func.instruction(&Instruction::I32Const(1)); // iovs_len
    start_func.instruction(&Instruction::I32Const(24)); // size
    start_func.instruction(&Instruction::Call(fd_write_func));

    start_func.instruction(&Instruction::If(BlockType::Empty));
    start_func.instruction(&Instruction::Return);
    start_func.instruction(&Instruction::End);

    start_func.instruction(&Instruction::I32Const(24));
    start_func.instruction(&Instruction::I32Load(MemArg {
        offset: 0,
        align: 2,
        memory_index: 0,
    }));
    start_func.instruction(&Instruction::LocalSet(0));

    start_func.instruction(&Instruction::I32Const(36));
    start_func.instruction(&Instruction::I32Const(36));
    start_func.instruction(&Instruction::I32Load(MemArg {
        offset: 0,
        align: 2,
        memory_index: 0,
    }));
    start_func.instruction(&Instruction::LocalGet(0));
    start_func.instruction(&Instruction::I32Add);
    start_func.instruction(&Instruction::I32Store(MemArg {
        offset: 0,
        align: 2,
        memory_index: 0,
    }));

    start_func.instruction(&Instruction::I32Const(32));
    start_func.instruction(&Instruction::I32Load(MemArg {
        offset: 0,
        align: 2,
        memory_index: 0,
    }));
    start_func.instruction(&Instruction::LocalGet(0));
    start_func.instruction(&Instruction::I32Sub);
    start_func.instruction(&Instruction::LocalTee(0));
    start_func.instruction(&Instruction::I32Eqz);
    start_func.instruction(&Instruction::BrIf(0));

    start_func.instruction(&Instruction::I32Const(32));
    start_func.instruction(&Instruction::LocalGet(0));
    start_func.instruction(&Instruction::I32Store(MemArg {
        offset: 0,
        align: 2,
        memory_index: 0,
    }));

    start_func.instruction(&Instruction::End);

    start_func.instruction(&Instruction::End);
    codes.function(&start_func);
    module.section(&codes);

    let mut data = DataSection::new();
    let buf = b"Hello world!\n";
    data.active(0, &ConstExpr::i32_const(42), buf.iter().copied());
    data.active(
        0,
        &ConstExpr::i32_const(32),
        [42u8, 0, 0, 0, buf.len() as _, 0, 0, 0],
    );
    module.section(&data);

    let wasm_bytes = module.finish();
    wasmparser::validate(&wasm_bytes).expect("Wasm validation should succeed");

    wasm_bytes
}

#[derive(Debug, Clone, Copy)]
enum LocalTypeRepr {
    None,
    Direct(WStorageType),
    DirectI32x2,
    DirectGcPtr(IrType),
    IndirectStatic,
    IndirectDynamic,
}

impl LocalTypeRepr {
    pub const I8: Self = Self::Direct(WStorageType::I8);
    pub const I16: Self = Self::Direct(WStorageType::I16);
    pub const I32: Self = Self::Direct(WStorageType::Val(WValType::I32));
    pub const I64: Self = Self::Direct(WStorageType::Val(WValType::I64));
    pub const F32: Self = Self::Direct(WStorageType::Val(WValType::F32));
    pub const F64: Self = Self::Direct(WStorageType::Val(WValType::F64));
}
impl From<WStorageType> for LocalTypeRepr {
    fn from(value: WStorageType) -> Self {
        Self::Direct(value)
    }
}
impl From<WValType> for LocalTypeRepr {
    fn from(value: WValType) -> Self {
        Self::Direct(WStorageType::Val(value))
    }
}
impl From<WRefType> for LocalTypeRepr {
    fn from(value: WRefType) -> Self {
        Self::Direct(WStorageType::Val(value.into()))
    }
}

#[derive(Debug, Clone)]
#[allow(dead_code)]
enum HeapTypeRepr<'a> {
    ZstStruct,
    WrapperStruct {
        ir_el_ty: IrType,
        w_ty: u32,
    },
    Struct {
        ir: &'a IrStructDef<'a>,
        field_offsets: Rc<[u32]>,
        w_ty: u32,
    },
    ZstArray {
        ir_el_ty: IrType,
        w_ty: u32,
    },
    Array {
        ir_el_ty: IrType,
        w_ty: u32,
    },
    Undetermined {
        w_ty: u32,
    },
}

impl<'a> HeapTypeRepr<'a> {
    pub fn w_ty(&self) -> Option<u32> {
        match *self {
            HeapTypeRepr::ZstStruct => None,
            HeapTypeRepr::WrapperStruct { w_ty, .. }
            | HeapTypeRepr::Struct { w_ty, .. }
            | HeapTypeRepr::ZstArray { w_ty, .. }
            | HeapTypeRepr::Array { w_ty, .. }
            | Self::Undetermined { w_ty } => Some(w_ty),
        }
    }
    pub fn w_heap_type(&self) -> WHeapType {
        match self.w_ty() {
            None => wsme::HeapType::I31,
            Some(w_ty) => wsme::HeapType::Concrete(w_ty),
        }
    }
    pub fn w_ref_type(&self, nullable: bool) -> WRefType {
        WRefType {
            nullable,
            heap_type: self.w_heap_type(),
        }
    }
}

#[cfg_attr(debug_assertions, allow(dead_code))]
#[derive(Debug, Clone)]
struct StackTypeReprField {
    offset: u32,
    ty: IrType,
}

#[cfg_attr(debug_assertions, allow(dead_code))]
#[derive(Debug, Clone)]
enum StackTypeRepr {
    Zst,
    Primitive {
        size: u32,
    },
    GcPtr,
    FatStackPtr,
    Struct {
        log_align: u8,
        size: Option<u32>,
        fields: Rc<[StackTypeReprField]>,
    },
    Array {
        el_log_align: u8,
        el_size: u32,
        el_ty: IrType,
    },
}

impl StackTypeRepr {
    fn size(&self) -> Option<u32> {
        match *self {
            StackTypeRepr::Zst => Some(0),
            StackTypeRepr::Primitive { size } => Some(size),
            StackTypeRepr::GcPtr => Some(4),
            StackTypeRepr::FatStackPtr => Some(8),
            StackTypeRepr::Struct {
                size: total_size, ..
            } => total_size,
            StackTypeRepr::Array { .. } => None,
        }
    }
    fn log_align(&self) -> u8 {
        match *self {
            StackTypeRepr::Zst => 0,
            StackTypeRepr::Primitive { size } => size.checked_ilog2().unwrap_or(0) as _,
            StackTypeRepr::GcPtr => 2,
            StackTypeRepr::FatStackPtr => 2,
            StackTypeRepr::Struct { log_align, .. } => log_align,
            StackTypeRepr::Array { el_log_align, .. } => el_log_align,
        }
    }
    #[cfg_attr(debug_assertions, allow(dead_code))]
    fn align(&self) -> u32 {
        1 << self.log_align()
    }
    #[cfg_attr(debug_assertions, allow(dead_code))]
    fn is_zst(&self) -> bool {
        matches!(self, Self::Zst)
    }
}

#[derive(Debug, Default)]
struct FuncData {
    w_num_locals: u32,
    local_map: Vec<u32>,
    frame_pointer: Option<u32>,
}

#[derive(Debug)]
struct GlobalEncState<'a> {
    ir_module: &'a IrModule<'a>,
    local_type_reprs: Vec<Option<LocalTypeRepr>>,
    heap_type_reprs: Vec<Option<HeapTypeRepr<'a>>>,
    stack_type_reprs: Vec<Option<StackTypeRepr>>,
    func_data: Vec<FuncData>,
    func_types_offset: u32,
}

impl<'a> GlobalEncState<'a> {
    pub fn w_func_ty(&self, i: u32) -> u32 {
        self.func_types_offset + i
    }
}

fn repr_local_type(state: &mut GlobalEncState, ty: IrType) -> LocalTypeRepr {
    use IrTypeDefKind as IrTKind;

    if let Some(repr) = state.local_type_reprs[ty.idx()] {
        return repr;
    }

    let def = &state.ir_module[ty];
    let repr = match def.kind {
        IrTKind::Primitive(IrPrimitive::None) => LocalTypeRepr::None,
        IrTKind::Primitive(IrPrimitive::Bool | IrPrimitive::U8 | IrPrimitive::I8) => {
            LocalTypeRepr::I8
        }
        IrTKind::Primitive(IrPrimitive::U16 | IrPrimitive::I16) => LocalTypeRepr::I16,
        IrTKind::Primitive(IrPrimitive::U32 | IrPrimitive::I32) => LocalTypeRepr::I32,
        IrTKind::Primitive(IrPrimitive::U64 | IrPrimitive::I64) => LocalTypeRepr::I64,
        IrTKind::Primitive(IrPrimitive::F32) => LocalTypeRepr::F32,
        IrTKind::Primitive(IrPrimitive::F64) => LocalTypeRepr::F64,
        IrTKind::Struct(_) if !def.sized => LocalTypeRepr::IndirectDynamic,
        IrTKind::Struct(ref def) => {
            let mut repr = LocalTypeRepr::None;
            for field in &def.fields {
                repr = match (repr, repr_local_type(state, field.ty)) {
                    (repr, LocalTypeRepr::None) => repr,
                    (
                        LocalTypeRepr::None,
                        repr @ (LocalTypeRepr::Direct(_) | LocalTypeRepr::DirectGcPtr(_)),
                    ) => repr.clone(),
                    _ => {
                        repr = LocalTypeRepr::IndirectStatic;
                        break;
                    }
                };
            }
            repr
        }
        IrTKind::Array(_, el_ty) => {
            let el_repr = repr_local_type(state, el_ty);
            match el_repr {
                LocalTypeRepr::None => LocalTypeRepr::I32,
                _ => LocalTypeRepr::IndirectDynamic,
            }
        }
        IrTKind::GcPtr(ty) => match &state.heap_type_reprs[ty.idx()] {
            Some(repr) => repr.w_ref_type(true).into(),
            None => LocalTypeRepr::DirectGcPtr(ty),
        },
        IrTKind::StackPtr(ty) => match state.ir_module[ty].sized {
            true => LocalTypeRepr::I32,
            false => LocalTypeRepr::DirectI32x2,
        },
        IrTKind::Alias(ty) => repr_local_type(state, ty).clone(),
        IrTKind::Undetermined(_) => unreachable!(),
    };

    *state.local_type_reprs[ty.idx()].insert(repr)
}

fn repr_heap_types(state: &mut GlobalEncState, w_types: &mut Vec<wsme::SubType>) {
    fn w_mew_placeholder_type(w_types: &mut Vec<wsme::SubType>) -> u32 {
        let w_ty = w_types.len() as _;
        w_types.push(wsme::SubType {
            composite_type: wsme::CompositeType {
                inner: wsme::CompositeInnerType::Struct(wsme::StructType {
                    fields: Box::new([]),
                }),
                shared: false,
            },
            supertype_idx: None,
            is_final: true,
        });
        w_ty
    }
    fn w_write_wrap_struct(w_type: &mut wsme::SubType, element_type: WStorageType) {
        w_type.composite_type.inner = wsme::CompositeInnerType::Struct(wsme::StructType {
            fields: Box::new([wsme::FieldType {
                element_type,
                mutable: true,
            }]),
        });
    }

    fn w_write_array(w_type: &mut wsme::SubType, element_type: WStorageType) {
        w_type.composite_type.inner =
            wsme::CompositeInnerType::Array(wsme::ArrayType(wsme::FieldType {
                element_type,
                mutable: true,
            }));
    }

    fn rec<'a, 'b>(
        state: &'a mut GlobalEncState<'b>,
        w_types: &mut Vec<wsme::SubType>,
        ty: IrType,
    ) -> &'a HeapTypeRepr<'b> {
        let repr = state.heap_type_reprs[ty.idx()].take();

        let def = &state.ir_module[ty];
        let repr = repr.unwrap_or_else(|| match def.kind {
            IrTypeDefKind::Primitive(_) => match repr_local_type(state, ty) {
                LocalTypeRepr::None => HeapTypeRepr::ZstStruct,
                LocalTypeRepr::Direct(st) => {
                    let w_ty = w_mew_placeholder_type(w_types);
                    w_write_wrap_struct(&mut w_types[w_ty as usize], st);
                    HeapTypeRepr::WrapperStruct { ir_el_ty: ty, w_ty }
                }
                LocalTypeRepr::DirectI32x2
                | LocalTypeRepr::DirectGcPtr(_)
                | LocalTypeRepr::IndirectStatic
                | LocalTypeRepr::IndirectDynamic => unreachable!(),
            },
            IrTypeDefKind::Struct(ref def) => {
                if matches!(repr_local_type(state, ty), LocalTypeRepr::None) {
                    return HeapTypeRepr::ZstStruct;
                }

                let w_ty = w_mew_placeholder_type(w_types);
                state.heap_type_reprs[ty.idx()] = Some(HeapTypeRepr::Undetermined { w_ty });

                let mut field_map = Vec::with_capacity(def.fields.len());
                let mut w_fields = Vec::with_capacity(def.fields.len());
                for field in &def.fields {
                    field_map.push(w_fields.len() as _);

                    match repr_local_type(state, field.ty) {
                        LocalTypeRepr::None => {}
                        LocalTypeRepr::Direct(element_type) => w_fields.push(wsme::FieldType {
                            element_type,
                            mutable: true,
                        }),
                        LocalTypeRepr::DirectI32x2 => {
                            w_fields.push(wsme::FieldType {
                                element_type: WStorageType::Val(WValType::I32),
                                mutable: true,
                            });
                            w_fields.push(wsme::FieldType {
                                element_type: WStorageType::Val(WValType::I32),
                                mutable: true,
                            });
                        }
                        LocalTypeRepr::DirectGcPtr(to_ty) => {
                            let w_ref_ty = rec(state, w_types, to_ty).w_ref_type(true);
                            state.local_type_reprs[to_ty.idx()] = Some(w_ref_ty.into());

                            w_fields.push(wsme::FieldType {
                                element_type: WStorageType::Val(w_ref_ty.into()),
                                mutable: true,
                            })
                        }
                        LocalTypeRepr::IndirectStatic => {
                            let field_repr = rec(state, w_types, field.ty);

                            let w_ty = match *field_repr {
                                HeapTypeRepr::Struct { w_ty, .. } => w_ty,
                                HeapTypeRepr::ZstStruct
                                | HeapTypeRepr::WrapperStruct { .. }
                                | HeapTypeRepr::ZstArray { .. } => unreachable!(
                                    "Should have been localy represented as \
                                    `LocalTypeRepr::Direct`"
                                ),
                                HeapTypeRepr::Array { .. } => unreachable!(
                                    "Should have been localy represented as \
                                    `LocalTypeRepr::IndirectDynamic`"
                                ),
                                HeapTypeRepr::Undetermined { .. } => unreachable!(),
                            };
                            let w_def = &w_types[w_ty as usize].composite_type.inner;
                            let wsme::CompositeInnerType::Struct(w_def) = w_def else {
                                unreachable!(
                                    "heap structs must be represented with wasm gc structs"
                                );
                            };
                            w_fields.extend_from_slice(&w_def.fields);
                        }
                        LocalTypeRepr::IndirectDynamic => {
                            todo!(
                                "Heap structs with unsized fields \
                                are not yet unimplemented, at {:?}",
                                field.ast.ty.span()
                            )
                        }
                    }
                }

                w_types[w_ty as usize].composite_type.inner =
                    wsme::CompositeInnerType::Struct(wsme::StructType {
                        fields: w_fields.into(),
                    });
                HeapTypeRepr::Struct {
                    ir: def,
                    field_offsets: field_map.into(),
                    w_ty,
                }
            }
            IrTypeDefKind::Array(ast, ir_el_ty) => match repr_local_type(state, ir_el_ty) {
                LocalTypeRepr::Direct(st) => {
                    let w_ty = w_mew_placeholder_type(w_types);
                    w_write_array(&mut w_types[w_ty as usize], st);
                    HeapTypeRepr::Array { ir_el_ty, w_ty }
                }
                LocalTypeRepr::DirectGcPtr(to_ty) => {
                    let w_ty = w_mew_placeholder_type(w_types);
                    state.heap_type_reprs[ty.idx()] = Some(HeapTypeRepr::Undetermined { w_ty });

                    let w_ref_ty = rec(state, w_types, to_ty).w_ref_type(true);
                    state.local_type_reprs[to_ty.idx()] = Some(w_ref_ty.into());

                    w_write_array(
                        &mut w_types[w_ty as usize],
                        WStorageType::Val(w_ref_ty.into()),
                    );
                    HeapTypeRepr::Array { ir_el_ty, w_ty }
                }
                LocalTypeRepr::DirectI32x2
                | LocalTypeRepr::IndirectStatic
                | LocalTypeRepr::IndirectDynamic => todo!(
                    "Heap arrays with non primitive elements \
                    are not yet unimplemented, at {:?}",
                    ast.map(|ast| ast.span())
                ),
                LocalTypeRepr::None => HeapTypeRepr::ZstArray {
                    ir_el_ty,
                    w_ty: rec(state, w_types, IrPrimitive::U32.into()).w_ty().unwrap(),
                },
            },
            IrTypeDefKind::GcPtr(to_ty) => {
                let w_ty = w_mew_placeholder_type(w_types);
                state.heap_type_reprs[ty.idx()] = Some(HeapTypeRepr::Undetermined { w_ty });
                match rec(state, w_types, to_ty).w_ty() {
                    None => {
                        w_write_wrap_struct(
                            &mut w_types[w_ty as usize],
                            WStorageType::Val(WValType::Ref(WRefType::I31REF)),
                        );
                        HeapTypeRepr::WrapperStruct { ir_el_ty: ty, w_ty }
                    }
                    Some(w_ty) => {
                        w_write_wrap_struct(
                            &mut w_types[w_ty as usize],
                            WStorageType::Val(WValType::Ref(WRefType {
                                nullable: true,
                                heap_type: WHeapType::Concrete(w_ty),
                            })),
                        );
                        HeapTypeRepr::WrapperStruct { ir_el_ty: ty, w_ty }
                    }
                }
            }
            IrTypeDefKind::StackPtr(_) => rec(state, w_types, IrPrimitive::U32.into()).clone(),
            IrTypeDefKind::Alias(ty) => rec(state, w_types, ty).clone(),
            IrTypeDefKind::Undetermined(_) => unreachable!(),
        });
        state.heap_type_reprs[ty.idx()].insert(repr)
    }

    let type_defs = &state.ir_module.type_defs;
    state.local_type_reprs = type_defs.iter().map(|_| None).collect();
    for def in type_defs {
        if let IrTypeDefKind::GcPtr(ty) = def.kind {
            rec(state, w_types, ty);
        }
    }
}

#[cfg_attr(debug_assertions, allow(dead_code))]
fn repr_stack_type<'a>(state: &'a mut GlobalEncState, ty: IrType) -> &'a StackTypeRepr {
    let repr = state.stack_type_reprs[ty.idx()].take();

    let def = &state.ir_module[ty];
    let repr = repr.unwrap_or_else(|| match def.kind {
        IrTypeDefKind::Primitive(prim) => StackTypeRepr::Primitive {
            size: prim.byte_size(),
        },
        IrTypeDefKind::Struct(ref def) => {
            let mut total_size = Some(0);
            let mut total_log_align = 0;
            let mut fields = Vec::with_capacity(def.fields.len());

            for field in &def.fields {
                let field_repr = repr_stack_type(state, field.ty);

                let log_align = field_repr.log_align();
                let align_mask = (1 << log_align) - 1;
                let offset = total_size.unwrap() + align_mask & !align_mask;
                fields.push(StackTypeReprField {
                    offset,
                    ty: field.ty,
                });
                total_size = field_repr.size().map(|size| total_size.unwrap() + size);
                total_log_align = total_log_align.max(log_align);
            }

            let align_mask = (1 << total_log_align) - 1;
            StackTypeRepr::Struct {
                log_align: total_log_align,
                size: total_size.map(|s| s + align_mask & !align_mask),
                fields: fields.into(),
            }
        }
        IrTypeDefKind::Array(_, el_ty) => {
            let repr = repr_stack_type(state, el_ty);
            StackTypeRepr::Array {
                el_log_align: repr.log_align(),
                el_size: repr.size().expect("Array element cannot be unsized"),
                el_ty,
            }
        }
        IrTypeDefKind::GcPtr(_) => StackTypeRepr::GcPtr,
        IrTypeDefKind::StackPtr(ptr) => match state.ir_module[ptr].sized {
            true => StackTypeRepr::Primitive { size: 4 },
            false => StackTypeRepr::FatStackPtr,
        },
        IrTypeDefKind::Alias(ty) => repr_stack_type(state, ty).clone(),
        IrTypeDefKind::Undetermined(_) => unreachable!(),
    });

    state.stack_type_reprs[ty.idx()].insert(repr)
}

// /// Converts an [`IrType`] into a Wasm value type.
// /// Useful for Wasm function parameters and returns.
// ///
// /// Only returns [`None`] for zero sized types.
// fn ir_type_to_val_type(state: &GlobalEncState, ty: IrType) -> Option<WValType> {
//     let ty = resolve_ir_type(state, ty);
//     let ty_def = &state.ir_module[ty];
//     if ty_def.zst {
//         return None;
//     }
//     Some(match ty_def.kind {
//         IrTypeDefKind::Primitive(IrPrimitive::F64) => WValType::F64,
//         IrTypeDefKind::Primitive(IrPrimitive::F32) => WValType::F32,
//         IrTypeDefKind::Primitive(IrPrimitive::I64 | IrPrimitive::U64) => WValType::I64,
//         IrTypeDefKind::Primitive(
//             IrPrimitive::I32
//             | IrPrimitive::I16
//             | IrPrimitive::I8
//             | IrPrimitive::U32
//             | IrPrimitive::U16
//             | IrPrimitive::U8,
//         ) => WValType::I32,
//         IrTypeDefKind::Primitive(IrPrimitive::None) => unreachable!(),
//         IrTypeDefKind::Struct(ref def) => match def.fields.as_slice() {
//             [] => unreachable!(),
//             [f] => ir_type_to_val_type(&state, f.ty).unwrap(),
//             [..] => WValType::I32,
//         },
//         IrTypeDefKind::Array(_, _) => WValType::I32,
//         IrTypeDefKind::GcPtr(ty) => match state[resolve_ir_type(state, ty)].get() {
//             Some(w_ty) => WValType::Ref(WRefType {
//                 nullable: true,
//                 heap_type: wsme::HeapType::Concrete(w_ty),
//             }),
//             None => WValType::Ref(WRefType::I31REF),
//         },
//         IrTypeDefKind::StackPtr(_) => WValType::I32,
//         IrTypeDefKind::Alias(_) | IrTypeDefKind::Undetermined(_) => unreachable!(),
//     })
// }

pub fn compile(ir_module: &IrModule) -> Vec<u8> {
    let mut state = GlobalEncState {
        ir_module,
        func_types_offset: 0,
        heap_type_reprs: vec![None; ir_module.type_defs.len()],
        func_data: {
            let mut func_data = vec![];
            func_data.resize_with(
                ir_module.imports.len() + ir_module.funcs.len(),
                Default::default,
            );
            func_data
        },
        local_type_reprs: vec![None; ir_module.type_defs.len()],
        stack_type_reprs: vec![None; ir_module.type_defs.len()],
    };

    let mut w_module = wsme::Module::new();

    let mut w_types = wsme::TypeSection::new();

    let mut w_rec_types = Vec::new();

    repr_heap_types(&mut state, &mut w_rec_types);
    state.func_types_offset = w_rec_types.len() as _;

    if !w_rec_types.is_empty() {
        w_types.ty().rec(w_rec_types);
    }

    // LocalTypeRepr::DirectGcPtr should never be needed anymore,
    // because we instantiated all heap types already.
    for repr in &mut state.local_type_reprs {
        let Some(LocalTypeRepr::DirectGcPtr(ty)) = repr else {
            continue;
        };
        *repr = Some(
            state.heap_type_reprs[ty.idx()]
                .as_ref()
                .unwrap()
                .w_ref_type(true)
                .into(),
        );
    }

    for (i, ir_import) in ir_module.imports.iter().enumerate() {
        let mut w_locals = vec![];

        let ret_ty: &[_] = match repr_local_type(&mut state, ir_import.ret_ty) {
            LocalTypeRepr::None => &[],
            LocalTypeRepr::Direct(st) => &[st.unpack()],
            LocalTypeRepr::DirectI32x2 => &[WValType::I32; 2],
            LocalTypeRepr::DirectGcPtr(_) => unreachable!(),
            LocalTypeRepr::IndirectStatic => {
                w_locals.push(WValType::I32);
                &[]
            }
            LocalTypeRepr::IndirectDynamic => unreachable!(),
        };

        for ir_param in &ir_import.params {
            let repr = repr_local_type(&mut state, ir_param.local.ty);
            state.func_data[i].local_map.push(w_locals.len() as _);
            match repr {
                LocalTypeRepr::None => {}
                LocalTypeRepr::Direct(st) => w_locals.push(st.unpack()),
                LocalTypeRepr::DirectI32x2 => {
                    w_locals.push(WValType::I32);
                    w_locals.push(WValType::I32);
                }
                LocalTypeRepr::DirectGcPtr(_) => unreachable!(),
                LocalTypeRepr::IndirectStatic => w_locals.push(WValType::I32),
                LocalTypeRepr::IndirectDynamic => {
                    w_locals.push(WValType::I32);
                    w_locals.push(WValType::I32);
                }
            };
        }
        state.func_data[i].w_num_locals = w_locals.len() as _;
        w_types.ty().function(w_locals, ret_ty.iter().copied());
    }
    for (i, ir_func) in ir_module.funcs.iter().enumerate() {
        let i = ir_module.imports.len() + i;

        let mut w_locals = vec![];

        let ret_ty: &[_] = match repr_local_type(&mut state, ir_func.ret_ty) {
            LocalTypeRepr::None => &[],
            LocalTypeRepr::Direct(st) => &[st.unpack()],
            LocalTypeRepr::DirectI32x2 => &[WValType::I32; 2],
            LocalTypeRepr::DirectGcPtr(_) => unreachable!(),
            LocalTypeRepr::IndirectStatic => {
                w_locals.push(WValType::I32);
                &[]
            }
            LocalTypeRepr::IndirectDynamic => unreachable!(),
        };

        for ir_param in &ir_func.params {
            let repr = repr_local_type(&mut state, ir_param.local.ty);
            state.func_data[i].local_map.push(w_locals.len() as _);
            match repr {
                LocalTypeRepr::None => {}
                LocalTypeRepr::Direct(st) => w_locals.push(st.unpack()),
                LocalTypeRepr::DirectI32x2 => {
                    w_locals.push(WValType::I32);
                    w_locals.push(WValType::I32);
                }
                LocalTypeRepr::DirectGcPtr(_) => unreachable!(),
                LocalTypeRepr::IndirectStatic => w_locals.push(WValType::I32),
                LocalTypeRepr::IndirectDynamic => {
                    w_locals.push(WValType::I32);
                    w_locals.push(WValType::I32);
                }
            };
        }
        state.func_data[i].w_num_locals = w_locals.len() as _;
        w_types.ty().function(w_locals, ret_ty.iter().copied());
    }

    w_module.section(&w_types);
    w_module.section(&{
        let mut w_imports = wsme::ImportSection::new();

        for (i, ir_import) in ir_module.imports.iter().enumerate() {
            w_imports.import(
                ir_import.module,
                ir_import.field,
                wsme::EntityType::Function(state.w_func_ty(i as _)),
            );
        }

        w_imports
    });
    w_module.section(&{
        let mut w_funcs = wsme::FunctionSection::new();

        for (i, _func) in ir_module.funcs.iter().enumerate() {
            w_funcs.function(state.w_func_ty((ir_module.imports.len() + i) as _));
        }

        w_funcs
    });
    w_module.section(&{
        let mut w_tables = wsme::TableSection::new();

        w_tables.table(wsme::TableType {
            element_type: WRefType::ANYREF,
            table64: false,
            minimum: 4 * 65536,
            maximum: None,
            shared: false,
        });

        w_tables
    });
    w_module.section(&{
        let mut w_memory = wsme::MemorySection::new();

        w_memory.memory(wsme::MemoryType {
            minimum: 17,
            maximum: None,
            memory64: false,
            shared: false,
            page_size_log2: None,
        });

        w_memory
    });
    w_module.section(&{
        let mut w_globals = wsme::GlobalSection::new();

        w_globals.global(
            wsme::GlobalType {
                val_type: WValType::I32,
                mutable: true,
                shared: false,
            },
            &wsme::ConstExpr::i32_const(16 * 65536),
        );

        w_globals
    });
    w_module.section(&{
        let mut w_exports = wsme::ExportSection::new();

        w_exports.export("memory", wsme::ExportKind::Memory, 0);
        for (i, ir_func) in ir_module.funcs.iter().enumerate() {
            let Some(name) = ir_func.export else {
                continue;
            };
            let idx = (ir_module.imports.len() + i) as _;
            w_exports.export(name, wsme::ExportKind::Func, idx);
        }

        w_exports
    });
    // start_section
    // element_section
    // datacount_section
    let mut w_code = wsme::CodeSection::new();

    for (i, ir_func) in ir_module.funcs.iter().enumerate() {
        let i = ir_module.imports.len() + i;

        let mut w_locals = vec![];
        let mut all_sized = true;
        for ir_local in &ir_func.locals {
            let sized = ir_module[ir_local.ty].sized;
            all_sized &= sized;
            let repr = repr_local_type(&mut state, ir_local.ty);
            let func_data = &mut state.func_data[i];
            (func_data.local_map).push(func_data.w_num_locals);
            let (w_width, w_ty) = match repr {
                LocalTypeRepr::Direct(st) => (1, st.unpack()),
                LocalTypeRepr::DirectI32x2 => (2, WValType::I32),
                LocalTypeRepr::IndirectStatic => continue,
                LocalTypeRepr::IndirectDynamic => (2, WValType::I32),
                LocalTypeRepr::DirectGcPtr(_) => unreachable!(),
                LocalTypeRepr::None => continue,
            };
            func_data.w_num_locals += w_width;
            match w_locals.last_mut().filter(|(_, t)| *t == w_ty) {
                Some((w_num, _)) => *w_num += w_width,
                None => w_locals.push((w_width, w_ty)),
            }
        }
        let func_data = &mut state.func_data[i];
        if !all_sized {
            func_data.frame_pointer = Some(func_data.w_num_locals);

            let w_ty = WValType::I32;
            func_data.w_num_locals += 1;
            match w_locals.last_mut().filter(|(_, t)| *t == w_ty) {
                Some((w_num, _)) => *w_num += 1,
                None => w_locals.push((1, w_ty)),
            }
        }

        let mut w_func = wsme::Function::new(w_locals);
        w_func.instruction(&wsme::Instruction::Unreachable);
        w_func.instruction(&wsme::Instruction::End);
        w_code.function(&w_func);
    }

    w_module.section(&w_code);

    w_module.section(&{
        let mut w_names = wsme::NameSection::new();
        w_names.module("out");

        let mut w_func_names = wsme::NameMap::new();

        for (i, ir_import) in ir_module.imports.iter().enumerate() {
            w_func_names.append(i as _, ir_import.ast.decl.name.as_str());
        }

        for (i, ir_func) in ir_module.funcs.iter().enumerate() {
            let i = (ir_module.imports.len() + i) as _;
            w_func_names.append(i, ir_func.ast.decl.name.as_str());
        }

        w_names.functions(&w_func_names);
        let mut w_local_names = wsme::IndirectNameMap::new();

        for (i, (ir_import, func_data)) in
            iter::zip(&ir_module.imports, &state.func_data).enumerate()
        {
            let mut w_names = wsme::NameMap::new();

            match state.local_type_reprs[ir_import.ret_ty.idx()].unwrap() {
                LocalTypeRepr::None | LocalTypeRepr::Direct(_) | LocalTypeRepr::DirectI32x2 => {}
                LocalTypeRepr::IndirectStatic => w_names.append(0, "return-ptr"),
                LocalTypeRepr::DirectGcPtr(_) => unreachable!(),
                LocalTypeRepr::IndirectDynamic => unreachable!(),
            }

            for (&w_local, ir_param) in iter::zip(&func_data.local_map, &ir_import.params) {
                let Some(name) = ir_param.local.name else {
                    continue;
                };

                match state.local_type_reprs[ir_param.local.ty.idx()].unwrap() {
                    LocalTypeRepr::None => {}
                    LocalTypeRepr::Direct(_) | LocalTypeRepr::IndirectDynamic => {
                        w_names.append(w_local, name.as_str())
                    }
                    LocalTypeRepr::DirectI32x2 => {
                        w_names.append(w_local, &format!("{name}.ptr"));
                        w_names.append(w_local + 1, &format!("{name}.len"));
                    }
                    LocalTypeRepr::IndirectStatic => {}
                    LocalTypeRepr::DirectGcPtr(_) => unreachable!(),
                }
            }

            w_local_names.append(i as _, &w_names);
        }

        for (i, (ir_func, func_data)) in Iterator::enumerate(iter::zip(
            &ir_module.funcs,
            &state.func_data[ir_module.imports.len()..],
        )) {
            let mut w_names = wsme::NameMap::new();

            match state.local_type_reprs[ir_func.ret_ty.idx()].unwrap() {
                LocalTypeRepr::None | LocalTypeRepr::Direct(_) | LocalTypeRepr::DirectI32x2 => {}
                LocalTypeRepr::IndirectStatic => w_names.append(0, "return-ptr"),
                LocalTypeRepr::DirectGcPtr(_) => unreachable!(),
                LocalTypeRepr::IndirectDynamic => unreachable!(),
            }

            for (ir_local_i, &w_local) in func_data.local_map.iter().enumerate() {
                let local = ir_func.local(IrLocal::from_idx(ir_local_i));
                let Some(name) = local.name else {
                    continue;
                };
                match state.local_type_reprs[local.ty.idx()].unwrap() {
                    LocalTypeRepr::None => {}
                    LocalTypeRepr::Direct(_) | LocalTypeRepr::IndirectDynamic => {
                        w_names.append(w_local, name.as_str())
                    }
                    LocalTypeRepr::DirectI32x2 => {
                        w_names.append(w_local, &format!("{name}.ptr"));
                        w_names.append(w_local + 1, &format!("{name}.len"));
                    }
                    LocalTypeRepr::IndirectStatic => {}
                    LocalTypeRepr::DirectGcPtr(_) => unreachable!(),
                }
            }

            w_local_names.append((ir_module.imports.len() + i) as _, &w_names);
        }

        w_names.locals(&w_local_names);
        let mut w_type_names = wsme::NameMap::new();

        let mut ordered_type_map: Vec<_> = (state.heap_type_reprs.iter())
            .enumerate()
            .filter_map(|(i, repr)| Some((repr.as_ref()?.w_ty()?, IrType::from_idx(i))))
            .collect();

        ordered_type_map.sort_unstable_by_key(|&(w_ty, _)| w_ty);

        for &(w_ty, ir_ty) in &ordered_type_map {
            w_type_names.append(w_ty, &ir_ty.repr(&ir_module.type_defs));
        }

        for (i, ir_import) in ir_module.imports.iter().enumerate() {
            let w_ty = state.w_func_ty(i as _);
            w_type_names.append(w_ty, ir_import.ast.decl.name.as_str());
        }

        for (i, ir_func) in ir_module.funcs.iter().enumerate() {
            let w_ty = state.w_func_ty((ir_module.imports.len() + i) as _);
            w_type_names.append(w_ty, ir_func.ast.decl.name.as_str());
        }

        w_names.types(&w_type_names);
        let mut w_table_names = wsme::NameMap::new();

        w_table_names.append(0, "ref_stack");

        w_names.tables(&w_table_names);
        let mut w_memory_names = wsme::NameMap::new();

        w_memory_names.append(0, "main");

        w_names.memories(&w_memory_names);
        let mut w_global_names = wsme::NameMap::new();

        w_global_names.append(0, "stack_pointer");

        w_names.globals(&w_global_names);
        let mut w_field_names = wsme::IndirectNameMap::new();

        for &(w_ty, ir_ty) in &ordered_type_map {
            match state.heap_type_reprs[ir_ty.idx()].as_ref().unwrap() {
                HeapTypeRepr::Struct {
                    ir,
                    field_offsets: field_map,
                    ..
                } => {
                    let mut w_names = wsme::NameMap::new();
                    for (&i, field) in iter::zip(&**field_map, &ir.fields) {
                        match state.local_type_reprs[field.ty.idx()].as_ref().unwrap() {
                            LocalTypeRepr::None => {}
                            LocalTypeRepr::Direct(_) => w_names.append(i, field.ast.name.as_str()),
                            LocalTypeRepr::DirectI32x2 => {
                                w_names.append(i, &format!("{}.ptr", field.ast.name));
                                w_names.append(i + 1, &format!("{}.len", field.ast.name));
                            }
                            LocalTypeRepr::IndirectStatic => {
                                w_names.append(i, &format!("{}-start-", field.ast.name));
                                // TODO: add fields for substructs
                            }
                            LocalTypeRepr::IndirectDynamic => {
                                todo!("Indirect dynamic fields not yet supported")
                            }
                            LocalTypeRepr::DirectGcPtr(_) => unreachable!(),
                        }
                    }
                    w_field_names.append(w_ty, &w_names);
                }
                HeapTypeRepr::WrapperStruct { .. }
                | HeapTypeRepr::ZstArray { .. }
                | HeapTypeRepr::Array { .. } => {}
                HeapTypeRepr::ZstStruct | HeapTypeRepr::Undetermined { .. } => unreachable!(),
            }
        }

        w_names.fields(&w_field_names);

        w_names
    });

    let wasm_bytes = w_module.finish();
    wasmparser::validate(&wasm_bytes).expect("Wasm validation should succeed");

    wasm_bytes
}
