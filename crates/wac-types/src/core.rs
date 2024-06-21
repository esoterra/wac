use indexmap::IndexMap;
use std::fmt;

/// Represents a core module type.
#[derive(Debug, Clone, Default)]
#[cfg_attr(feature = "serde", derive(serde::Serialize))]
#[cfg_attr(feature = "serde", serde(rename_all = "camelCase"))]
pub struct ModuleType {
    /// The imports of the module type.
    #[cfg_attr(feature = "serde", serde(skip_serializing_if = "IndexMap::is_empty"))]
    pub imports: IndexMap<(String, String), CoreExtern>,
    /// The exports of the module type.
    #[cfg_attr(feature = "serde", serde(skip_serializing_if = "IndexMap::is_empty"))]
    pub exports: IndexMap<String, CoreExtern>,
}

/// Represents a core extern imported or exported from a core module.
#[derive(Debug, Clone)]
#[cfg_attr(feature = "serde", derive(serde::Serialize))]
#[cfg_attr(feature = "serde", serde(rename_all = "camelCase"))]
pub enum CoreExtern {
    /// The item is a function.
    Func(CoreFuncType),
    /// The item is a table.
    #[cfg_attr(feature = "serde", serde(rename_all = "camelCase"))]
    Table {
        /// The table's element type.
        element_type: CoreRefType,
        /// Initial size of this table, in elements.
        initial: u64,
        /// Optional maximum size of the table, in elements.
        maximum: Option<u64>,

        /// TODO
        table64: bool
    },
    /// The item is a memory.
    #[cfg_attr(feature = "serde", serde(rename_all = "camelCase"))]
    Memory {
        /// Whether or not this is a 64-bit memory, using i64 as an index. If this
        /// is false it's a 32-bit memory using i32 as an index.
        ///
        /// This is part of the memory64 proposal in WebAssembly.
        memory64: bool,

        /// Whether or not this is a "shared" memory, indicating that it should be
        /// send-able across threads and the `maximum` field is always present for
        /// valid types.
        ///
        /// This is part of the threads proposal in WebAssembly.
        shared: bool,

        /// Initial size of this memory, in wasm pages.
        ///
        /// For 32-bit memories (when `memory64` is `false`) this is guaranteed to
        /// be at most `u32::MAX` for valid types.
        initial: u64,

        /// Optional maximum size of this memory, in wasm pages.
        ///
        /// For 32-bit memories (when `memory64` is `false`) this is guaranteed to
        /// be at most `u32::MAX` for valid types. This field is always present for
        /// valid wasm memories when `shared` is `true`.
        maximum: Option<u64>,

        /// TODO
        page_size_log2: Option<u32>
    },
    /// The item is a global.
    #[cfg_attr(feature = "serde", serde(rename_all = "camelCase"))]
    Global {
        /// The global's type.
        val_type: CoreType,
        /// Whether or not the global is mutable.
        mutable: bool,

        /// TODO
        shared: bool,
    },
    /// The item is a tag.
    Tag(CoreFuncType),
}

impl fmt::Display for CoreExtern {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Func(_) => write!(f, "function"),
            Self::Table { .. } => write!(f, "table"),
            Self::Memory { .. } => write!(f, "memory"),
            Self::Global { .. } => write!(f, "global"),
            Self::Tag(_) => write!(f, "tag"),
        }
    }
}

impl From<wasmparser::TableType> for CoreExtern {
    fn from(ty: wasmparser::TableType) -> Self {
        Self::Table {
            element_type: ty.element_type.into(),
            initial: ty.initial,
            maximum: ty.maximum,
            table64: ty.table64,
        }
    }
}

impl From<wasmparser::MemoryType> for CoreExtern {
    fn from(ty: wasmparser::MemoryType) -> Self {
        Self::Memory {
            memory64: ty.memory64,
            shared: ty.shared,
            initial: ty.initial,
            maximum: ty.maximum,
            page_size_log2: ty.page_size_log2,
        }
    }
}

impl From<wasmparser::GlobalType> for CoreExtern {
    fn from(ty: wasmparser::GlobalType) -> Self {
        Self::Global {
            val_type: ty.content_type.into(),
            mutable: ty.mutable,
            shared: ty.shared,
        }
    }
}

/// Represents the value types in a WebAssembly module.
#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash)]
#[cfg_attr(feature = "serde", derive(serde::Serialize))]
#[cfg_attr(feature = "serde", serde(rename_all = "camelCase"))]
pub enum CoreType {
    /// The value type is i32.
    I32,
    /// The value type is i64.
    I64,
    /// The value type is f32.
    F32,
    /// The value type is f64.
    F64,
    /// The value type is v128.
    V128,
    /// The value type is a reference.
    Ref(CoreRefType),
}

impl fmt::Display for CoreType {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::I32 => write!(f, "i32"),
            Self::I64 => write!(f, "i64"),
            Self::F32 => write!(f, "f32"),
            Self::F64 => write!(f, "f64"),
            Self::V128 => write!(f, "v128"),
            Self::Ref(r) => r.fmt(f),
        }
    }
}

impl From<wasmparser::ValType> for CoreType {
    fn from(ty: wasmparser::ValType) -> Self {
        match ty {
            wasmparser::ValType::I32 => Self::I32,
            wasmparser::ValType::I64 => Self::I64,
            wasmparser::ValType::F32 => Self::F32,
            wasmparser::ValType::F64 => Self::F64,
            wasmparser::ValType::V128 => Self::V128,
            wasmparser::ValType::Ref(ty) => Self::Ref(ty.into()),
        }
    }
}

impl From<CoreType> for wasm_encoder::ValType {
    fn from(value: CoreType) -> Self {
        match value {
            CoreType::I32 => Self::I32,
            CoreType::I64 => Self::I64,
            CoreType::F32 => Self::F32,
            CoreType::F64 => Self::F64,
            CoreType::V128 => Self::V128,
            CoreType::Ref(r) => Self::Ref(r.into()),
        }
    }
}

/// Represents the type of a reference in a WebAssembly module.
#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash)]
#[cfg_attr(feature = "serde", derive(serde::Serialize))]
#[cfg_attr(feature = "serde", serde(rename_all = "camelCase"))]
pub struct CoreRefType {
    /// Whether or not the ref type is nullable.
    pub nullable: bool,
    /// The heap type of the ref type.
    pub heap_type: HeapType,
}

impl fmt::Display for CoreRefType {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let (shared, ty) = match self.heap_type {
            HeapType::Abstract { shared, ty } => (shared, ty),
            HeapType::Concrete(i) => {
                match self.nullable {
                    true => return write!(f, "(ref null {i})"),
                    false => return write!(f, "(ref {i})"),
                }
            },
        };

        assert_eq!(shared, false); // TODO: display for shared

        let s = match (self.nullable, ty) {
            (true, AbstractHeapType::Func) => "funcref",
            (true, AbstractHeapType::Extern) => "externref",
            (true, AbstractHeapType::Any) => "anyref",
            (true, AbstractHeapType::None) => "nullref",
            (true, AbstractHeapType::NoExtern) => "nullexternref",
            (true, AbstractHeapType::NoFunc) => "nullfuncref",
            (true, AbstractHeapType::Eq) => "eqref",
            (true, AbstractHeapType::Struct) => "structref",
            (true, AbstractHeapType::Array) => "arrayref",
            (true, AbstractHeapType::I31) => "i31ref",
            (true, AbstractHeapType::Exn) => "exnref",
            (true, AbstractHeapType::NoExn) => todo!(),
            (false, AbstractHeapType::Func) => "(ref func)",
            (false, AbstractHeapType::Extern) => "(ref extern)",
            (false, AbstractHeapType::Any) => "(ref any)",
            (false, AbstractHeapType::None) => "(ref none)",
            (false, AbstractHeapType::NoExtern) => "(ref noextern)",
            (false, AbstractHeapType::NoFunc) => "(ref nofunc)",
            (false, AbstractHeapType::Eq) => "(ref eq)",
            (false, AbstractHeapType::Struct) => "(ref struct)",
            (false, AbstractHeapType::Array) => "(ref array)",
            (false, AbstractHeapType::I31) => "(ref i31)",
            (false, AbstractHeapType::Exn) => "(ref exn)",
            (false, AbstractHeapType::NoExn) => todo!(),
        };

        f.write_str(s)
    }
}

impl From<wasmparser::RefType> for CoreRefType {
    fn from(ty: wasmparser::RefType) -> Self {
        Self {
            nullable: ty.is_nullable(),
            heap_type: ty.heap_type().into(),
        }
    }
}

impl From<CoreRefType> for wasm_encoder::RefType {
    fn from(value: CoreRefType) -> Self {
        wasm_encoder::RefType {
            nullable: value.nullable,
            heap_type: value.heap_type.into(),
        }
    }
}

/// A heap type of a reference type.
#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash)]
#[cfg_attr(feature = "serde", derive(serde::Serialize))]
#[cfg_attr(feature = "serde", serde(rename_all = "camelCase"))]
pub enum HeapType {
    /// An abstract heap type; e.g., `anyref`.
    Abstract {
        /// Whether the type is shared.
        shared: bool,
        /// The actual heap type.
        ty: AbstractHeapType,
    },

    /// A concrete Wasm-defined type at the given index.
    Concrete(u32),
}

/// An abstract heap type.
#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash)]
#[cfg_attr(feature = "serde", derive(serde::Serialize))]
#[cfg_attr(feature = "serde", serde(rename_all = "camelCase"))]
pub enum AbstractHeapType {
    /// Untyped (any) function.
    Func,

    /// The abstract external heap type.
    Extern,

    /// The abstract `any` heap type.
    ///
    /// The common supertype (a.k.a. top) of all internal types.
    Any,

    /// The abstract `none` heap type.
    ///
    /// The common subtype (a.k.a. bottom) of all internal types.
    None,

    /// The abstract `noextern` heap type.
    ///
    /// The common subtype (a.k.a. bottom) of all external types.
    NoExtern,

    /// The abstract `nofunc` heap type.
    ///
    /// The common subtype (a.k.a. bottom) of all function types.
    NoFunc,

    /// The abstract `eq` heap type.
    ///
    /// The common supertype of all referenceable types on which comparison
    /// (ref.eq) is allowed.
    Eq,

    /// The abstract `struct` heap type.
    ///
    /// The common supertype of all struct types.
    Struct,

    /// The abstract `array` heap type.
    ///
    /// The common supertype of all array types.
    Array,

    /// The unboxed `i31` heap type.
    I31,

    /// The abstract `exception` heap type.
    Exn,

    /// The abstract `noexn` heap type.
    NoExn,
}

impl From<wasmparser::HeapType> for HeapType {
    fn from(ty: wasmparser::HeapType) -> Self {
        match ty {
            wasmparser::HeapType::Abstract { shared, ty } => {
                let ty = ty.into();
                Self::Abstract { shared, ty }
            },
            wasmparser::HeapType::Concrete(index) => {
                Self::Concrete(index.as_module_index().unwrap())
            }
        }
    }
}


impl From<wasmparser::AbstractHeapType> for AbstractHeapType {
    fn from(ty: wasmparser::AbstractHeapType) -> Self {
        match ty {
            wasmparser::AbstractHeapType::Any => Self::Any,
            wasmparser::AbstractHeapType::Func => Self::Func,
            wasmparser::AbstractHeapType::Extern => Self::Extern,
            wasmparser::AbstractHeapType::Eq => Self::Eq,
            wasmparser::AbstractHeapType::I31 => Self::I31,
            wasmparser::AbstractHeapType::None => Self::None,
            wasmparser::AbstractHeapType::NoExtern => Self::NoExtern,
            wasmparser::AbstractHeapType::NoFunc => Self::NoFunc,
            wasmparser::AbstractHeapType::Struct => Self::Struct,
            wasmparser::AbstractHeapType::Array => Self::Array,
            wasmparser::AbstractHeapType::Exn => Self::Exn,
            wasmparser::AbstractHeapType::NoExn => Self::NoExn,
        }
    }
}

impl From<HeapType> for wasm_encoder::HeapType {
    fn from(value: HeapType) -> Self {
        match value {
            HeapType::Abstract { shared, ty } => {
                let ty = ty.into();
                Self::Abstract { shared, ty }
            }
            HeapType::Concrete(index) => Self::Concrete(index),
        }
    }
}

impl From<AbstractHeapType> for wasm_encoder::AbstractHeapType {
    fn from(value: AbstractHeapType) -> Self {
        match value {
            AbstractHeapType::Func => Self::Func,
            AbstractHeapType::Extern => Self::Extern,
            AbstractHeapType::Any => Self::Any,
            AbstractHeapType::None => Self::None,
            AbstractHeapType::NoExtern => Self::NoExtern,
            AbstractHeapType::NoFunc => Self::NoFunc,
            AbstractHeapType::Eq => Self::Eq,
            AbstractHeapType::Struct => Self::Struct,
            AbstractHeapType::Array => Self::Array,
            AbstractHeapType::I31 => Self::I31,
            AbstractHeapType::Exn => Self::Exn,
            AbstractHeapType::NoExn => Self::NoExn,
        }
    }
}

/// Represents a core function type in a WebAssembly module.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
#[cfg_attr(feature = "serde", derive(serde::Serialize))]
#[cfg_attr(feature = "serde", serde(rename_all = "camelCase"))]
pub struct CoreFuncType {
    /// The parameters of the function.
    pub params: Vec<CoreType>,
    /// The results of the function.
    pub results: Vec<CoreType>,
}

impl fmt::Display for CoreFuncType {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "[")?;

        for (i, ty) in self.params.iter().enumerate() {
            if i > 0 {
                write!(f, ", ")?;
            }

            write!(f, "{}", ty)?;
        }

        write!(f, "] -> [")?;

        for (i, ty) in self.results.iter().enumerate() {
            if i > 0 {
                write!(f, ", ")?;
            }

            write!(f, "{}", ty)?;
        }

        write!(f, "]")
    }
}
