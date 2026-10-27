use std::collections::HashMap;

use crate::ast::{Mutability, QualIdent};

#[derive(Clone, Debug)]
pub struct Global<T> {
    pub qualid: QualIdent,
    pub info: T,
}

pub const GENERIC: i32 = -1;
pub const NOTGENERIC: i32 = 0;

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct TypId(pub u32);

#[derive(Clone, Debug)]
pub struct Typ {
    pub desc: TypDesc,
    pub level: i32,
}

#[derive(Clone, Debug)]
pub enum TypDesc {
    Tvar(TypLink),
    Tarrow(TypId, TypId),
    Tproduct(Vec<TypId>),
    Tconstr(TypeConstrId, Vec<TypId>),
}

#[derive(Clone, Debug)]
pub enum TypLink {
    Tnolink,
    Tlinkto(TypId),
}

#[derive(Default)]
pub struct TypeArena {
    types: Vec<Typ>,
}

impl TypeArena {
    pub fn new() -> Self {
        TypeArena { types: Vec::new() }
    }

    pub fn alloc(&mut self, desc: TypDesc, level: i32) -> TypId {
        let id = TypId(self.types.len() as u32);
        self.types.push(Typ { desc, level });
        id
    }

    pub fn get(&self, id: TypId) -> &Typ {
        &self.types[id.0 as usize]
    }

    pub fn get_mut(&mut self, id: TypId) -> &mut Typ {
        &mut self.types[id.0 as usize]
    }

    pub fn set_desc(&mut self, id: TypId, desc: TypDesc) {
        self.get_mut(id).desc = desc;
    }

    pub fn set_level(&mut self, id: TypId, level: i32) {
        self.get_mut(id).level = level;
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct TypeConstrId(pub u32);

#[derive(Clone, Debug)]
pub enum TypeAbbrev {
    Tnotabbrev,
    Tabbrev(Vec<TypId>, TypId),
}

#[derive(Default)]
pub struct TypeConstrArena {
    entries: Vec<Global<TypeInfo>>,
    by_name: HashMap<String, TypeConstrId>,
}

impl TypeConstrArena {
    pub fn new() -> Self {
        TypeConstrArena {
            entries: Vec::new(),
            by_name: std::collections::HashMap::new(),
        }
    }

    pub fn alloc(&mut self, qualid: QualIdent, info: TypeInfo) -> TypeConstrId {
        let id = TypeConstrId(self.entries.len() as u32);
        self.by_name.insert(qualid.id.clone(), id);
        self.entries.push(Global { qualid, info });
        id
    }

    pub fn find_by_name(&self, name: &str) -> Option<TypeConstrId> {
        self.by_name.get(name).copied()
    }

    pub fn find_by_qual_name(&self, qual: &str, name: &str) -> Option<TypeConstrId> {
        self.entries
            .iter()
            .find(|entry| entry.qualid.qual == qual && entry.qualid.id == name)
            .map(|entry| {
                let index = self
                    .entries
                    .iter()
                    .position(|candidate| candidate.qualid == entry.qualid)
                    .expect("type constructor entry must exist");
                TypeConstrId(index as u32)
            })
    }

    pub fn get(&self, id: TypeConstrId) -> &Global<TypeInfo> {
        &self.entries[id.0 as usize]
    }

    pub fn get_mut(&mut self, id: TypeConstrId) -> &mut Global<TypeInfo> {
        &mut self.entries[id.0 as usize]
    }

    pub fn replace(&mut self, id: TypeConstrId, info: TypeInfo) -> TypeInfo {
        std::mem::replace(&mut self.entries[id.0 as usize].info, info)
    }

    pub fn same_type_constr(&self, a: TypeConstrId, b: TypeConstrId) -> bool {
        a == b
    }
}

#[derive(Clone, Debug)]
pub struct TypeInfo {
    pub ty_abbr: TypeAbbrev,
    pub ty_arity: i32,
    pub ty_desc: TypeComponents,
}

#[derive(Clone, Debug)]
pub enum TypeComponents {
    AbstractType,
    VariantType(Vec<ConstrDescId>),
    RecordType(Vec<LabelDescId>),
    AbbrevType(Vec<TypId>, TypId),
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct ConstrDescId(pub u32);

#[derive(Clone, Debug)]
pub struct ConstrDesc {
    pub cs_res: TypId,
    pub cs_arg: TypId,
    pub cs_mut: Mutability,
    pub cs_tag: ConstrTag,
    pub cs_kind: ConstrKind,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ConstrKind {
    ConstrConstant,
    ConstrRegular,
    ConstrSuperfluous(i32),
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ConstrTag {
    ConstrExtensible(ConstrDescId),
    ConstrRegular(i32, i32),
}

#[derive(Default)]
pub struct ConstrDescArena {
    entries: Vec<Global<ConstrDesc>>,
    by_name: HashMap<String, ConstrDescId>,
}

impl ConstrDescArena {
    pub fn new() -> Self {
        ConstrDescArena {
            entries: Vec::new(),
            by_name: std::collections::HashMap::new(),
        }
    }

    pub fn alloc(&mut self, qualid: QualIdent, info: ConstrDesc) -> ConstrDescId {
        let id = ConstrDescId(self.entries.len() as u32);
        self.by_name.insert(qualid.id.clone(), id);
        self.entries.push(Global { qualid, info });
        id
    }

    pub fn find_by_name(&self, name: &str) -> Option<ConstrDescId> {
        self.by_name.get(name).copied()
    }

    pub fn get(&self, id: ConstrDescId) -> &Global<ConstrDesc> {
        &self.entries[id.0 as usize]
    }

    pub fn get_mut(&mut self, id: ConstrDescId) -> &mut Global<ConstrDesc> {
        &mut self.entries[id.0 as usize]
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct LabelDescId(pub u32);

#[derive(Clone, Debug)]
pub struct LabelDesc {
    pub lbl_res: TypId,
    pub lbl_arg: TypId,
    pub lbl_mut: Mutability,
    pub lbl_pos: i32,
}

#[derive(Default)]
pub struct LabelDescArena {
    entries: Vec<Global<LabelDesc>>,
    by_name: HashMap<String, LabelDescId>,
}

impl LabelDescArena {
    pub fn new() -> Self {
        LabelDescArena {
            entries: Vec::new(),
            by_name: std::collections::HashMap::new(),
        }
    }

    pub fn alloc(&mut self, qualid: QualIdent, info: LabelDesc) -> LabelDescId {
        let id = LabelDescId(self.entries.len() as u32);
        self.by_name.insert(qualid.id.clone(), id);
        self.entries.push(Global { qualid, info });
        id
    }

    pub fn find_by_name(&self, name: &str) -> Option<LabelDescId> {
        self.by_name.get(name).copied()
    }

    pub fn get(&self, id: LabelDescId) -> &Global<LabelDesc> {
        &self.entries[id.0 as usize]
    }

    pub fn get_mut(&mut self, id: LabelDescId) -> &mut Global<LabelDesc> {
        &mut self.entries[id.0 as usize]
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct ValueDescId(pub u32);

#[derive(Clone, Debug)]
pub struct ValueDesc {
    pub val_typ: TypId,
    pub val_prim: PrimDesc,
}

#[derive(Clone, Debug)]
pub enum PrimDesc {
    ValueNotPrim,
    ValuePrim(i32, String),
}

#[derive(Default)]
pub struct ValueDescArena {
    entries: Vec<Global<ValueDesc>>,
    by_name: HashMap<String, ValueDescId>,
}

impl ValueDescArena {
    pub fn new() -> Self {
        ValueDescArena {
            entries: Vec::new(),
            by_name: std::collections::HashMap::new(),
        }
    }

    pub fn alloc(&mut self, qualid: QualIdent, info: ValueDesc) -> ValueDescId {
        let id = ValueDescId(self.entries.len() as u32);
        self.by_name.insert(qualid.id.clone(), id);
        self.entries.push(Global { qualid, info });
        id
    }

    pub fn find_by_name(&self, name: &str) -> Option<ValueDescId> {
        self.by_name.get(name).copied()
    }

    pub fn get(&self, id: ValueDescId) -> &Global<ValueDesc> {
        &self.entries[id.0 as usize]
    }

    pub fn get_mut(&mut self, id: ValueDescId) -> &mut Global<ValueDesc> {
        &mut self.entries[id.0 as usize]
    }
}

#[derive(Default)]
pub struct GlobalTables {
    pub types: TypeArena,
    pub type_constrs: TypeConstrArena,
    pub constrs: ConstrDescArena,
    pub labels: LabelDescArena,
    pub values: ValueDescArena,
}

impl GlobalTables {
    pub fn new() -> Self {
        GlobalTables::default()
    }
}
