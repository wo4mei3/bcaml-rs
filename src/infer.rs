use std::collections::HashMap;

use crate::ast::*;
use crate::types::*;

#[derive(Debug, Clone, Copy)]
pub struct Unify;

#[derive(Debug, Clone, Copy)]
pub struct RecursiveAbbrev;

#[derive(Debug, Clone)]
pub enum TypeError {
    UnboundValue(String, Loc),

    UnboundConstr(String, Loc),

    UnboundLabel(String, Loc),

    UnboundTypeConstr(String, Loc),

    UnboundTypeVar(String, Loc),

    TypeArityErr {
        name: String,
        expected: i32,
        got: usize,
        loc: Loc,
    },

    NonLinearPattern(String, Loc),

    OrpatShouldBeClosed(Loc),

    PatWrongType(Loc),

    ExprWrongType(Loc),

    ApplicationOfNonFunction(Loc),

    IllShapedMatch(Loc),

    NotMutable(String, Loc),

    LabelMultiplyDefined(Loc),

    LabelUndefined(Loc),

    LabelNotBelong(Loc),

    LabelNotMutable(Loc),

    NonConstantConstr(Loc),

    ConstantConstr(Loc),

    RecursiveAbbrevErr(Loc),
    MalformedApp(Loc),
    BadFormatLetter(Loc, char),
}

pub struct Infer {
    pub current_level: i32,
}

impl Infer {
    pub fn new() -> Self {
        Infer { current_level: 0 }
    }

    pub fn reset_type_var(&mut self) {
        self.current_level = 0;
    }

    pub fn push_type_level(&mut self) {
        self.current_level += 1;
    }

    pub fn pop_type_level(&mut self) {
        self.current_level -= 1;
    }

    pub fn new_type_var(&self, arena: &mut TypeArena) -> TypId {
        arena.alloc(TypDesc::Tvar(TypLink::Tnolink), self.current_level)
    }

    pub fn new_type_var_list(&self, arena: &mut TypeArena, n: usize) -> Vec<TypId> {
        (0..n).map(|_| self.new_type_var(arena)).collect()
    }
}

pub fn new_global_type_var(arena: &mut TypeArena) -> TypId {
    arena.alloc(TypDesc::Tvar(TypLink::Tnolink), 1)
}

pub fn type_var_list(arena: &mut TypeArena, n: usize, level: i32) -> Vec<TypId> {
    (0..n)
        .map(|_| arena.alloc(TypDesc::Tvar(TypLink::Tnolink), level))
        .collect()
}

pub fn no_type(arena: &mut TypeArena) -> TypId {
    arena.alloc(TypDesc::Tproduct(Vec::new()), 0)
}

pub fn type_repr(arena: &mut TypeArena, ty: TypId) -> TypId {
    let link_target = match &arena.get(ty).desc {
        TypDesc::Tvar(TypLink::Tlinkto(t1)) => Some(*t1),
        _ => None,
    };
    match link_target {
        Some(t1) => {
            let t2 = type_repr(arena, t1);
            arena.set_desc(ty, TypDesc::Tvar(TypLink::Tlinkto(t2)));
            t2
        }
        None => ty,
    }
}

pub fn free_type_vars(arena: &mut TypeArena, level: i32, ty: TypId) -> Vec<TypId> {
    let mut fv = Vec::new();
    free_vars_rec(arena, level, ty, &mut fv);
    fv
}

fn free_vars_rec(arena: &mut TypeArena, level: i32, ty: TypId, fv: &mut Vec<TypId>) {
    let ty = type_repr(arena, ty);
    match arena.get(ty).desc.clone() {
        TypDesc::Tvar(_) => {
            if arena.get(ty).level >= level {
                fv.push(ty);
            }
        }
        TypDesc::Tarrow(t1, t2) => {
            free_vars_rec(arena, level, t1, fv);
            free_vars_rec(arena, level, t2, fv);
        }
        TypDesc::Tproduct(list) | TypDesc::Tconstr(_, list) => {
            for t in list {
                free_vars_rec(arena, level, t, fv);
            }
        }
    }
}

pub fn gen_type(infer: &Infer, arena: &mut TypeArena, ty: TypId) -> i32 {
    let ty = type_repr(arena, ty);
    let new_level = match arena.get(ty).desc.clone() {
        TypDesc::Tvar(_) => {
            let lvl = arena.get(ty).level;
            if lvl > infer.current_level {
                GENERIC
            } else {
                lvl
            }
        }
        TypDesc::Tarrow(t1, t2) => {
            let lvl1 = gen_type(infer, arena, t1);
            let lvl2 = gen_type(infer, arena, t2);
            lvl1.min(lvl2)
        }
        TypDesc::Tproduct(list) | TypDesc::Tconstr(_, list) => gen_type_list(infer, arena, &list),
    };
    arena.set_level(ty, new_level);
    new_level
}

fn gen_type_list(infer: &Infer, arena: &mut TypeArena, list: &[TypId]) -> i32 {
    let mut acc = NOTGENERIC;
    let mut first = true;
    for &ty in list {
        let lvl = gen_type(infer, arena, ty);
        acc = if first { lvl } else { acc.min(lvl) };
        first = false;
    }
    if list.is_empty() { NOTGENERIC } else { acc }
}

pub fn generalize_type(infer: &Infer, arena: &mut TypeArena, ty: TypId) {
    gen_type(infer, arena, ty);
}

pub fn nongen_type(infer: &Infer, arena: &mut TypeArena, ty: TypId) {
    let ty = type_repr(arena, ty);
    match arena.get(ty).desc.clone() {
        TypDesc::Tvar(_) => {
            if arena.get(ty).level > infer.current_level {
                arena.set_level(ty, infer.current_level);
            }
        }
        TypDesc::Tarrow(t1, t2) => {
            nongen_type(infer, arena, t1);
            nongen_type(infer, arena, t2);
        }
        TypDesc::Tproduct(list) | TypDesc::Tconstr(_, list) => {
            for t in list {
                nongen_type(infer, arena, t);
            }
        }
    }
}

pub fn copy_type(arena: &mut TypeArena, ty: TypId) -> TypId {
    let level = arena.get(ty).level;
    match arena.get(ty).desc.clone() {
        TypDesc::Tvar(TypLink::Tnolink) => {
            if level == GENERIC {
                let v = new_global_type_var(arena);
                arena.set_desc(ty, TypDesc::Tvar(TypLink::Tlinkto(v)));
                v
            } else {
                ty
            }
        }
        TypDesc::Tvar(TypLink::Tlinkto(inner)) => {
            if level == GENERIC {
                inner
            } else {
                copy_type(arena, inner)
            }
        }
        TypDesc::Tarrow(t1, t2) => {
            if level == GENERIC {
                let c1 = copy_type(arena, t1);
                let c2 = copy_type(arena, t2);
                arena.alloc(TypDesc::Tarrow(c1, c2), NOTGENERIC)
            } else {
                ty
            }
        }
        TypDesc::Tproduct(list) => {
            if level == GENERIC {
                let copied: Vec<TypId> = list.iter().map(|&t| copy_type(arena, t)).collect();
                arena.alloc(TypDesc::Tproduct(copied), NOTGENERIC)
            } else {
                ty
            }
        }
        TypDesc::Tconstr(cstr, list) => {
            if level == GENERIC {
                let copied: Vec<TypId> = list.iter().map(|&t| copy_type(arena, t)).collect();
                arena.alloc(TypDesc::Tconstr(cstr, copied), NOTGENERIC)
            } else {
                ty
            }
        }
    }
}

pub fn cleanup_type(arena: &mut TypeArena, ty: TypId) {
    let level = arena.get(ty).level;
    match arena.get(ty).desc.clone() {
        TypDesc::Tvar(TypLink::Tnolink) => {}
        TypDesc::Tvar(TypLink::Tlinkto(inner)) => {
            if level == GENERIC {
                arena.set_desc(ty, TypDesc::Tvar(TypLink::Tnolink));
            } else {
                cleanup_type(arena, inner);
            }
        }
        TypDesc::Tarrow(t1, t2) => {
            if level == GENERIC {
                cleanup_type(arena, t1);
                cleanup_type(arena, t2);
            }
        }
        TypDesc::Tproduct(list) | TypDesc::Tconstr(_, list) => {
            if level == GENERIC {
                for t in list {
                    cleanup_type(arena, t);
                }
            }
        }
    }
}

pub fn type_instance(arena: &mut TypeArena, ty: TypId) -> TypId {
    let ty2 = copy_type(arena, ty);
    cleanup_type(arena, ty);
    ty2
}

pub fn type_pair_instance(arena: &mut TypeArena, ty1: TypId, ty2: TypId) -> (TypId, TypId) {
    let c1 = copy_type(arena, ty1);
    let c2 = copy_type(arena, ty2);
    cleanup_type(arena, ty1);
    cleanup_type(arena, ty2);
    (c1, c2)
}

fn bind_variable(arena: &mut TypeArena, ty1: TypId, ty2: TypId) {
    match arena.get(ty1).desc.clone() {
        TypDesc::Tvar(TypLink::Tnolink) => {
            arena.set_desc(ty1, TypDesc::Tvar(TypLink::Tlinkto(ty2)));
        }
        _ => panic!("bind_variable: fatal_error"),
    }
}

pub fn expand_abbrev(
    arena: &mut TypeArena,
    params: &[TypId],
    body: TypId,
    args: &[TypId],
) -> TypId {
    let params2: Vec<TypId> = params.iter().map(|&p| copy_type(arena, p)).collect();
    let body2 = copy_type(arena, body);
    for &p in params {
        cleanup_type(arena, p);
    }
    cleanup_type(arena, body);
    for (&p2, &a) in params2.iter().zip(args.iter()) {
        bind_variable(arena, p2, a);
    }
    body2
}

pub fn occur_check(arena: &mut TypeArena, level0: i32, v: TypId, ty: TypId) -> bool {
    let ty = type_repr(arena, ty);
    match arena.get(ty).desc.clone() {
        TypDesc::Tvar(_) => {
            if arena.get(ty).level > level0 {
                arena.set_level(ty, level0);
            }
            ty == v
        }
        TypDesc::Tarrow(t1, t2) => {
            occur_check(arena, level0, v, t1) || occur_check(arena, level0, v, t2)
        }
        TypDesc::Tproduct(list) | TypDesc::Tconstr(_, list) => {
            list.iter().any(|&t| occur_check(arena, level0, v, t))
        }
    }
}

pub fn unify(
    arena: &mut TypeArena,
    constrs: &TypeConstrArena,
    ty1: TypId,
    ty2: TypId,
) -> Result<(), Unify> {
    if ty1 == ty2 {
        return Ok(());
    }
    let ty1 = type_repr(arena, ty1);
    let ty2 = type_repr(arena, ty2);
    if ty1 == ty2 {
        return Ok(());
    }
    let d1 = arena.get(ty1).desc.clone();
    let d2 = arena.get(ty2).desc.clone();
    match (d1, d2) {
        (TypDesc::Tvar(_), TypDesc::Tvar(_)) => {
            let l1 = arena.get(ty1).level;
            let l2 = arena.get(ty2).level;
            if l1 < l2 {
                arena.set_level(ty2, l1);
                arena.set_desc(ty2, TypDesc::Tvar(TypLink::Tlinkto(ty1)));
            } else {
                arena.set_level(ty1, l2);
                arena.set_desc(ty1, TypDesc::Tvar(TypLink::Tlinkto(ty2)));
            }
            Ok(())
        }
        (TypDesc::Tvar(_), _) if !occur_check(arena, arena.get(ty1).level, ty1, ty2) => {
            arena.set_desc(ty1, TypDesc::Tvar(TypLink::Tlinkto(ty2)));
            Ok(())
        }
        (_, TypDesc::Tvar(_)) if !occur_check(arena, arena.get(ty2).level, ty2, ty1) => {
            arena.set_desc(ty2, TypDesc::Tvar(TypLink::Tlinkto(ty1)));
            Ok(())
        }
        (TypDesc::Tarrow(a1, r1), TypDesc::Tarrow(a2, r2)) => {
            unify(arena, constrs, a1, a2)?;
            unify(arena, constrs, r1, r2)
        }
        (TypDesc::Tproduct(l1), TypDesc::Tproduct(l2)) => unify_list(arena, constrs, &l1, &l2),
        (TypDesc::Tconstr(c1, a1), TypDesc::Tconstr(c2, a2))
            if a1.is_empty() && a2.is_empty() && constrs.same_type_constr(c1, c2) =>
        {
            Ok(())
        }
        (TypDesc::Tconstr(c1, args), _) if is_abbrev(constrs, c1) => {
            let (params, body) = abbrev_of(constrs, c1);
            let expanded = expand_abbrev(arena, &params, body, &args);
            unify(arena, constrs, expanded, ty2)
        }
        (_, TypDesc::Tconstr(c2, args)) if is_abbrev(constrs, c2) => {
            let (params, body) = abbrev_of(constrs, c2);
            let expanded = expand_abbrev(arena, &params, body, &args);
            unify(arena, constrs, ty1, expanded)
        }
        (TypDesc::Tconstr(c1, l1), TypDesc::Tconstr(c2, l2))
            if constrs.same_type_constr(c1, c2) =>
        {
            unify_list(arena, constrs, &l1, &l2)
        }
        _ => Err(Unify),
    }
}

fn unify_list(
    arena: &mut TypeArena,
    constrs: &TypeConstrArena,
    l1: &[TypId],
    l2: &[TypId],
) -> Result<(), Unify> {
    if l1.len() != l2.len() {
        return Err(Unify);
    }
    for (&t1, &t2) in l1.iter().zip(l2.iter()) {
        unify(arena, constrs, t1, t2)?;
    }
    Ok(())
}

fn is_abbrev(constrs: &TypeConstrArena, c: TypeConstrId) -> bool {
    matches!(constrs.get(c).info.ty_abbr, TypeAbbrev::Tabbrev(_, _))
}

fn abbrev_of(constrs: &TypeConstrArena, c: TypeConstrId) -> (Vec<TypId>, TypId) {
    match &constrs.get(c).info.ty_abbr {
        TypeAbbrev::Tabbrev(params, body) => (params.clone(), *body),
        TypeAbbrev::Tnotabbrev => unreachable!(),
    }
}

pub fn filter_arrow(
    arena: &mut TypeArena,
    constrs: &TypeConstrArena,
    ty: TypId,
) -> Result<(TypId, TypId), Unify> {
    let ty = type_repr(arena, ty);
    match arena.get(ty).desc.clone() {
        TypDesc::Tvar(_) => {
            let level = arena.get(ty).level;
            let ty1 = arena.alloc(TypDesc::Tvar(TypLink::Tnolink), level);
            let ty2 = arena.alloc(TypDesc::Tvar(TypLink::Tnolink), level);
            let arrow = arena.alloc(TypDesc::Tarrow(ty1, ty2), NOTGENERIC);
            arena.set_desc(ty, TypDesc::Tvar(TypLink::Tlinkto(arrow)));
            Ok((ty1, ty2))
        }
        TypDesc::Tarrow(t1, t2) => Ok((t1, t2)),
        TypDesc::Tconstr(c, args) if is_abbrev(constrs, c) => {
            let (params, body) = abbrev_of(constrs, c);
            let expanded = expand_abbrev(arena, &params, body, &args);
            filter_arrow(arena, constrs, expanded)
        }
        _ => Err(Unify),
    }
}

pub fn filter_product(
    arena: &mut TypeArena,
    constrs: &TypeConstrArena,
    arity: usize,
    ty: TypId,
) -> Result<Vec<TypId>, Unify> {
    let ty = type_repr(arena, ty);
    match arena.get(ty).desc.clone() {
        TypDesc::Tvar(_) => {
            let level = arena.get(ty).level;
            let tyl = type_var_list(arena, arity, level);
            let prod = arena.alloc(TypDesc::Tproduct(tyl.clone()), NOTGENERIC);
            arena.set_desc(ty, TypDesc::Tvar(TypLink::Tlinkto(prod)));
            Ok(tyl)
        }
        TypDesc::Tproduct(tyl) => {
            if tyl.len() == arity {
                Ok(tyl)
            } else {
                Err(Unify)
            }
        }
        TypDesc::Tconstr(c, args) if is_abbrev(constrs, c) => {
            let (params, body) = abbrev_of(constrs, c);
            let expanded = expand_abbrev(arena, &params, body, &args);
            filter_product(arena, constrs, arity, expanded)
        }
        _ => Err(Unify),
    }
}

pub fn same_base_type(
    arena: &mut TypeArena,
    constrs: &TypeConstrArena,
    ty: TypId,
    base_ty: TypId,
) -> bool {
    let ty = type_repr(arena, ty);
    let base_ty = type_repr(arena, base_ty);
    match (arena.get(ty).desc.clone(), arena.get(base_ty).desc.clone()) {
        (TypDesc::Tconstr(c, args), _) if is_abbrev(constrs, c) => {
            let (params, body) = abbrev_of(constrs, c);
            let expanded = expand_abbrev(arena, &params, body, &args);
            same_base_type(arena, constrs, expanded, base_ty)
        }
        (_, TypDesc::Tconstr(c, args)) if is_abbrev(constrs, c) => {
            let (params, body) = abbrev_of(constrs, c);
            let expanded = expand_abbrev(arena, &params, body, &args);
            same_base_type(arena, constrs, ty, expanded)
        }
        (TypDesc::Tconstr(c1, a1), TypDesc::Tconstr(c2, a2)) if a1.is_empty() && a2.is_empty() => {
            constrs.same_type_constr(c1, c2)
        }
        _ => false,
    }
}

pub fn check_recursive_abbrev(
    arena: &mut TypeArena,
    constrs: &TypeConstrArena,
    cstr: TypeConstrId,
) -> Result<(), RecursiveAbbrev> {
    let (_, body) = match &constrs.get(cstr).info.ty_abbr {
        TypeAbbrev::Tnotabbrev => return Ok(()),
        TypeAbbrev::Tabbrev(params, body) => (params.clone(), *body),
    };
    let mut seen = vec![cstr];
    check_abbrev_rec(arena, constrs, &mut seen, body)
}

fn check_abbrev_rec(
    arena: &mut TypeArena,
    constrs: &TypeConstrArena,
    seen: &mut Vec<TypeConstrId>,
    ty: TypId,
) -> Result<(), RecursiveAbbrev> {
    let ty = type_repr(arena, ty);
    match arena.get(ty).desc.clone() {
        TypDesc::Tvar(_) => Ok(()),
        TypDesc::Tarrow(t1, t2) => {
            check_abbrev_rec(arena, constrs, seen, t1)?;
            check_abbrev_rec(arena, constrs, seen, t2)
        }
        TypDesc::Tproduct(list) => {
            for t in list {
                check_abbrev_rec(arena, constrs, seen, t)?;
            }
            Ok(())
        }
        TypDesc::Tconstr(c, list) => {
            if seen.contains(&c) {
                return Err(RecursiveAbbrev);
            }
            for t in &list {
                check_abbrev_rec(arena, constrs, seen, *t)?;
            }
            if let TypeAbbrev::Tabbrev(_, body) = &constrs.get(c).info.ty_abbr {
                let body = *body;
                seen.push(c);
                check_abbrev_rec(arena, constrs, seen, body)?;
                seen.pop();
            }
            Ok(())
        }
    }
}

pub struct Builtins {
    pub int: TypeConstrId,
    pub float: TypeConstrId,
    pub char: TypeConstrId,
    pub string: TypeConstrId,
    pub bool: TypeConstrId,
    pub unit: TypeConstrId,
    pub exn: TypeConstrId,
    pub vect: TypeConstrId,
    pub list: TypeConstrId,
    pub format: TypeConstrId,
    pub in_channel: TypeConstrId,
    pub out_channel: TypeConstrId,
    pub ref_constr: TypeConstrId,
    pub ty_int: TypId,
    pub ty_float: TypId,
    pub ty_char: TypId,
    pub ty_string: TypId,
    pub ty_bool: TypId,
    pub ty_unit: TypId,
    pub ty_out_channel: TypId,
}

fn base_type_constr(tables: &mut GlobalTables, name: &str) -> (TypeConstrId, TypId) {
    let cstr_id = tables.type_constrs.alloc(
        QualIdent {
            qual: String::new(),
            id: name.to_string(),
        },
        TypeInfo {
            ty_abbr: TypeAbbrev::Tnotabbrev,
            ty_arity: 0,
            ty_desc: TypeComponents::AbstractType,
        },
    );
    let ty = tables
        .types
        .alloc(TypDesc::Tconstr(cstr_id, Vec::new()), NOTGENERIC);
    (cstr_id, ty)
}

pub fn install_builtins(tables: &mut GlobalTables) -> Builtins {
    let (int, ty_int) = base_type_constr(tables, "int");
    let (float, ty_float) = base_type_constr(tables, "float");
    let (char, ty_char) = base_type_constr(tables, "char");
    let (string, ty_string) = base_type_constr(tables, "string");
    let (bool, ty_bool) = base_type_constr(tables, "bool");
    let (unit, ty_unit) = base_type_constr(tables, "unit");
    let (exn, _ty_exn) = base_type_constr(tables, "exn");

    let format = tables.type_constrs.alloc(
        QualIdent {
            qual: String::new(),
            id: "format".to_string(),
        },
        TypeInfo {
            ty_abbr: TypeAbbrev::Tnotabbrev,
            ty_arity: 3,
            ty_desc: TypeComponents::AbstractType,
        },
    );

    let (in_channel, _ty_in_channel) = base_type_constr(tables, "in_channel");
    let (out_channel, ty_out_channel) = base_type_constr(tables, "out_channel");
    {
        let ty_exn = tables
            .types
            .alloc(TypDesc::Tconstr(exn, Vec::new()), NOTGENERIC);
        let id = tables.constrs.alloc(
            QualIdent {
                qual: String::new(),
                id: "End_of_file".to_string(),
            },
            ConstrDesc {
                cs_res: ty_exn,
                cs_arg: no_type(&mut tables.types),
                cs_mut: Mutability::Notmutable,
                cs_tag: ConstrTag::ConstrRegular(0, 0),
                cs_kind: ConstrKind::ConstrConstant,
            },
        );
        tables.constrs.get_mut(id).info.cs_tag = ConstrTag::ConstrExtensible(id);
    }

    let ref_constr = tables.type_constrs.alloc(
        QualIdent {
            qual: String::new(),
            id: "ref".to_string(),
        },
        TypeInfo {
            ty_abbr: TypeAbbrev::Tnotabbrev,
            ty_arity: 1,
            ty_desc: TypeComponents::AbstractType,
        },
    );
    {
        let ref_var = tables.types.alloc(TypDesc::Tvar(TypLink::Tnolink), GENERIC);
        let ty_ref_of_var = tables
            .types
            .alloc(TypDesc::Tconstr(ref_constr, vec![ref_var]), GENERIC);
        let ref_ctor_id = tables.constrs.alloc(
            QualIdent {
                qual: String::new(),
                id: "ref".to_string(),
            },
            ConstrDesc {
                cs_res: ty_ref_of_var,
                cs_arg: ref_var,
                cs_mut: Mutability::Mutable,
                cs_tag: ConstrTag::ConstrRegular(0, 1),
                cs_kind: ConstrKind::ConstrRegular,
            },
        );
        tables.type_constrs.get_mut(ref_constr).info.ty_desc =
            TypeComponents::VariantType(vec![ref_ctor_id]);
    }

    let vect = tables.type_constrs.alloc(
        QualIdent {
            qual: String::new(),
            id: "vect".to_string(),
        },
        TypeInfo {
            ty_abbr: TypeAbbrev::Tnotabbrev,
            ty_arity: 1,
            ty_desc: TypeComponents::AbstractType,
        },
    );

    let list = tables.type_constrs.alloc(
        QualIdent {
            qual: String::new(),
            id: "list".to_string(),
        },
        TypeInfo {
            ty_abbr: TypeAbbrev::Tnotabbrev,
            ty_arity: 1,
            ty_desc: TypeComponents::AbstractType,
        },
    );
    let list_var = tables.types.alloc(TypDesc::Tvar(TypLink::Tnolink), GENERIC);
    let ty_list_of_var = tables
        .types
        .alloc(TypDesc::Tconstr(list, vec![list_var]), GENERIC);
    let nil_id = tables.constrs.alloc(
        QualIdent {
            qual: String::new(),
            id: CONSTR_NIL.to_string(),
        },
        ConstrDesc {
            cs_res: ty_list_of_var,
            cs_arg: no_type(&mut tables.types),
            cs_mut: Mutability::Notmutable,
            cs_tag: ConstrTag::ConstrRegular(0, 2),
            cs_kind: ConstrKind::ConstrConstant,
        },
    );
    let cons_arg = {
        let head = list_var;
        tables
            .types
            .alloc(TypDesc::Tproduct(vec![head, ty_list_of_var]), GENERIC)
    };
    let cons_id = tables.constrs.alloc(
        QualIdent {
            qual: String::new(),
            id: CONSTR_CONS.to_string(),
        },
        ConstrDesc {
            cs_res: ty_list_of_var,
            cs_arg: cons_arg,
            cs_mut: Mutability::Notmutable,
            cs_tag: ConstrTag::ConstrRegular(1, 2),
            cs_kind: ConstrKind::ConstrRegular,
        },
    );
    tables.type_constrs.get_mut(list).info.ty_desc =
        TypeComponents::VariantType(vec![nil_id, cons_id]);

    let bool_true = tables.constrs.alloc(
        QualIdent {
            qual: String::new(),
            id: "true".to_string(),
        },
        ConstrDesc {
            cs_res: ty_bool,
            cs_arg: no_type(&mut tables.types),
            cs_mut: Mutability::Notmutable,
            cs_tag: ConstrTag::ConstrRegular(1, 2),
            cs_kind: ConstrKind::ConstrConstant,
        },
    );
    let bool_false = tables.constrs.alloc(
        QualIdent {
            qual: String::new(),
            id: "false".to_string(),
        },
        ConstrDesc {
            cs_res: ty_bool,
            cs_arg: no_type(&mut tables.types),
            cs_mut: Mutability::Notmutable,
            cs_tag: ConstrTag::ConstrRegular(0, 2),
            cs_kind: ConstrKind::ConstrConstant,
        },
    );
    let _ = (bool_true, bool_false);

    tables.constrs.alloc(
        QualIdent {
            qual: String::new(),
            id: CONSTR_VOID.to_string(),
        },
        ConstrDesc {
            cs_res: ty_unit,
            cs_arg: no_type(&mut tables.types),
            cs_mut: Mutability::Notmutable,
            cs_tag: ConstrTag::ConstrRegular(0, 1),
            cs_kind: ConstrKind::ConstrConstant,
        },
    );

    Builtins {
        int,
        float,
        char,
        string,
        bool,
        unit,
        exn,
        vect,
        list,
        format,
        in_channel,
        out_channel,
        ref_constr,
        ty_int,
        ty_float,
        ty_char,
        ty_string,
        ty_bool,
        ty_unit,
        ty_out_channel,
    }
}

#[derive(Clone)]
enum TB {
    Int,
    Float,
    Char,
    String,
    Bool,
    Unit,
    Exn,
    InChannel,
    OutChannel,

    Format(Box<TB>, Box<TB>, Box<TB>),

    Ref(Box<TB>),
    Var(&'static str),
    Arrow(Box<TB>, Box<TB>),
    Tuple(Vec<TB>),
    List(Box<TB>),
    Vect(Box<TB>),
}

fn arr(a: TB, b: TB) -> TB {
    TB::Arrow(Box::new(a), Box::new(b))
}

fn arrn(args: Vec<TB>, ret: TB) -> TB {
    let mut result = ret;
    for a in args.into_iter().rev() {
        result = arr(a, result);
    }
    result
}

fn v(name: &'static str) -> TB {
    TB::Var(name)
}
fn lst(t: TB) -> TB {
    TB::List(Box::new(t))
}
fn vct(t: TB) -> TB {
    TB::Vect(Box::new(t))
}
fn tup(ts: Vec<TB>) -> TB {
    TB::Tuple(ts)
}

fn build_tb(
    tables: &mut GlobalTables,
    b: &Builtins,
    vars: &mut HashMap<&'static str, TypId>,
    tb: &TB,
) -> TypId {
    match tb {
        TB::Int => b.ty_int,
        TB::Float => b.ty_float,
        TB::Char => b.ty_char,
        TB::String => b.ty_string,
        TB::Bool => b.ty_bool,
        TB::Unit => b.ty_unit,
        TB::Exn => tables
            .types
            .alloc(TypDesc::Tconstr(b.exn, Vec::new()), NOTGENERIC),
        TB::InChannel => tables
            .types
            .alloc(TypDesc::Tconstr(b.in_channel, Vec::new()), NOTGENERIC),
        TB::OutChannel => b.ty_out_channel,
        TB::Format(a, i, r) => {
            let ta = build_tb(tables, b, vars, a);
            let ti = build_tb(tables, b, vars, i);
            let tr = build_tb(tables, b, vars, r);
            tables
                .types
                .alloc(TypDesc::Tconstr(b.format, vec![ta, ti, tr]), NOTGENERIC)
        }
        TB::Ref(t) => {
            let tt = build_tb(tables, b, vars, t);
            tables
                .types
                .alloc(TypDesc::Tconstr(b.ref_constr, vec![tt]), NOTGENERIC)
        }
        TB::Var(name) => *vars
            .entry(name)
            .or_insert_with(|| new_global_type_var(&mut tables.types)),
        TB::Arrow(a, r) => {
            let ta = build_tb(tables, b, vars, a);
            let tr = build_tb(tables, b, vars, r);
            type_arrow(&mut tables.types, ta, tr)
        }
        TB::Tuple(ts) => {
            let tts: Vec<TypId> = ts.iter().map(|t| build_tb(tables, b, vars, t)).collect();
            type_product(&mut tables.types, tts)
        }
        TB::List(t) => {
            let tt = build_tb(tables, b, vars, t);
            tables
                .types
                .alloc(TypDesc::Tconstr(b.list, vec![tt]), NOTGENERIC)
        }
        TB::Vect(t) => {
            let tt = build_tb(tables, b, vars, t);
            tables
                .types
                .alloc(TypDesc::Tconstr(b.vect, vec![tt]), NOTGENERIC)
        }
    }
}

fn reg(tables: &mut GlobalTables, b: &Builtins, name: &str, tb: TB) {
    let mut vars = HashMap::new();
    let ty = build_tb(tables, b, &mut vars, &tb);
    if !vars.is_empty() {
        let infer0 = Infer::new();
        generalize_type(&infer0, &mut tables.types, ty);
    }
    tables.values.alloc(
        QualIdent {
            qual: String::new(),
            id: name.to_string(),
        },
        ValueDesc {
            val_typ: ty,
            val_prim: PrimDesc::ValueNotPrim,
        },
    );
}

fn reg_exn0(tables: &mut GlobalTables, ty_exn: TypId, name: &str) {
    let id = tables.constrs.alloc(
        QualIdent {
            qual: String::new(),
            id: name.to_string(),
        },
        ConstrDesc {
            cs_res: ty_exn,
            cs_arg: no_type(&mut tables.types),
            cs_mut: Mutability::Notmutable,
            cs_tag: ConstrTag::ConstrRegular(0, 0),
            cs_kind: ConstrKind::ConstrConstant,
        },
    );
    tables.constrs.get_mut(id).info.cs_tag = ConstrTag::ConstrExtensible(id);
}

fn reg_exn1(tables: &mut GlobalTables, b: &Builtins, ty_exn: TypId, name: &str, arg: TB) {
    let mut vars = HashMap::new();
    let arg_ty = build_tb(tables, b, &mut vars, &arg);
    let id = tables.constrs.alloc(
        QualIdent {
            qual: String::new(),
            id: name.to_string(),
        },
        ConstrDesc {
            cs_res: ty_exn,
            cs_arg: arg_ty,
            cs_mut: Mutability::Notmutable,
            cs_tag: ConstrTag::ConstrRegular(0, 0),
            cs_kind: ConstrKind::ConstrRegular,
        },
    );
    tables.constrs.get_mut(id).info.cs_tag = ConstrTag::ConstrExtensible(id);
}

pub fn type_format(
    infer: &Infer,
    tables: &mut GlobalTables,
    b: &Builtins,
    loc: Loc,
    fmt: &str,
) -> Result<TypId, TypeError> {
    let chars: Vec<char> = fmt.chars().collect();
    let ty_input = infer.new_type_var(&mut tables.types);
    let ty_result = infer.new_type_var(&mut tables.types);

    fn skip_args(chars: &[char], mut j: usize) -> usize {
        while j < chars.len() {
            match chars[j] {
                '0'..='9' | ' ' | '.' | '-' => j += 1,
                _ => break,
            }
        }
        j
    }

    fn scan_format(
        infer: &Infer,
        tables: &mut GlobalTables,
        b: &Builtins,
        chars: &[char],
        i: usize,
        ty_input: TypId,
        ty_result: TypId,
        loc: Loc,
    ) -> Result<TypId, TypeError> {
        if i >= chars.len() {
            return Ok(ty_result);
        }
        if chars[i] != '%' {
            return scan_format(infer, tables, b, chars, i + 1, ty_input, ty_result, loc);
        }
        let j = skip_args(chars, i + 1);
        if j >= chars.len() {
            return Err(TypeError::BadFormatLetter(loc, '%'));
        }
        let conv = chars[j];
        match conv {
            '%' => scan_format(infer, tables, b, chars, j + 1, ty_input, ty_result, loc),
            's' => {
                let rest = scan_format(infer, tables, b, chars, j + 1, ty_input, ty_result, loc)?;
                Ok(type_arrow(&mut tables.types, b.ty_string, rest))
            }
            'c' => {
                let rest = scan_format(infer, tables, b, chars, j + 1, ty_input, ty_result, loc)?;
                Ok(type_arrow(&mut tables.types, b.ty_char, rest))
            }
            'd' | 'o' | 'x' | 'X' | 'u' => {
                let rest = scan_format(infer, tables, b, chars, j + 1, ty_input, ty_result, loc)?;
                Ok(type_arrow(&mut tables.types, b.ty_int, rest))
            }
            'f' | 'e' | 'E' | 'g' | 'G' => {
                let rest = scan_format(infer, tables, b, chars, j + 1, ty_input, ty_result, loc)?;
                Ok(type_arrow(&mut tables.types, b.ty_float, rest))
            }
            'b' => {
                let rest = scan_format(infer, tables, b, chars, j + 1, ty_input, ty_result, loc)?;
                Ok(type_arrow(&mut tables.types, b.ty_bool, rest))
            }
            'a' => {
                let ty_arg = infer.new_type_var(&mut tables.types);
                let rest = scan_format(infer, tables, b, chars, j + 1, ty_input, ty_result, loc)?;
                let inner = type_arrow(&mut tables.types, ty_arg, ty_result);
                let printer = type_arrow(&mut tables.types, ty_input, inner);
                let after_arg = type_arrow(&mut tables.types, ty_arg, rest);
                Ok(type_arrow(&mut tables.types, printer, after_arg))
            }
            't' => {
                let rest = scan_format(infer, tables, b, chars, j + 1, ty_input, ty_result, loc)?;
                let printer = type_arrow(&mut tables.types, ty_input, ty_result);
                Ok(type_arrow(&mut tables.types, printer, rest))
            }
            c => Err(TypeError::BadFormatLetter(loc, c)),
        }
    }

    let scanned = scan_format(infer, tables, b, &chars, 0, ty_input, ty_result, loc)?;
    Ok(tables.types.alloc(
        TypDesc::Tconstr(b.format, vec![scanned, ty_input, ty_result]),
        NOTGENERIC,
    ))
}

pub fn install_prims(tables: &mut GlobalTables, b: &Builtins) {
    reg(tables, b, "raise", arr(TB::Exn, v("a")));
    reg(tables, b, "failwith", arr(TB::String, v("a")));
    reg(tables, b, "invalid_arg", arr(TB::String, v("a")));
    {
        let ty_exn = tables
            .types
            .alloc(TypDesc::Tconstr(b.exn, Vec::new()), NOTGENERIC);
        reg_exn0(tables, ty_exn, "Out_of_memory");
        reg_exn1(tables, b, ty_exn, "Invalid_argument", TB::String);
        reg_exn1(tables, b, ty_exn, "Failure", TB::String);
        reg_exn0(tables, ty_exn, "Not_found");
        reg_exn0(tables, ty_exn, "Exit");
    }

    for name in ["&", "&&", "or", "||"] {
        reg(tables, b, name, arrn(vec![TB::Bool, TB::Bool], TB::Bool));
    }
    reg(tables, b, "not", arr(TB::Bool, TB::Bool));
    reg(tables, b, "string_of_bool", arr(TB::Bool, TB::String));
    reg(tables, b, "bool_of_string", arr(TB::String, TB::Bool));

    for name in ["=", "<>", "<", "<=", ">", ">=", "==", "!="] {
        reg(tables, b, name, arrn(vec![v("a"), v("a")], TB::Bool));
    }
    reg(tables, b, "compare", arrn(vec![v("a"), v("a")], TB::Int));
    reg(tables, b, "min", arrn(vec![v("a"), v("a")], v("a")));
    reg(tables, b, "max", arrn(vec![v("a"), v("a")], v("a")));

    reg(tables, b, "minus", arr(TB::Int, TB::Int));
    reg(tables, b, "minus_int", arr(TB::Int, TB::Int));
    reg(tables, b, "succ", arr(TB::Int, TB::Int));
    reg(tables, b, "pred", arr(TB::Int, TB::Int));
    for name in ["+", "add_int"] {
        reg(tables, b, name, arrn(vec![TB::Int, TB::Int], TB::Int));
    }
    for name in ["-", "sub_int"] {
        reg(tables, b, name, arrn(vec![TB::Int, TB::Int], TB::Int));
    }
    for name in ["*", "mult_int"] {
        reg(tables, b, name, arrn(vec![TB::Int, TB::Int], TB::Int));
    }
    for name in ["/", "div_int", "quo"] {
        reg(tables, b, name, arrn(vec![TB::Int, TB::Int], TB::Int));
    }
    reg(tables, b, "mod", arrn(vec![TB::Int, TB::Int], TB::Int));
    for name in ["eq_int", "neq_int", "lt_int", "gt_int", "le_int", "ge_int"] {
        reg(tables, b, name, arrn(vec![TB::Int, TB::Int], TB::Bool));
    }
    reg(tables, b, "abs", arr(TB::Int, TB::Int));
    reg(tables, b, "max_int", TB::Int);
    reg(tables, b, "min_int", TB::Int);
    for name in [
        "land",
        "lor",
        "lxor",
        "lsl",
        "lshift_left",
        "lsr",
        "asr",
        "lshift_right",
    ] {
        reg(tables, b, name, arrn(vec![TB::Int, TB::Int], TB::Int));
    }
    reg(tables, b, "lnot", arr(TB::Int, TB::Int));
    reg(tables, b, "string_of_int", arr(TB::Int, TB::String));
    reg(tables, b, "int_of_string", arr(TB::String, TB::Int));
    reg(
        tables,
        b,
        "format_int",
        arrn(vec![TB::String, TB::Int], TB::String),
    );

    reg(tables, b, "int_of_float", arr(TB::Float, TB::Int));
    reg(tables, b, "float_of_int", arr(TB::Int, TB::Float));
    reg(tables, b, "minus_float", arr(TB::Float, TB::Float));
    for name in ["+.", "add_float"] {
        reg(tables, b, name, arrn(vec![TB::Float, TB::Float], TB::Float));
    }
    for name in ["-.", "sub_float"] {
        reg(tables, b, name, arrn(vec![TB::Float, TB::Float], TB::Float));
    }
    for name in ["*.", "mult_float"] {
        reg(tables, b, name, arrn(vec![TB::Float, TB::Float], TB::Float));
    }
    for name in ["/.", "div_float"] {
        reg(tables, b, name, arrn(vec![TB::Float, TB::Float], TB::Float));
    }
    for name in ["**", "**.", "power"] {
        reg(tables, b, name, arrn(vec![TB::Float, TB::Float], TB::Float));
    }
    for name in ["eq_float", "=."] {
        reg(tables, b, name, arrn(vec![TB::Float, TB::Float], TB::Bool));
    }
    for name in ["neq_float", "<>."] {
        reg(tables, b, name, arrn(vec![TB::Float, TB::Float], TB::Bool));
    }
    for name in ["<.", "lt_float"] {
        reg(tables, b, name, arrn(vec![TB::Float, TB::Float], TB::Bool));
    }
    for name in [">.", "gt_float"] {
        reg(tables, b, name, arrn(vec![TB::Float, TB::Float], TB::Bool));
    }
    for name in ["<=.", "le_float"] {
        reg(tables, b, name, arrn(vec![TB::Float, TB::Float], TB::Bool));
    }
    for name in [">=.", "ge_float"] {
        reg(tables, b, name, arrn(vec![TB::Float, TB::Float], TB::Bool));
    }
    for name in [
        "acos", "asin", "atan", "cos", "cosh", "exp", "log", "log10", "sin", "sinh", "sqrt", "tan",
        "tanh",
    ] {
        reg(tables, b, name, arr(TB::Float, TB::Float));
    }
    reg(
        tables,
        b,
        "atan2",
        arrn(vec![TB::Float, TB::Float], TB::Float),
    );
    reg(tables, b, "ceil", arr(TB::Float, TB::Float));
    reg(tables, b, "floor", arr(TB::Float, TB::Float));
    reg(tables, b, "abs_float", arr(TB::Float, TB::Float));
    reg(
        tables,
        b,
        "mod_float",
        arrn(vec![TB::Float, TB::Float], TB::Float),
    );
    reg(
        tables,
        b,
        "frexp",
        arr(TB::Float, tup(vec![TB::Float, TB::Int])),
    );
    reg(
        tables,
        b,
        "ldexp",
        arrn(vec![TB::Float, TB::Int], TB::Float),
    );
    reg(
        tables,
        b,
        "modf",
        arr(TB::Float, tup(vec![TB::Float, TB::Float])),
    );
    reg(tables, b, "string_of_float", arr(TB::Float, TB::String));
    reg(tables, b, "float_of_string", arr(TB::String, TB::Float));
    reg(
        tables,
        b,
        "format_float",
        arrn(vec![TB::String, TB::Float], TB::String),
    );

    reg(tables, b, "int_of_char", arr(TB::Char, TB::Int));
    reg(tables, b, "char_of_int", arr(TB::Int, TB::Char));
    reg(tables, b, "string_of_char", arr(TB::Char, TB::String));
    reg(tables, b, "char_for_read", arr(TB::Char, TB::String));
    reg(tables, b, "is_printable", arr(TB::Char, TB::Bool));

    reg(tables, b, "string_length", arr(TB::String, TB::Int));
    reg(
        tables,
        b,
        "nth_char",
        arrn(vec![TB::String, TB::Int], TB::Char),
    );
    reg(
        tables,
        b,
        "set_nth_char",
        arrn(vec![TB::String, TB::Int, TB::Char], TB::Unit),
    );
    reg(
        tables,
        b,
        "^",
        arrn(vec![TB::String, TB::String], TB::String),
    );
    reg(tables, b, "concat", arr(lst(TB::String), TB::String));
    reg(
        tables,
        b,
        "sub_string",
        arrn(vec![TB::String, TB::Int, TB::Int], TB::String),
    );
    reg(tables, b, "create_string", arr(TB::Int, TB::String));
    reg(
        tables,
        b,
        "make_string",
        arrn(vec![TB::Int, TB::Char], TB::String),
    );
    reg(
        tables,
        b,
        "fill_string",
        arrn(vec![TB::String, TB::Int, TB::Int, TB::Char], TB::Unit),
    );
    reg(
        tables,
        b,
        "blit_string",
        arrn(
            vec![TB::String, TB::Int, TB::String, TB::Int, TB::Int],
            TB::Unit,
        ),
    );
    reg(
        tables,
        b,
        "replace_string",
        arrn(vec![TB::String, TB::String, TB::Int], TB::Unit),
    );
    for name in [
        "eq_string",
        "neq_string",
        "le_string",
        "lt_string",
        "ge_string",
        "gt_string",
    ] {
        reg(
            tables,
            b,
            name,
            arrn(vec![TB::String, TB::String], TB::Bool),
        );
    }
    reg(
        tables,
        b,
        "compare_strings",
        arrn(vec![TB::String, TB::String], TB::Int),
    );
    reg(tables, b, "string_for_read", arr(TB::String, TB::String));
    reg(
        tables,
        b,
        "index_char",
        arrn(vec![TB::String, TB::Char], TB::Int),
    );
    reg(
        tables,
        b,
        "rindex_char",
        arrn(vec![TB::String, TB::Char], TB::Int),
    );
    reg(
        tables,
        b,
        "index_char_from",
        arrn(vec![TB::String, TB::Int, TB::Char], TB::Int),
    );
    reg(
        tables,
        b,
        "rindex_char_from",
        arrn(vec![TB::String, TB::Int, TB::Char], TB::Int),
    );

    reg(tables, b, "vect_length", arr(vct(v("a")), TB::Int));
    reg(
        tables,
        b,
        "vect_item",
        arrn(vec![vct(v("a")), TB::Int], v("a")),
    );
    reg(
        tables,
        b,
        "vect_assign",
        arrn(vec![vct(v("a")), TB::Int, v("a")], TB::Unit),
    );
    reg(
        tables,
        b,
        "make_vect",
        arrn(vec![TB::Int, v("a")], vct(v("a"))),
    );
    reg(
        tables,
        b,
        "make_matrix",
        arrn(vec![TB::Int, TB::Int, v("a")], vct(vct(v("a")))),
    );
    reg(
        tables,
        b,
        "init_vect",
        arrn(vec![TB::Int, arr(TB::Int, v("a"))], vct(v("a"))),
    );
    reg(
        tables,
        b,
        "concat_vect",
        arrn(vec![vct(v("a")), vct(v("a"))], vct(v("a"))),
    );
    reg(
        tables,
        b,
        "sub_vect",
        arrn(vec![vct(v("a")), TB::Int, TB::Int], vct(v("a"))),
    );
    reg(tables, b, "copy_vect", arr(vct(v("a")), vct(v("a"))));
    reg(
        tables,
        b,
        "fill_vect",
        arrn(vec![vct(v("a")), TB::Int, TB::Int, v("a")], TB::Unit),
    );
    reg(
        tables,
        b,
        "blit_vect",
        arrn(
            vec![vct(v("a")), TB::Int, vct(v("a")), TB::Int, TB::Int],
            TB::Unit,
        ),
    );
    reg(tables, b, "list_of_vect", arr(vct(v("a")), lst(v("a"))));
    reg(tables, b, "vect_of_list", arr(lst(v("a")), vct(v("a"))));
    reg(
        tables,
        b,
        "map_vect",
        arrn(vec![arr(v("a"), v("b")), vct(v("a"))], vct(v("b"))),
    );
    reg(
        tables,
        b,
        "map_vect_list",
        arrn(vec![arr(v("a"), v("b")), vct(v("a"))], lst(v("b"))),
    );
    reg(
        tables,
        b,
        "do_vect",
        arrn(vec![arr(v("a"), TB::Unit), vct(v("a"))], TB::Unit),
    );

    reg(tables, b, "fst", arr(tup(vec![v("a"), v("b")]), v("a")));
    reg(tables, b, "snd", arr(tup(vec![v("a"), v("b")]), v("b")));
    reg(
        tables,
        b,
        "split",
        arr(
            lst(tup(vec![v("a"), v("b")])),
            tup(vec![lst(v("a")), lst(v("b"))]),
        ),
    );
    reg(
        tables,
        b,
        "combine",
        arr(
            tup(vec![lst(v("a")), lst(v("b"))]),
            lst(tup(vec![v("a"), v("b")])),
        ),
    );
    reg(
        tables,
        b,
        "map_combine",
        arrn(
            vec![
                arr(tup(vec![v("a"), v("b")]), v("c")),
                tup(vec![lst(v("a")), lst(v("b"))]),
            ],
            lst(v("c")),
        ),
    );
    reg(
        tables,
        b,
        "do_list_combine",
        arrn(
            vec![
                arr(tup(vec![v("a"), v("b")]), TB::Unit),
                tup(vec![lst(v("a")), lst(v("b"))]),
            ],
            TB::Unit,
        ),
    );

    reg(tables, b, "list_length", arr(lst(v("a")), TB::Int));
    reg(
        tables,
        b,
        "@",
        arrn(vec![lst(v("a")), lst(v("a"))], lst(v("a"))),
    );
    reg(tables, b, "hd", arr(lst(v("a")), v("a")));
    reg(tables, b, "tl", arr(lst(v("a")), lst(v("a"))));
    reg(tables, b, "rev", arr(lst(v("a")), lst(v("a"))));
    reg(
        tables,
        b,
        "map",
        arrn(vec![arr(v("a"), v("b")), lst(v("a"))], lst(v("b"))),
    );
    reg(
        tables,
        b,
        "do_list",
        arrn(vec![arr(v("a"), TB::Unit), lst(v("a"))], TB::Unit),
    );
    reg(
        tables,
        b,
        "it_list",
        arrn(
            vec![arrn(vec![v("a"), v("b")], v("a")), v("a"), lst(v("b"))],
            v("a"),
        ),
    );
    reg(
        tables,
        b,
        "list_it",
        arrn(
            vec![arrn(vec![v("a"), v("b")], v("b")), lst(v("a")), v("b")],
            v("b"),
        ),
    );
    reg(
        tables,
        b,
        "map2",
        arrn(
            vec![arrn(vec![v("a"), v("b")], v("c")), lst(v("a")), lst(v("b"))],
            lst(v("c")),
        ),
    );
    reg(
        tables,
        b,
        "do_list2",
        arrn(
            vec![
                arrn(vec![v("a"), v("b")], TB::Unit),
                lst(v("a")),
                lst(v("b")),
            ],
            TB::Unit,
        ),
    );
    reg(
        tables,
        b,
        "it_list2",
        arrn(
            vec![
                arrn(vec![v("a"), v("b"), v("c")], v("a")),
                v("a"),
                lst(v("b")),
                lst(v("c")),
            ],
            v("a"),
        ),
    );
    reg(
        tables,
        b,
        "list_it2",
        arrn(
            vec![
                arrn(vec![v("a"), v("b"), v("c")], v("c")),
                lst(v("a")),
                lst(v("b")),
                v("c"),
            ],
            v("c"),
        ),
    );
    reg(
        tables,
        b,
        "flat_map",
        arrn(vec![arr(v("a"), lst(v("b"))), lst(v("a"))], lst(v("b"))),
    );
    reg(
        tables,
        b,
        "for_all",
        arrn(vec![arr(v("a"), TB::Bool), lst(v("a"))], TB::Bool),
    );
    reg(
        tables,
        b,
        "exists",
        arrn(vec![arr(v("a"), TB::Bool), lst(v("a"))], TB::Bool),
    );
    reg(tables, b, "mem", arrn(vec![v("a"), lst(v("a"))], TB::Bool));
    reg(tables, b, "memq", arrn(vec![v("a"), lst(v("a"))], TB::Bool));
    reg(
        tables,
        b,
        "except",
        arrn(vec![v("a"), lst(v("a"))], lst(v("a"))),
    );
    reg(
        tables,
        b,
        "exceptq",
        arrn(vec![v("a"), lst(v("a"))], lst(v("a"))),
    );
    reg(
        tables,
        b,
        "subtract",
        arrn(vec![lst(v("a")), lst(v("a"))], lst(v("a"))),
    );
    reg(
        tables,
        b,
        "union",
        arrn(vec![lst(v("a")), lst(v("a"))], lst(v("a"))),
    );
    reg(
        tables,
        b,
        "intersect",
        arrn(vec![lst(v("a")), lst(v("a"))], lst(v("a"))),
    );
    reg(tables, b, "index", arrn(vec![v("a"), lst(v("a"))], TB::Int));
    reg(
        tables,
        b,
        "find",
        arrn(vec![arr(v("a"), TB::Bool), lst(v("a"))], v("a")),
    );
    reg(
        tables,
        b,
        "find_all",
        arrn(vec![arr(v("a"), TB::Bool), lst(v("a"))], lst(v("a"))),
    );
    reg(
        tables,
        b,
        "partition",
        arrn(
            vec![arr(v("a"), TB::Bool), lst(v("a"))],
            tup(vec![lst(v("a")), lst(v("a"))]),
        ),
    );
    reg(
        tables,
        b,
        "assoc",
        arrn(vec![v("a"), lst(tup(vec![v("a"), v("b")]))], v("b")),
    );
    reg(
        tables,
        b,
        "assq",
        arrn(vec![v("a"), lst(tup(vec![v("a"), v("b")]))], v("b")),
    );
    reg(
        tables,
        b,
        "mem_assoc",
        arrn(vec![v("a"), lst(tup(vec![v("a"), v("b")]))], TB::Bool),
    );

    reg(tables, b, "stdin", TB::InChannel);
    reg(tables, b, "std_in", TB::InChannel);
    reg(tables, b, "stdout", TB::OutChannel);
    reg(tables, b, "std_out", TB::OutChannel);
    reg(tables, b, "stderr", TB::OutChannel);
    reg(tables, b, "std_err", TB::OutChannel);
    reg(tables, b, "exit", arr(TB::Int, v("a")));
    reg(tables, b, "flush", arr(TB::OutChannel, TB::Unit));
    reg(tables, b, "print_char", arr(TB::Char, TB::Unit));
    reg(tables, b, "print_string", arr(TB::String, TB::Unit));
    reg(tables, b, "print_int", arr(TB::Int, TB::Unit));
    reg(tables, b, "print_float", arr(TB::Float, TB::Unit));
    reg(tables, b, "print_endline", arr(TB::String, TB::Unit));
    reg(tables, b, "print_newline", arr(TB::Unit, TB::Unit));
    reg(tables, b, "prerr_char", arr(TB::Char, TB::Unit));
    reg(tables, b, "prerr_string", arr(TB::String, TB::Unit));
    reg(tables, b, "prerr_int", arr(TB::Int, TB::Unit));
    reg(tables, b, "prerr_float", arr(TB::Float, TB::Unit));
    reg(tables, b, "prerr_endline", arr(TB::String, TB::Unit));
    reg(tables, b, "read_line", arr(TB::Unit, TB::String));
    reg(tables, b, "read_int", arr(TB::Unit, TB::Int));
    reg(tables, b, "read_float", arr(TB::Unit, TB::Float));
    reg(tables, b, "open_out", arr(TB::String, TB::OutChannel));
    reg(tables, b, "close_out", arr(TB::OutChannel, TB::Unit));
    reg(
        tables,
        b,
        "output_char",
        arrn(vec![TB::OutChannel, TB::Char], TB::Unit),
    );
    reg(
        tables,
        b,
        "output_string",
        arrn(vec![TB::OutChannel, TB::String], TB::Unit),
    );

    let fmt_out = |a: TB| TB::Format(Box::new(a), Box::new(TB::OutChannel), Box::new(TB::Unit));
    let fmt_str = |a: TB| TB::Format(Box::new(a), Box::new(TB::Unit), Box::new(TB::String));
    reg(
        tables,
        b,
        "fprintf",
        arrn(vec![TB::OutChannel, fmt_out(v("a"))], v("a")),
    );
    reg(tables, b, "printf", arr(fmt_out(v("a")), v("a")));
    reg(tables, b, "eprintf", arr(fmt_out(v("a")), v("a")));
    reg(tables, b, "sprintf", arr(fmt_str(v("a")), v("a")));
    reg(
        tables,
        b,
        "fprint",
        arrn(vec![TB::OutChannel, TB::String], TB::Unit),
    );
    reg(tables, b, "print", arr(TB::String, TB::Unit));
    reg(tables, b, "eprint", arr(TB::String, TB::Unit));

    reg(tables, b, "!", arr(TB::Ref(Box::new(v("a"))), v("a")));
    reg(
        tables,
        b,
        ":=",
        arrn(vec![TB::Ref(Box::new(v("a"))), v("a")], TB::Unit),
    );
    reg(tables, b, "incr", arr(TB::Ref(Box::new(TB::Int)), TB::Unit));
    reg(tables, b, "decr", arr(TB::Ref(Box::new(TB::Int)), TB::Unit));
}

pub fn type_arrow(arena: &mut TypeArena, t1: TypId, t2: TypId) -> TypId {
    arena.alloc(TypDesc::Tarrow(t1, t2), NOTGENERIC)
}

pub fn type_product(arena: &mut TypeArena, list: Vec<TypId>) -> TypId {
    arena.alloc(TypDesc::Tproduct(list), NOTGENERIC)
}

pub fn type_vect(builtins: &Builtins, arena: &mut TypeArena, ty_arg: TypId) -> TypId {
    arena.alloc(TypDesc::Tconstr(builtins.vect, vec![ty_arg]), NOTGENERIC)
}

pub type Env = Vec<(String, (TypId, Mutability))>;

fn env_lookup<'a>(env: &'a Env, name: &str) -> Option<&'a (TypId, Mutability)> {
    env.iter().find(|(n, _)| n == name).map(|(_, v)| v)
}

fn unify_pat(
    arena: &mut TypeArena,
    constrs: &TypeConstrArena,
    expected: TypId,
    actual: TypId,
    loc: Loc,
) -> Result<(), TypeError> {
    unify(arena, constrs, expected, actual).map_err(|_| TypeError::PatWrongType(loc))
}

fn unify_expr(
    arena: &mut TypeArena,
    constrs: &TypeConstrArena,
    expected: TypId,
    actual: TypId,
    loc: Loc,
) -> Result<(), TypeError> {
    unify(arena, constrs, expected, actual).map_err(|_| TypeError::ExprWrongType(loc))
}

fn resolve_constant_constr(tables: &GlobalTables, name: &str) -> Option<ConstrDescId> {
    tables.constrs.find_by_name(name).filter(|&id| {
        matches!(
            tables.constrs.get(id).info.cs_kind,
            ConstrKind::ConstrConstant
        )
    })
}

fn ref_name(r: &GlobalRef) -> &str {
    match r {
        GlobalRef::Name(n) => n,
        GlobalRef::Symbol(_, n) => n,
        GlobalRef::Modname(q) => &q.id,
    }
}

pub fn tpat(
    tables: &mut GlobalTables,
    new_env: Env,
    pat: &Pattern,
    ty: TypId,
    mut_flag: Mutability,
) -> Result<Env, TypeError> {
    match &pat.desc {
        PatternDesc::Wild => Ok(new_env),

        PatternDesc::Var(v) => {
            let name = ref_name(v);
            if let Some(cstr_id) = resolve_constant_constr(tables, name) {
                let ty_res = {
                    let cs_res = tables.constrs.get(cstr_id).info.cs_res;
                    type_instance(&mut tables.types, cs_res)
                };
                unify_pat(&mut tables.types, &tables.type_constrs, ty, ty_res, pat.loc)?;
                return Ok(new_env);
            }
            if env_lookup(&new_env, name).is_some() {
                return Err(TypeError::NonLinearPattern(name.to_string(), pat.loc));
            }
            let mut env = new_env;
            env.push((name.to_string(), (ty, mut_flag)));
            Ok(env)
        }

        PatternDesc::Alias(p, v) => {
            let name = ref_name(v);
            if env_lookup(&new_env, name).is_some() {
                return Err(TypeError::NonLinearPattern(name.to_string(), pat.loc));
            }
            let mut env = new_env;
            env.push((name.to_string(), (ty, mut_flag)));
            tpat(tables, env, p, ty, mut_flag)
        }

        PatternDesc::Constant(c) => {
            let actual = type_of_atomic_constant_by_name(tables, c)
                .ok_or_else(|| TypeError::UnboundTypeConstr("<builtin>".to_string(), pat.loc))?;
            unify_pat(&mut tables.types, &tables.type_constrs, ty, actual, pat.loc)?;
            Ok(new_env)
        }

        PatternDesc::Tuple(list) => {
            let tys = filter_product(&mut tables.types, &tables.type_constrs, list.len(), ty)
                .map_err(|_| TypeError::PatWrongType(pat.loc))?;
            tpat_list(tables, new_env, list, &tys)
        }

        PatternDesc::Construct0(r) => {
            let name = ref_name(r);
            let cstr_id = tables
                .constrs
                .find_by_name(name)
                .ok_or_else(|| TypeError::UnboundConstr(name.to_string(), pat.loc))?;
            let kind = tables.constrs.get(cstr_id).info.cs_kind;
            if kind != ConstrKind::ConstrConstant {
                return Err(TypeError::NonConstantConstr(pat.loc));
            }
            let cs_res = tables.constrs.get(cstr_id).info.cs_res;
            let ty_res = type_instance(&mut tables.types, cs_res);
            unify_pat(&mut tables.types, &tables.type_constrs, ty, ty_res, pat.loc)?;
            Ok(new_env)
        }

        PatternDesc::Construct1(r, arg) => {
            let name = ref_name(r);
            let cstr_id = tables
                .constrs
                .find_by_name(name)
                .ok_or_else(|| TypeError::UnboundConstr(name.to_string(), pat.loc))?;
            let info = &tables.constrs.get(cstr_id).info;
            if info.cs_kind == ConstrKind::ConstrConstant {
                return Err(TypeError::ConstantConstr(pat.loc));
            }
            let (cs_res, cs_arg, cs_mut) = (info.cs_res, info.cs_arg, info.cs_mut);
            let (ty_res, ty_arg) = type_pair_instance(&mut tables.types, cs_res, cs_arg);
            unify_pat(&mut tables.types, &tables.type_constrs, ty, ty_res, pat.loc)?;
            tpat(tables, new_env, arg, ty_arg, cs_mut)
        }

        PatternDesc::App(head, args) => {
            if let (PatternDesc::Var(name), [single]) = (&head.desc, args.as_slice()) {
                if let Some(cstr_id) = tables.constrs.find_by_name(ref_name(name)) {
                    let info = &tables.constrs.get(cstr_id).info;
                    if info.cs_kind != ConstrKind::ConstrConstant {
                        let (cs_res, cs_arg, cs_mut) = (info.cs_res, info.cs_arg, info.cs_mut);
                        let (ty_res, ty_arg) =
                            type_pair_instance(&mut tables.types, cs_res, cs_arg);
                        unify_pat(&mut tables.types, &tables.type_constrs, ty, ty_res, pat.loc)?;
                        return tpat(tables, new_env, single, ty_arg, cs_mut);
                    }
                }
            }
            Err(TypeError::MalformedApp(pat.loc))
        }

        PatternDesc::Or(p1, p2) => {
            if !free_vars_of_pat(pat).is_empty() {
                return Err(TypeError::OrpatShouldBeClosed(pat.loc));
            }
            let env1 = tpat(tables, new_env, p1, ty, mut_flag)?;
            tpat(tables, env1, p2, ty, mut_flag)
        }

        PatternDesc::Constraint(p, texpr) => {
            let ty2 = type_of_type_expression(tables, true, texpr)?;
            let env2 = tpat(tables, new_env, p, ty2, mut_flag)?;
            unify_pat(&mut tables.types, &tables.type_constrs, ty, ty2, pat.loc)?;
            Ok(env2)
        }

        PatternDesc::Record(fields) => {
            let mut env = new_env;
            for (r, p) in fields {
                let name = ref_name(r);
                let lbl_id = tables
                    .labels
                    .find_by_name(name)
                    .ok_or_else(|| TypeError::UnboundLabel(name.to_string(), pat.loc))?;
                let info = &tables.labels.get(lbl_id).info;
                let (lbl_res, lbl_arg, lbl_mut) = (info.lbl_res, info.lbl_arg, info.lbl_mut);
                let (ty_res, ty_arg) = type_pair_instance(&mut tables.types, lbl_res, lbl_arg);
                unify_pat(&mut tables.types, &tables.type_constrs, ty, ty_res, pat.loc)?;
                env = tpat(tables, env, p, ty_arg, lbl_mut)?;
            }
            Ok(env)
        }
    }
}

fn tpat_list(
    tables: &mut GlobalTables,
    new_env: Env,
    pats: &[Pattern],
    tys: &[TypId],
) -> Result<Env, TypeError> {
    let mut env = new_env;
    for (p, &ty) in pats.iter().zip(tys.iter()) {
        env = tpat(tables, env, p, ty, Mutability::Notmutable)?;
    }
    Ok(env)
}

pub fn type_pattern(tables: &mut GlobalTables, pat: &Pattern, ty: TypId) -> Result<Env, TypeError> {
    tpat(tables, Vec::new(), pat, ty, Mutability::Notmutable)
}

pub fn type_pattern_list(
    tables: &mut GlobalTables,
    pats: &[Pattern],
    tys: &[TypId],
) -> Result<Env, TypeError> {
    tpat_list(tables, Vec::new(), pats, tys)
}

fn free_vars_of_pat(pat: &Pattern) -> Vec<String> {
    let mut acc = Vec::new();
    free_vars_of_pat_rec(pat, &mut acc);
    acc
}

fn free_vars_of_pat_rec(pat: &Pattern, acc: &mut Vec<String>) {
    match &pat.desc {
        PatternDesc::Wild | PatternDesc::Constant(_) | PatternDesc::Construct0(_) => {}
        PatternDesc::Var(v) => acc.push(ref_name(v).to_string()),
        PatternDesc::Alias(p, v) => {
            acc.push(ref_name(v).to_string());
            free_vars_of_pat_rec(p, acc);
        }
        PatternDesc::Tuple(list) => list.iter().for_each(|p| free_vars_of_pat_rec(p, acc)),
        PatternDesc::Construct1(_, p) => free_vars_of_pat_rec(p, acc),
        PatternDesc::App(head, args) => {
            free_vars_of_pat_rec(head, acc);
            args.iter().for_each(|p| free_vars_of_pat_rec(p, acc));
        }
        PatternDesc::Or(p1, p2) => {
            free_vars_of_pat_rec(p1, acc);
            free_vars_of_pat_rec(p2, acc);
        }
        PatternDesc::Constraint(p, _) => free_vars_of_pat_rec(p, acc),
        PatternDesc::Record(fields) => fields
            .iter()
            .for_each(|(_, p)| free_vars_of_pat_rec(p, acc)),
    }
}

pub fn type_of_type_expression(
    tables: &mut GlobalTables,
    strict: bool,
    texpr: &TypeExpr,
) -> Result<TypId, TypeError> {
    let mut vars: HashMap<String, TypId> = HashMap::new();
    type_of_rec(tables, strict, &mut vars, texpr)
}

pub fn type_of_type_expression_with_vars(
    tables: &mut GlobalTables,
    strict: bool,
    vars: &mut HashMap<String, TypId>,
    texpr: &TypeExpr,
) -> Result<TypId, TypeError> {
    type_of_rec(tables, strict, vars, texpr)
}

pub(crate) fn type_of_rec(
    tables: &mut GlobalTables,
    strict: bool,
    vars: &mut HashMap<String, TypId>,
    texpr: &TypeExpr,
) -> Result<TypId, TypeError> {
    match &texpr.desc {
        TypeDesc::Var(v) => {
            if let Some(&t) = vars.get(v) {
                Ok(t)
            } else if strict {
                Err(TypeError::UnboundTypeVar(v.clone(), texpr.loc))
            } else {
                let t = new_global_type_var(&mut tables.types);
                vars.insert(v.clone(), t);
                Ok(t)
            }
        }
        TypeDesc::Arrow(a, b) => {
            let ta = type_of_rec(tables, strict, vars, a)?;
            let tb = type_of_rec(tables, strict, vars, b)?;
            Ok(type_arrow(&mut tables.types, ta, tb))
        }
        TypeDesc::Tuple(list) => {
            let tys = list
                .iter()
                .map(|t| type_of_rec(tables, strict, vars, t))
                .collect::<Result<Vec<_>, _>>()?;
            Ok(type_product(&mut tables.types, tys))
        }
        TypeDesc::Constr(r, args) => {
            let name = ref_name(r);
            let decl_id = tables
                .type_constrs
                .find_by_name(name)
                .ok_or_else(|| TypeError::UnboundTypeConstr(name.to_string(), texpr.loc))?;
            let ty_arity = tables.type_constrs.get(decl_id).info.ty_arity;
            if args.len() as i32 != ty_arity {
                return Err(TypeError::TypeArityErr {
                    name: name.to_string(),
                    expected: ty_arity,
                    got: args.len(),
                    loc: texpr.loc,
                });
            }
            let tys = args
                .iter()
                .map(|t| type_of_rec(tables, strict, vars, t))
                .collect::<Result<Vec<_>, _>>()?;
            Ok(tables
                .types
                .alloc(TypDesc::Tconstr(decl_id, tys), NOTGENERIC))
        }
    }
}

fn type_of_atomic_constant_by_name(tables: &mut GlobalTables, c: &AtomicConstant) -> Option<TypId> {
    let name = match c {
        AtomicConstant::Int(_) => "int",
        AtomicConstant::Float(_) => "float",
        AtomicConstant::Str(_) => "string",
        AtomicConstant::Char(_) => "char",
    };
    let cstr_id = tables.type_constrs.find_by_name(name)?;
    Some(
        tables
            .types
            .alloc(TypDesc::Tconstr(cstr_id, Vec::new()), NOTGENERIC),
    )
}

fn type_of_atomic_constant_b(builtins: &Builtins, c: &AtomicConstant) -> TypId {
    match c {
        AtomicConstant::Int(_) => builtins.ty_int,
        AtomicConstant::Float(_) => builtins.ty_float,
        AtomicConstant::Str(_) => builtins.ty_string,
        AtomicConstant::Char(_) => builtins.ty_char,
    }
}

fn type_of_structured_constant(builtins: &Builtins, c: &StructConstant) -> TypId {
    match c {
        StructConstant::Atom(a) => type_of_atomic_constant_b(builtins, a),
    }
}

pub fn is_nonexpansive(expr: &Expr) -> bool {
    match &expr.desc {
        ExprDesc::Ident(_) => true,
        ExprDesc::Constant(_) => true,
        ExprDesc::Tuple(list) => list.iter().all(is_nonexpansive),
        ExprDesc::Construct0(_) => true,
        ExprDesc::Construct1(_, e) => is_nonexpansive(e),
        ExprDesc::Let(_, bindings, body) => {
            bindings.iter().all(|(_, e)| is_nonexpansive(e)) && is_nonexpansive(body)
        }
        ExprDesc::Function(_) => true,
        ExprDesc::TryWith(body, cases) => {
            is_nonexpansive(body) && cases.iter().all(|(_, e)| is_nonexpansive(e))
        }
        ExprDesc::Sequence(_, e2) => is_nonexpansive(e2),
        ExprDesc::Condition(_, ifso, ifnot) => is_nonexpansive(ifso) && is_nonexpansive(ifnot),
        ExprDesc::Constraint(e, _) => is_nonexpansive(e),
        ExprDesc::Vector(list) => list.is_empty() || false,
        ExprDesc::Record(fields) => fields.iter().all(|(_, e)| is_nonexpansive(e)),
        ExprDesc::RecordAccess(e, _) => is_nonexpansive(e),
        ExprDesc::When(_, act) => is_nonexpansive(act),
        _ => false,
    }
}

pub struct TypeCtx<'a> {
    pub tables: &'a mut GlobalTables,
    pub infer: Infer,
    pub builtins: Builtins,
}

impl<'a> TypeCtx<'a> {
    pub fn new(tables: &'a mut GlobalTables) -> Self {
        let builtins = install_builtins(tables);
        install_prims(tables, &builtins);
        TypeCtx {
            tables,
            infer: Infer::new(),
            builtins,
        }
    }

    fn is_void(&self, e: &Expr) -> bool {
        matches!(&e.desc, ExprDesc::Construct0(GlobalRef::Name(n)) if n == CONSTR_VOID)
    }

    pub fn type_expr(&mut self, env: &Env, expr: &Expr) -> Result<TypId, TypeError> {
        let ty = match &expr.desc {
            ExprDesc::Ident(r) => {
                let name = ref_name(r);
                if let Some((ty_schema, _)) = env_lookup(env, name) {
                    type_instance(&mut self.tables.types, *ty_schema)
                } else if let Some(cstr_id) = resolve_constant_constr(self.tables, name) {
                    let cs_res = self.tables.constrs.get(cstr_id).info.cs_res;
                    type_instance(&mut self.tables.types, cs_res)
                } else if let Some(val_id) = self.tables.values.find_by_name(name) {
                    let val_typ = self.tables.values.get(val_id).info.val_typ;
                    type_instance(&mut self.tables.types, val_typ)
                } else {
                    return Err(TypeError::UnboundValue(name.to_string(), expr.loc));
                }
            }

            ExprDesc::Constant(c) => type_of_structured_constant(&self.builtins, c),

            ExprDesc::Tuple(args) => {
                let tys = args
                    .iter()
                    .map(|e| self.type_expr(env, e))
                    .collect::<Result<Vec<_>, _>>()?;
                type_product(&mut self.tables.types, tys)
            }

            ExprDesc::Construct0(r) => {
                let name = ref_name(r);
                let cstr_id = self
                    .tables
                    .constrs
                    .find_by_name(name)
                    .ok_or_else(|| TypeError::UnboundConstr(name.to_string(), expr.loc))?;
                let info = &self.tables.constrs.get(cstr_id).info;
                if info.cs_kind == ConstrKind::ConstrConstant {
                    let cs_res = info.cs_res;
                    type_instance(&mut self.tables.types, cs_res)
                } else {
                    let (cs_res, cs_arg) = (info.cs_res, info.cs_arg);
                    let (ty_res, ty_arg) =
                        type_pair_instance(&mut self.tables.types, cs_res, cs_arg);
                    type_arrow(&mut self.tables.types, ty_arg, ty_res)
                }
            }

            ExprDesc::Construct1(r, arg) => {
                let name = ref_name(r);
                let cstr_id = self
                    .tables
                    .constrs
                    .find_by_name(name)
                    .ok_or_else(|| TypeError::UnboundConstr(name.to_string(), expr.loc))?;
                let info = &self.tables.constrs.get(cstr_id).info;
                if info.cs_kind == ConstrKind::ConstrConstant {
                    return Err(TypeError::ConstantConstr(expr.loc));
                }
                let (cs_res, cs_arg) = (info.cs_res, info.cs_arg);
                let (ty_res, ty_arg) = type_pair_instance(&mut self.tables.types, cs_res, cs_arg);
                self.type_expect(env, arg, ty_arg)?;
                ty_res
            }

            ExprDesc::Apply(f, args) => {
                if let ExprDesc::Ident(r) = &f.desc {
                    let name = ref_name(r);
                    if let Some(cstr_id) = self.tables.constrs.find_by_name(name) {
                        let kind = self.tables.constrs.get(cstr_id).info.cs_kind;
                        if kind != ConstrKind::ConstrConstant && args.len() == 1 {
                            let info = &self.tables.constrs.get(cstr_id).info;
                            let (cs_res, cs_arg) = (info.cs_res, info.cs_arg);
                            let (ty_res, ty_arg) =
                                type_pair_instance(&mut self.tables.types, cs_res, cs_arg);
                            self.type_expect(env, &args[0], ty_arg)?;
                            return Ok(self.finish(expr, ty_res));
                        }
                    }
                }
                let mut ty_res = self.type_expr(env, f)?;
                for arg in args {
                    let (ty1, ty2) =
                        filter_arrow(&mut self.tables.types, &self.tables.type_constrs, ty_res)
                            .map_err(|_| TypeError::ApplicationOfNonFunction(expr.loc))?;
                    self.type_expect(env, arg, ty1)?;
                    ty_res = ty2;
                }
                ty_res
            }

            ExprDesc::Assign(reference, e) => {
                let id = ref_name(reference);
                let (ty_schema, mut_flag) = env_lookup(env, id)
                    .cloned()
                    .ok_or_else(|| TypeError::UnboundValue(id.to_string(), expr.loc))?;
                if mut_flag == Mutability::Notmutable {
                    return Err(TypeError::NotMutable(id.to_string(), expr.loc));
                }
                let inst = type_instance(&mut self.tables.types, ty_schema);
                self.type_expect(env, e, inst)?;
                self.builtins.ty_unit
            }

            ExprDesc::RecordAccess(e, r) => {
                let name = ref_name(r);
                let lbl_id = self
                    .tables
                    .labels
                    .find_by_name(name)
                    .ok_or_else(|| TypeError::UnboundLabel(name.to_string(), expr.loc))?;
                let info = &self.tables.labels.get(lbl_id).info;
                let (lbl_res, lbl_arg) = (info.lbl_res, info.lbl_arg);
                let (ty_res, ty_arg) = type_pair_instance(&mut self.tables.types, lbl_res, lbl_arg);
                self.type_expect(env, e, ty_res)?;
                ty_arg
            }

            ExprDesc::RecordUpdate(e1, r, e2) => {
                let name = ref_name(r);
                let lbl_id = self
                    .tables
                    .labels
                    .find_by_name(name)
                    .ok_or_else(|| TypeError::UnboundLabel(name.to_string(), expr.loc))?;
                let info = &self.tables.labels.get(lbl_id).info;
                if info.lbl_mut == Mutability::Notmutable {
                    return Err(TypeError::LabelNotMutable(expr.loc));
                }
                let (lbl_res, lbl_arg) = (info.lbl_res, info.lbl_arg);
                let (ty_res, ty_arg) = type_pair_instance(&mut self.tables.types, lbl_res, lbl_arg);
                self.type_expect(env, e1, ty_res)?;
                self.type_expect(env, e2, ty_arg)?;
                self.builtins.ty_unit
            }

            ExprDesc::Record(fields) => {
                let ty = self.infer.new_type_var(&mut self.tables.types);
                for (r, e) in fields {
                    let name = ref_name(r);
                    let lbl_id = self
                        .tables
                        .labels
                        .find_by_name(name)
                        .ok_or_else(|| TypeError::UnboundLabel(name.to_string(), expr.loc))?;
                    let info = &self.tables.labels.get(lbl_id).info;
                    let (lbl_res, lbl_arg) = (info.lbl_res, info.lbl_arg);
                    let (ty_res, ty_arg) =
                        type_pair_instance(&mut self.tables.types, lbl_res, lbl_arg);
                    unify(
                        &mut self.tables.types,
                        &self.tables.type_constrs,
                        ty,
                        ty_res,
                    )
                    .map_err(|_| TypeError::LabelNotBelong(expr.loc))?;
                    self.type_expect(env, e, ty_arg)?;
                }
                ty
            }

            ExprDesc::Vector(elems) => {
                let ty_arg = self.infer.new_type_var(&mut self.tables.types);
                for e in elems {
                    self.type_expect(env, e, ty_arg)?;
                }
                type_vect(&self.builtins, &mut self.tables.types, ty_arg)
            }

            ExprDesc::Constraint(e, texpr) => {
                let ty2 = type_of_type_expression(self.tables, false, texpr)?;
                self.type_expect(env, e, ty2)?;
                ty2
            }

            ExprDesc::Condition(cond, ifso, ifnot) => {
                self.type_expect(env, cond, self.builtins.ty_bool)?;
                if self.is_void(ifnot) {
                    self.type_expect(env, ifso, self.builtins.ty_unit)?;
                    self.builtins.ty_unit
                } else {
                    let ty = self.type_expr(env, ifso)?;
                    self.type_expect(env, ifnot, ty)?;
                    ty
                }
            }

            ExprDesc::While(cond, body) => {
                self.type_expect(env, cond, self.builtins.ty_bool)?;
                self.type_statement(env, body)?;
                self.builtins.ty_unit
            }

            ExprDesc::For {
                var,
                start,
                stop,
                body,
                ..
            } => {
                self.type_expect(env, start, self.builtins.ty_int)?;
                self.type_expect(env, stop, self.builtins.ty_int)?;
                let mut env2 = env.clone();
                env2.push((
                    ref_name(var).to_string(),
                    (self.builtins.ty_int, Mutability::Notmutable),
                ));
                self.type_statement(&env2, body)?;
                self.builtins.ty_unit
            }

            ExprDesc::Sequence(e1, e2) => {
                self.type_statement(env, e1)?;
                self.type_expr(env, e2)?
            }

            ExprDesc::When(cond, act) => {
                self.type_expect(env, cond, self.builtins.ty_bool)?;
                self.type_expr(env, act)?
            }

            ExprDesc::Function(cases) => {
                if cases.is_empty() {
                    panic!("type_expr: empty matching");
                }
                let n_args = cases[0].0.len();
                let ty_args: Vec<TypId> = (0..n_args)
                    .map(|_| self.infer.new_type_var(&mut self.tables.types))
                    .collect();
                let ty_res = self.infer.new_type_var(&mut self.tables.types);
                for (patl, action) in cases {
                    if patl.len() != ty_args.len() {
                        return Err(TypeError::IllShapedMatch(expr.loc));
                    }
                    let mut case_env = type_pattern_list(self.tables, patl, &ty_args)?;
                    case_env.extend(env.iter().cloned());
                    self.type_expect(&case_env, action, ty_res)?;
                }
                let mut result = ty_res;
                for &ty_arg in ty_args.iter().rev() {
                    result = type_arrow(&mut self.tables.types, ty_arg, result);
                }
                result
            }

            ExprDesc::TryWith(body, cases) => {
                let ty = self.type_expr(env, body)?;
                for (pat, action) in cases {
                    let exn_ty = self.builtins_exn_ty();
                    let mut case_env = type_pattern(self.tables, pat, exn_ty)?;
                    case_env.extend(env.iter().cloned());
                    self.type_expect(&case_env, action, ty)?;
                }
                ty
            }

            ExprDesc::Let(rec_flag, bindings, body) => {
                let new_env = self.type_let_decl(env, *rec_flag, bindings)?;
                self.type_expr(&new_env, body)?
            }
        };
        Ok(self.finish(expr, ty))
    }

    fn finish(&self, _expr: &Expr, ty: TypId) -> TypId {
        ty
    }

    fn builtins_exn_ty(&mut self) -> TypId {
        self.tables
            .types
            .alloc(TypDesc::Tconstr(self.builtins.exn, Vec::new()), NOTGENERIC)
    }

    pub fn type_expect(
        &mut self,
        env: &Env,
        expr: &Expr,
        expected_ty: TypId,
    ) -> Result<(), TypeError> {
        match &expr.desc {
            ExprDesc::Constant(StructConstant::Atom(AtomicConstant::Str(s))) => {
                let repr = type_repr(&mut self.tables.types, expected_ty);
                let actual = match &self.tables.types.get(repr).desc {
                    TypDesc::Tconstr(cstr, _) if *cstr == self.builtins.format => {
                        type_format(&self.infer, self.tables, &self.builtins, expr.loc, s)?
                    }
                    _ => self.builtins.ty_string,
                };
                unify_expr(
                    &mut self.tables.types,
                    &self.tables.type_constrs,
                    expected_ty,
                    actual,
                    expr.loc,
                )
            }
            ExprDesc::Let(rec_flag, bindings, body) => {
                let new_env = self.type_let_decl(env, *rec_flag, bindings)?;
                self.type_expect(&new_env, body, expected_ty)
            }
            ExprDesc::Sequence(e1, e2) => {
                self.type_statement(env, e1)?;
                self.type_expect(env, e2, expected_ty)
            }
            ExprDesc::Condition(cond, ifso, ifnot) => {
                self.type_expect(env, cond, self.builtins.ty_bool)?;
                self.type_expect(env, ifso, expected_ty)?;
                self.type_expect(env, ifnot, expected_ty)
            }
            ExprDesc::Tuple(list) => {
                match filter_product(
                    &mut self.tables.types,
                    &self.tables.type_constrs,
                    list.len(),
                    expected_ty,
                ) {
                    Ok(tys) => {
                        for (e, ty) in list.iter().zip(tys.iter()) {
                            self.type_expect(env, e, *ty)?;
                        }
                        Ok(())
                    }
                    Err(_) => {
                        let actual = self.type_expr(env, expr)?;
                        unify_expr(
                            &mut self.tables.types,
                            &self.tables.type_constrs,
                            expected_ty,
                            actual,
                            expr.loc,
                        )
                    }
                }
            }
            _ => {
                let actual = self.type_expr(env, expr)?;
                unify_expr(
                    &mut self.tables.types,
                    &self.tables.type_constrs,
                    expected_ty,
                    actual,
                    expr.loc,
                )
            }
        }
    }

    pub fn type_let_decl(
        &mut self,
        env: &Env,
        rec_flag: bool,
        bindings: &[Binding],
    ) -> Result<Env, TypeError> {
        self.infer.push_type_level();

        let ty_list: Vec<TypId> = bindings
            .iter()
            .map(|_| self.infer.new_type_var(&mut self.tables.types))
            .collect();

        let mut add_env: Env = Vec::new();
        let mut normalized: Vec<(Pattern, Expr)> = Vec::new();
        for (pat, expr) in bindings {
            match &pat.desc {
                PatternDesc::App(head, args) if !args.is_empty() => {
                    if let PatternDesc::Var(name) = &head.desc {
                        if self.tables.constrs.find_by_name(ref_name(name)).is_none() {
                            let var_pat = pat_constr_or_var(head.loc, name.clone());
                            let fn_expr = expr_of_function(pat.loc, args.clone(), expr.clone());
                            normalized.push((var_pat, fn_expr));
                            continue;
                        }
                    }
                    normalized.push((pat.clone(), expr.clone()));
                }
                _ => normalized.push((pat.clone(), expr.clone())),
            }
        }

        for ((pat, _), &ty) in normalized.iter().zip(ty_list.iter()) {
            let e = type_pattern(self.tables, pat, ty)?;
            add_env.extend(e);
        }

        let mut new_env = add_env.clone();
        new_env.extend(env.iter().cloned());

        for ((_, expr), &ty) in normalized.iter().zip(ty_list.iter()) {
            let use_env = if rec_flag { &new_env } else { env };
            self.type_expect(use_env, expr, ty)?;
        }

        self.infer.pop_type_level();

        for ((_, expr), &ty) in normalized.iter().zip(ty_list.iter()) {
            if is_nonexpansive(expr) {
                generalize_type(&self.infer, &mut self.tables.types, ty);
            } else {
                nongen_type(&self.infer, &mut self.tables.types, ty);
            }
        }

        Ok(new_env)
    }

    pub fn type_statement(&mut self, env: &Env, expr: &Expr) -> Result<(), TypeError> {
        let ty = self.type_expr(env, expr)?;
        let ty = type_repr(&mut self.tables.types, ty);
        match &self.tables.types.get(ty).desc {
            TypDesc::Tarrow(_, _) => {}
            TypDesc::Tvar(_) => {}
            _ => {
                if !same_base_type(
                    &mut self.tables.types,
                    &self.tables.type_constrs,
                    ty,
                    self.builtins.ty_unit,
                ) {}
            }
        }
        Ok(())
    }

    pub fn elaborate_type_decls(&mut self, decls: &[TypeDecl]) -> Result<(), TypeError> {
        let mut slots: Vec<TypeConstrId> = Vec::new();
        for (name, params, _def) in decls {
            let cstr_id = self.tables.type_constrs.alloc(
                QualIdent {
                    qual: String::new(),
                    id: name.clone(),
                },
                TypeInfo {
                    ty_abbr: TypeAbbrev::Tnotabbrev,
                    ty_arity: params.len() as i32,
                    ty_desc: TypeComponents::AbstractType,
                },
            );
            slots.push(cstr_id);
        }

        for ((_name, params, def), &cstr_id) in decls.iter().zip(slots.iter()) {
            let mut vars: HashMap<String, TypId> = HashMap::new();
            let mut param_ids = Vec::new();
            for p in params {
                let v = self
                    .tables
                    .types
                    .alloc(TypDesc::Tvar(TypLink::Tnolink), GENERIC);
                vars.insert(p.clone(), v);
                param_ids.push(v);
            }
            let ty_this = self
                .tables
                .types
                .alloc(TypDesc::Tconstr(cstr_id, param_ids.clone()), GENERIC);

            match def {
                TypeDef::Abstract => {}
                TypeDef::Abbrev(texpr) => {
                    let body = type_of_rec(self.tables, true, &mut vars, texpr)?;
                    self.tables.type_constrs.get_mut(cstr_id).info.ty_abbr =
                        TypeAbbrev::Tabbrev(param_ids.clone(), body);
                    check_recursive_abbrev(
                        &mut self.tables.types,
                        &self.tables.type_constrs,
                        cstr_id,
                    )
                    .map_err(|_| TypeError::RecursiveAbbrevErr(Loc::default()))?;
                    self.tables.type_constrs.get_mut(cstr_id).info.ty_desc =
                        TypeComponents::AbbrevType(param_ids.clone(), body);
                }
                TypeDef::Variant(constrs) => {
                    let n = constrs.len() as i32;
                    let mut ids = Vec::new();
                    for (i, c) in constrs.iter().enumerate() {
                        let id = match c {
                            ConstrDecl::Constr0(cname) => self.tables.constrs.alloc(
                                QualIdent {
                                    qual: String::new(),
                                    id: cname.clone(),
                                },
                                ConstrDesc {
                                    cs_res: ty_this,
                                    cs_arg: no_type(&mut self.tables.types),
                                    cs_mut: Mutability::Notmutable,
                                    cs_tag: ConstrTag::ConstrRegular(i as i32, n),
                                    cs_kind: ConstrKind::ConstrConstant,
                                },
                            ),
                            ConstrDecl::Constr1(cname, arg_texpr, _mutf) => {
                                let arg_ty = type_of_rec(self.tables, true, &mut vars, arg_texpr)?;
                                self.tables.constrs.alloc(
                                    QualIdent {
                                        qual: String::new(),
                                        id: cname.clone(),
                                    },
                                    ConstrDesc {
                                        cs_res: ty_this,
                                        cs_arg: arg_ty,
                                        cs_mut: Mutability::Notmutable,
                                        cs_tag: ConstrTag::ConstrRegular(i as i32, n),
                                        cs_kind: ConstrKind::ConstrRegular,
                                    },
                                )
                            }
                        };
                        ids.push(id);
                    }
                    self.tables.type_constrs.get_mut(cstr_id).info.ty_desc =
                        TypeComponents::VariantType(ids);
                }
                TypeDef::Record(labels) => {
                    let mut ids = Vec::new();
                    for (pos, (lname, ltexpr, lmut)) in labels.iter().enumerate() {
                        let larg = type_of_rec(self.tables, true, &mut vars, ltexpr)?;
                        let id = self.tables.labels.alloc(
                            QualIdent {
                                qual: String::new(),
                                id: lname.clone(),
                            },
                            LabelDesc {
                                lbl_res: ty_this,
                                lbl_arg: larg,
                                lbl_mut: *lmut,
                                lbl_pos: pos as i32,
                            },
                        );
                        ids.push(id);
                    }
                    self.tables.type_constrs.get_mut(cstr_id).info.ty_desc =
                        TypeComponents::RecordType(ids);
                }
            }
        }

        Ok(())
    }

    pub fn elaborate_exc_decls(&mut self, decls: &[ConstrDecl]) -> Result<(), TypeError> {
        let ty_exn = self.builtins_exn_ty();
        for c in decls {
            let (name, cs_arg, cs_kind) = match c {
                ConstrDecl::Constr0(name) => (
                    name.clone(),
                    no_type(&mut self.tables.types),
                    ConstrKind::ConstrConstant,
                ),
                ConstrDecl::Constr1(name, texpr, _mutf) => {
                    let mut vars = HashMap::new();
                    let arg_ty =
                        type_of_type_expression_with_vars(self.tables, false, &mut vars, texpr)?;
                    (name.clone(), arg_ty, ConstrKind::ConstrRegular)
                }
            };
            let id = self.tables.constrs.alloc(
                QualIdent {
                    qual: String::new(),
                    id: name,
                },
                ConstrDesc {
                    cs_res: ty_exn,
                    cs_arg,
                    cs_mut: Mutability::Notmutable,
                    cs_tag: ConstrTag::ConstrRegular(0, 0),
                    cs_kind,
                },
            );
            self.tables.constrs.get_mut(id).info.cs_tag = ConstrTag::ConstrExtensible(id);
        }
        Ok(())
    }
}

fn pat_constr_or_var(loc: Loc, name: GlobalRef) -> Pattern {
    pat(loc, PatternDesc::Var(name))
}

fn expr_of_function(loc: Loc, args: Vec<Pattern>, body: Expr) -> Expr {
    expr(loc, ExprDesc::Function(vec![(args, body)]))
}
