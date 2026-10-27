pub type Ident = String;
pub type Path = Vec<Ident>;
use crate::symbol::{NameTable, Resolver, SymbolId};

#[derive(Clone, Copy, Debug, PartialEq, Eq, Default)]
pub struct Loc {
    pub start: usize,
    pub end: usize,
}

impl Loc {
    pub fn new(start: usize, end: usize) -> Self {
        Loc { start, end }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct QualIdent {
    pub qual: String,
    pub id: String,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum GlobalRef {
    Name(String),
    Symbol(SymbolId, String),
    Modname(QualIdent),
}

#[derive(Clone, Debug, PartialEq)]
pub enum AtomicConstant {
    Int(i64),
    Float(f64),
    Str(String),
    Char(char),
}

#[derive(Clone, Debug, PartialEq)]
pub enum StructConstant {
    Atom(AtomicConstant),
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Mutability {
    Mutable,
    Notmutable,
}

#[derive(Clone, Debug)]
pub struct Expr {
    pub desc: ExprDesc,
    pub loc: Loc,
    pub symbol: Option<SymbolId>,
}

pub type BoxExpr = Box<Expr>;

#[derive(Clone, Debug)]
pub enum ExprDesc {
    Constant(StructConstant),
    Ident(GlobalRef),

    Tuple(Vec<Expr>),

    Apply(BoxExpr, Vec<Expr>),

    Construct0(GlobalRef),

    Construct1(GlobalRef, BoxExpr),

    Assign(GlobalRef, BoxExpr),

    RecordAccess(BoxExpr, GlobalRef),

    RecordUpdate(BoxExpr, GlobalRef, BoxExpr),

    Record(Vec<(GlobalRef, Expr)>),

    Vector(Vec<Expr>),

    Constraint(BoxExpr, TypeExpr),
    Condition(BoxExpr, BoxExpr, BoxExpr),

    While(BoxExpr, BoxExpr),
    For {
        var: GlobalRef,
        start: BoxExpr,
        stop: BoxExpr,
        up: bool,
        body: BoxExpr,
    },

    Sequence(BoxExpr, BoxExpr),

    Function(Vec<MatchCase>),

    Let(bool, Vec<Binding>, BoxExpr),

    TryWith(BoxExpr, Vec<(Pattern, Expr)>),
    When(BoxExpr, BoxExpr),
}

pub type Binding = (Pattern, Expr);
pub type MatchCase = (Vec<Pattern>, Expr);

#[derive(Clone, Debug)]
pub struct Pattern {
    pub desc: PatternDesc,
    pub loc: Loc,
    pub symbol: Option<SymbolId>,
}

pub type BoxPattern = Box<Pattern>;

#[derive(Clone, Debug)]
pub enum PatternDesc {
    Wild,
    Var(GlobalRef),
    Alias(BoxPattern, GlobalRef),
    Constant(AtomicConstant),
    Tuple(Vec<Pattern>),
    Construct0(GlobalRef),
    Construct1(GlobalRef, BoxPattern),
    Or(BoxPattern, BoxPattern),
    Constraint(BoxPattern, TypeExpr),
    Record(Vec<(GlobalRef, Pattern)>),

    App(BoxPattern, Vec<Pattern>),
}

#[derive(Clone, Debug)]
pub struct TypeExpr {
    pub desc: TypeDesc,
    pub loc: Loc,
}

#[derive(Clone, Debug)]
pub enum TypeDesc {
    Var(Ident),
    Arrow(Box<TypeExpr>, Box<TypeExpr>),
    Tuple(Vec<TypeExpr>),
    Constr(GlobalRef, Vec<TypeExpr>),
}

#[derive(Clone, Debug)]
pub enum TypeDef {
    Abstract,
    Variant(Vec<ConstrDecl>),
    Record(Vec<LabelDecl>),
    Abbrev(TypeExpr),
}

#[derive(Clone, Debug)]
pub enum ConstrDecl {
    Constr0(Ident),
    Constr1(Ident, TypeExpr, Mutability),
}

pub type LabelDecl = (Ident, TypeExpr, Mutability);

pub type TypeDecl = (Ident, Vec<Ident>, TypeDef);

#[derive(Clone, Debug)]
pub enum PrimDecl {
    NotPrim,
    Prim { arity: i64, name: String },
}

pub type ValueDecl = (Ident, TypeExpr, PrimDecl);

#[derive(Clone, Debug)]
pub struct Directive {
    pub name: String,
    pub arg: String,
}

#[derive(Clone, Debug)]
pub enum ImplPhrase {
    Expr(Expr),
    LetDef(bool, Vec<Binding>),
    TypeDef(Vec<TypeDecl>),
    ExcDef(Vec<ConstrDecl>),
    Directive(Directive),
    Module(Ident, ModExpr),
    ModuleType(Ident, SigExpr),
}

#[derive(Clone, Debug)]
pub enum IntfPhrase {
    ValueDecl(Vec<ValueDecl>),
    TypeDecl(Vec<TypeDecl>),
    ExcDecl(Vec<ConstrDecl>),
    Directive(Directive),
}

#[derive(Clone, Debug)]
pub struct SigExpr {
    pub desc: SigDesc,
    pub loc: Loc,
}

#[derive(Clone, Debug)]
pub enum SigDesc {
    Var(Ident),
    Struct(Vec<SigItem>),
    Functor(Ident, Box<SigExpr>, Box<SigExpr>),
    WithType(Box<SigExpr>, Ident, TypeExpr),
}

#[derive(Clone, Debug)]
pub enum SigItem {
    Value(Ident, TypeExpr),
    Type(Vec<TypeDecl>),
    Module(Ident, SigExpr),
}

#[derive(Clone, Debug)]
pub struct ModExpr {
    pub desc: ModDesc,
    pub loc: Loc,
}

#[derive(Clone, Debug)]
pub enum ModDesc {
    Var(Ident),
    Access(Box<ModExpr>, Ident),
    Struct(Vec<ModBinding>),
    Functor(Ident, Box<SigExpr>, Box<ModExpr>),
    Apply(Box<ModExpr>, Vec<ModExpr>),
    Seal(Box<ModExpr>, Box<SigExpr>),
}

#[derive(Clone, Debug)]
pub enum ModBinding {
    Expr(Expr),
    Let(bool, Vec<Binding>),
    Type(Vec<TypeDecl>),
    Module(Ident, ModExpr),
    ModuleType(Ident, SigExpr),
}

pub const CONSTR_CONS: &str = "::";
pub const CONSTR_NIL: &str = "[]";
pub const CONSTR_VOID: &str = "()";

pub fn expr(loc: Loc, desc: ExprDesc) -> Expr {
    Expr {
        desc,
        loc,
        symbol: None,
    }
}

pub fn pat(loc: Loc, desc: PatternDesc) -> Pattern {
    Pattern {
        desc,
        loc,
        symbol: None,
    }
}

fn resolve_ref(table: &mut NameTable, resolver: &Resolver, reference: &mut GlobalRef) {
    if let GlobalRef::Name(name) = reference {
        let id = resolver.resolve(name).unwrap_or_else(|| table.intern(name));
        *reference = GlobalRef::Symbol(id, name.clone());
    }
}

fn resolve_binder(table: &mut NameTable, resolver: &mut Resolver, reference: &mut GlobalRef) {
    if let GlobalRef::Name(name) = reference {
        let id = resolver.declare(table, name);
        *reference = GlobalRef::Symbol(id, name.clone());
    }
}

pub fn resolve_pattern(table: &mut NameTable, resolver: &mut Resolver, pattern: &mut Pattern) {
    match &mut pattern.desc {
        PatternDesc::Var(reference) => {
            resolve_binder(table, resolver, reference);
            let id = match reference {
                GlobalRef::Symbol(id, _) => *id,
                _ => unreachable!(),
            };
            pattern.symbol = Some(id);
        }
        PatternDesc::Alias(inner, reference) => {
            resolve_pattern(table, resolver, inner);
            resolve_binder(table, resolver, reference);
            if let GlobalRef::Symbol(id, _) = reference {
                pattern.symbol = Some(*id);
            }
        }
        PatternDesc::Tuple(items) => items
            .iter_mut()
            .for_each(|p| resolve_pattern(table, resolver, p)),
        PatternDesc::Construct0(r) => resolve_ref(table, resolver, r),
        PatternDesc::Construct1(r, p) => {
            resolve_ref(table, resolver, r);
            resolve_pattern(table, resolver, p);
        }
        PatternDesc::Or(a, b) => {
            resolve_pattern(table, resolver, a);
            resolve_pattern(table, resolver, b);
        }
        PatternDesc::Constraint(p, _) => resolve_pattern(table, resolver, p),
        PatternDesc::Record(fields) => fields.iter_mut().for_each(|(r, p)| {
            resolve_ref(table, resolver, r);
            resolve_pattern(table, resolver, p);
        }),
        PatternDesc::App(head, args) => {
            resolve_pattern(table, resolver, head);
            args.iter_mut()
                .for_each(|p| resolve_pattern(table, resolver, p));
        }
        PatternDesc::Wild | PatternDesc::Constant(_) => {}
    }
}

pub fn resolve_expr(table: &mut NameTable, resolver: &mut Resolver, expr: &mut Expr) {
    match &mut expr.desc {
        ExprDesc::Ident(r) | ExprDesc::Construct0(r) => resolve_ref(table, resolver, r),
        ExprDesc::Construct1(r, e) => {
            resolve_ref(table, resolver, r);
            resolve_expr(table, resolver, e);
        }
        ExprDesc::Assign(r, e) => {
            resolve_ref(table, resolver, r);
            resolve_expr(table, resolver, e);
        }
        ExprDesc::Tuple(es) | ExprDesc::Vector(es) => {
            es.iter_mut().for_each(|e| resolve_expr(table, resolver, e))
        }
        ExprDesc::Apply(f, args) => {
            resolve_expr(table, resolver, f);
            args.iter_mut()
                .for_each(|e| resolve_expr(table, resolver, e));
        }
        ExprDesc::Record(fields) => fields.iter_mut().for_each(|(r, e)| {
            resolve_ref(table, resolver, r);
            resolve_expr(table, resolver, e);
        }),
        ExprDesc::RecordAccess(e, r) => {
            resolve_expr(table, resolver, e);
            resolve_ref(table, resolver, r);
        }
        ExprDesc::RecordUpdate(e, r, v) => {
            resolve_expr(table, resolver, e);
            resolve_ref(table, resolver, r);
            resolve_expr(table, resolver, v);
        }
        ExprDesc::Constraint(e, _) | ExprDesc::When(e, _) => resolve_expr(table, resolver, e),
        ExprDesc::Condition(a, b, c) => {
            resolve_expr(table, resolver, a);
            resolve_expr(table, resolver, b);
            resolve_expr(table, resolver, c);
        }
        ExprDesc::While(a, b) | ExprDesc::Sequence(a, b) => {
            resolve_expr(table, resolver, a);
            resolve_expr(table, resolver, b);
        }
        ExprDesc::For {
            var,
            start,
            stop,
            body,
            ..
        } => {
            resolve_expr(table, resolver, start);
            resolve_expr(table, resolver, stop);
            resolver.push_scope();
            resolve_binder(table, resolver, var);
            resolve_expr(table, resolver, body);
            resolver.pop_scope();
        }
        ExprDesc::Function(cases) => {
            for (patterns, body) in cases {
                resolver.push_scope();
                patterns
                    .iter_mut()
                    .for_each(|p| resolve_pattern(table, resolver, p));
                resolve_expr(table, resolver, body);
                resolver.pop_scope();
            }
        }
        ExprDesc::Let(rec, bindings, body) => {
            resolver.push_scope();
            if *rec {
                for (p, _) in bindings.iter_mut() {
                    resolve_pattern(table, resolver, p);
                }
            }
            for (p, e) in bindings {
                if !*rec {
                    resolve_expr(table, resolver, e);
                    resolve_pattern(table, resolver, p);
                } else {
                    resolve_expr(table, resolver, e);
                }
            }
            resolve_expr(table, resolver, body);
            resolver.pop_scope();
        }
        ExprDesc::TryWith(body, cases) => {
            resolve_expr(table, resolver, body);
            for (p, e) in cases {
                resolver.push_scope();
                resolve_pattern(table, resolver, p);
                resolve_expr(table, resolver, e);
                resolver.pop_scope();
            }
        }
        ExprDesc::Constant(_) => {}
    }
}

pub fn typ(loc: Loc, desc: TypeDesc) -> TypeExpr {
    TypeExpr { desc, loc }
}

fn gref(name: &str) -> GlobalRef {
    GlobalRef::Name(name.to_string())
}

pub fn void(loc: Loc) -> Expr {
    expr(loc, ExprDesc::Construct0(gref(CONSTR_VOID)))
}

pub fn binop(loc: Loc, op: &str, a: Expr, b: Expr) -> Expr {
    let f = expr(loc, ExprDesc::Ident(gref(op)));
    expr(loc, ExprDesc::Apply(Box::new(f), vec![a, b]))
}

pub fn unop(loc: Loc, op: &str, a: Expr) -> Expr {
    let f = expr(loc, ExprDesc::Ident(gref(op)));
    expr(loc, ExprDesc::Apply(Box::new(f), vec![a]))
}

pub fn ternop(loc: Loc, op: &str, a: Expr, b: Expr, c: Expr) -> Expr {
    let f = expr(loc, ExprDesc::Ident(gref(op)));
    expr(loc, ExprDesc::Apply(Box::new(f), vec![a, b, c]))
}

pub fn unary_minus(loc: Loc, op: &str, a: Expr) -> Expr {
    match (&op[..], &a.desc) {
        ("-", ExprDesc::Constant(StructConstant::Atom(AtomicConstant::Int(n)))) => expr(
            loc,
            ExprDesc::Constant(StructConstant::Atom(AtomicConstant::Int(-n))),
        ),
        ("-.", ExprDesc::Constant(StructConstant::Atom(AtomicConstant::Float(f)))) => expr(
            loc,
            ExprDesc::Constant(StructConstant::Atom(AtomicConstant::Float(-f))),
        ),
        ("-", _) => unop(loc, "minus", a),
        ("-.", _) => unop(loc, "minus_float", a),
        _ => unop(loc, op, a),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn resolver_rewrites_references_to_symbols() {
        let mut table = NameTable::new();
        let mut resolver = Resolver::new();
        let mut value = expr(Loc::default(), ExprDesc::Ident(GlobalRef::Name("x".into())));
        resolve_expr(&mut table, &mut resolver, &mut value);
        assert!(matches!(value.desc, ExprDesc::Ident(GlobalRef::Symbol(_, ref n)) if n == "x"));
    }

    #[test]
    fn resolver_assigns_distinct_symbols_to_shadowed_binders() {
        let mut table = NameTable::new();
        let mut resolver = Resolver::new();
        let mut value = expr(
            Loc::default(),
            ExprDesc::Let(
                false,
                vec![(
                    pat(
                        Loc::default(),
                        PatternDesc::Var(GlobalRef::Name("x".into())),
                    ),
                    expr(
                        Loc::default(),
                        ExprDesc::Constant(StructConstant::Atom(AtomicConstant::Int(1))),
                    ),
                )],
                Box::new(expr(
                    Loc::default(),
                    ExprDesc::For {
                        var: GlobalRef::Name("x".into()),
                        start: Box::new(expr(
                            Loc::default(),
                            ExprDesc::Constant(StructConstant::Atom(AtomicConstant::Int(0))),
                        )),
                        stop: Box::new(expr(
                            Loc::default(),
                            ExprDesc::Constant(StructConstant::Atom(AtomicConstant::Int(0))),
                        )),
                        up: true,
                        body: Box::new(expr(
                            Loc::default(),
                            ExprDesc::Ident(GlobalRef::Name("x".into())),
                        )),
                    },
                )),
            ),
        );
        resolve_expr(&mut table, &mut resolver, &mut value);
        let ExprDesc::Let(_, bindings, body) = value.desc else {
            panic!("expected let");
        };
        let PatternDesc::Var(GlobalRef::Symbol(outer, _)) = bindings[0].0.desc else {
            panic!("expected resolved outer binder");
        };
        let ExprDesc::For {
            var: GlobalRef::Symbol(inner, _),
            body,
            ..
        } = body.desc
        else {
            panic!("expected resolved for");
        };
        assert_ne!(outer, inner);
        assert!(matches!(
            body.desc,
            ExprDesc::Ident(GlobalRef::Symbol(id, _)) if id == inner
        ));
    }
}

pub fn apply(loc: Loc, f: Expr, args: Vec<Expr>) -> Expr {
    expr(loc, ExprDesc::Apply(Box::new(f), args))
}

pub fn make_list(loc: Loc, rev_elems: Vec<Expr>) -> Expr {
    let mut acc = expr(loc, ExprDesc::Construct0(gref(CONSTR_NIL)));
    for e in rev_elems {
        let cell = expr(loc, ExprDesc::Tuple(vec![e, acc]));
        acc = expr(loc, ExprDesc::Construct1(gref(CONSTR_CONS), Box::new(cell)));
    }
    acc
}

pub fn make_listpat(loc: Loc, rev_elems: Vec<Pattern>) -> Pattern {
    let mut acc = pat(loc, PatternDesc::Construct0(gref(CONSTR_NIL)));
    for p in rev_elems {
        let cell = pat(loc, PatternDesc::Tuple(vec![p, acc]));
        acc = pat(
            loc,
            PatternDesc::Construct1(gref(CONSTR_CONS), Box::new(cell)),
        );
    }
    acc
}

pub fn make_recordpat(loc: Loc, fields: Vec<(GlobalRef, Pattern)>) -> Pattern {
    pat(loc, PatternDesc::Record(fields))
}

pub fn make_range_pat(loc: Loc, lo: char, hi: char) -> Pattern {
    let (lo, hi) = if lo <= hi { (lo, hi) } else { (hi, lo) };
    let mut acc = pat(loc, PatternDesc::Constant(AtomicConstant::Char(hi)));
    let mut c = hi as u32;
    while c > lo as u32 {
        c -= 1;
        let ch = char::from_u32(c).expect("invalid char in range pattern");
        let one = pat(loc, PatternDesc::Constant(AtomicConstant::Char(ch)));
        acc = pat(loc, PatternDesc::Or(Box::new(one), Box::new(acc)));
    }
    acc
}

pub fn expr_constr_or_ident(loc: Loc, r: GlobalRef) -> Expr {
    expr(loc, ExprDesc::Ident(r))
}

pub fn pat_constr_or_var(loc: Loc, name: GlobalRef) -> Pattern {
    pat(loc, PatternDesc::Var(name))
}

pub fn find_label(r: GlobalRef) -> GlobalRef {
    r
}

pub fn find_constructor(r: GlobalRef) -> GlobalRef {
    r
}

pub fn find_primitive(arity: i64, name: String) -> PrimDecl {
    PrimDecl::Prim { arity, name }
}

pub fn make_assign(loc: Loc, lhs: Expr, rhs: Expr) -> Result<Expr, &'static str> {
    match lhs.desc {
        ExprDesc::Ident(r @ GlobalRef::Name(_)) => {
            Ok(expr(loc, ExprDesc::Assign(r, Box::new(rhs))))
        }
        ExprDesc::RecordAccess(e, f) => Ok(expr(loc, ExprDesc::RecordUpdate(e, f, Box::new(rhs)))),
        ExprDesc::Apply(f, args) => {
            let name = match &f.desc {
                ExprDesc::Ident(GlobalRef::Name(n)) => n.clone(),
                _ => return Err("left-hand side of `<-` is not assignable"),
            };
            let target = match name.as_str() {
                "vect_item" => "vect_assign",
                "nth_char" => "set_nth_char",
                _ => return Err("left-hand side of `<-` is not assignable"),
            };
            let mut args = args;
            if args.len() != 1 {
                return Err("left-hand side of `<-` is not assignable");
            }
            match args.remove(0).desc {
                ExprDesc::Tuple(mut pair) if pair.len() == 2 => {
                    let b = pair.remove(1);
                    let a = pair.remove(0);
                    Ok(ternop(loc, target, a, b, rhs))
                }
                _ => Err("left-hand side of `<-` is not assignable"),
            }
        }
        _ => Err("left-hand side of `<-` is not assignable"),
    }
}
