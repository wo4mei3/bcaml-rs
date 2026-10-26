pub type Ident = String;

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

    Assign(Ident, BoxExpr),

    RecordAccess(BoxExpr, GlobalRef),

    RecordUpdate(BoxExpr, GlobalRef, BoxExpr),

    Record(Vec<(GlobalRef, Expr)>),

    Vector(Vec<Expr>),

    Constraint(BoxExpr, TypeExpr),
    Condition(BoxExpr, BoxExpr, BoxExpr),

    While(BoxExpr, BoxExpr),
    For {
        var: Ident,
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
}

pub type BoxPattern = Box<Pattern>;

#[derive(Clone, Debug)]
pub enum PatternDesc {
    Wild,
    Var(Ident),
    Alias(BoxPattern, Ident),
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
}

#[derive(Clone, Debug)]
pub enum IntfPhrase {
    ValueDecl(Vec<ValueDecl>),
    TypeDecl(Vec<TypeDecl>),
    ExcDecl(Vec<ConstrDecl>),
    Directive(Directive),
}

pub const CONSTR_CONS: &str = "::";
pub const CONSTR_NIL: &str = "[]";
pub const CONSTR_VOID: &str = "()";

pub fn expr(loc: Loc, desc: ExprDesc) -> Expr {
    Expr { desc, loc }
}

pub fn pat(loc: Loc, desc: PatternDesc) -> Pattern {
    Pattern { desc, loc }
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

pub fn pat_constr_or_var(loc: Loc, name: Ident) -> Pattern {
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
        ExprDesc::Ident(GlobalRef::Name(x)) => Ok(expr(loc, ExprDesc::Assign(x, Box::new(rhs)))),
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
