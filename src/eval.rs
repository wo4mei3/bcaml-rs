use std::cell::RefCell;
use std::collections::HashMap;
use std::fmt;
use std::rc::Rc;

use crate::ast::*;

type Store = Rc<RefCell<HashMap<String, Value>>>;

#[derive(Clone)]
pub enum Value {
    Int(i64),
    Float(f64),
    String(Rc<RefCell<String>>),
    Char(char),
    Bool(bool),
    Unit,
    Tuple(Vec<Value>),
    Vector(Rc<RefCell<Vec<Value>>>),
    Record(HashMap<String, Value>),
    Constructor(String),
    Constructed(String, Option<Box<Value>>),
    Ref(Rc<RefCell<Value>>),
    Closure(Rc<Closure>),
    Primitive(String),
    Partial(String, Vec<Value>),
    Uninitialized,
}

pub struct Closure {
    cases: Vec<Case>,
}

struct Case {
    patterns: Vec<Pattern>,
    body: Expr,
    env: Store,
}

#[derive(Debug)]
pub enum EvalError {
    Unbound(String),
    InvalidApplication,
    PatternMatch,
    Runtime(String),
    Raised(Value),
}

impl fmt::Debug for Value {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(&display_value(self))
    }
}

impl fmt::Display for EvalError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Unbound(name) => write!(f, "unbound value: {name}"),
            Self::InvalidApplication => f.write_str("application of non-function"),
            Self::PatternMatch => f.write_str("pattern matching failed"),
            Self::Runtime(message) => f.write_str(message),
            Self::Raised(value) => write!(f, "uncaught exception: {value:?}"),
        }
    }
}

pub struct Evaluator {
    env: Store,
}

impl Evaluator {
    pub fn new() -> Self {
        Self {
            env: Rc::new(RefCell::new(HashMap::new())),
        }
    }

    pub fn eval_expr(&mut self, expr: &Expr) -> Result<Value, EvalError> {
        eval_expr(expr, self.env.clone())
    }

    pub fn eval_let(
        &mut self,
        rec_flag: bool,
        bindings: &[Binding],
    ) -> Result<Vec<(String, Value)>, EvalError> {
        let next = if rec_flag {
            self.env.clone()
        } else {
            Rc::new(RefCell::new(self.env.borrow().clone()))
        };
        let mut added = Vec::new();
        let mut normalized = Vec::new();
        for (pattern, body) in bindings {
            if let PatternDesc::App(head, args) = &pattern.desc {
                if let PatternDesc::Var(name) = &head.desc {
                    if !args.is_empty() {
                        normalized.push((
                            Pattern {
                                loc: head.loc,
                                symbol: head.symbol,
                                desc: PatternDesc::Var(name.clone()),
                            },
                            Expr {
                                loc: body.loc,
                                symbol: body.symbol,
                                desc: ExprDesc::Function(vec![(args.clone(), body.clone())]),
                            },
                        ));
                        continue;
                    }
                }
            }
            normalized.push((pattern.clone(), body.clone()));
        }
        if rec_flag {
            for (pattern, _) in &normalized {
                for name in pattern_names(pattern) {
                    next.borrow_mut().insert(name, Value::Uninitialized);
                }
            }
        }
        for (pattern, body) in &normalized {
            // Non-recursive bindings are simultaneous: their right-hand
            // sides see the enclosing scope, not earlier bindings.
            let value_env = if rec_flag {
                next.clone()
            } else {
                self.env.clone()
            };
            let value = eval_expr(body, value_env)?;
            let mut bindings = HashMap::new();
            if !match_pattern(pattern, &value, &mut bindings) {
                return Err(EvalError::PatternMatch);
            }
            if matches!(pattern.desc, PatternDesc::Wild) {
                added.push(("_".to_string(), value.clone()));
            }
            for (name, value) in bindings {
                next.borrow_mut().insert(name.clone(), value.clone());
                added.push((name, value));
            }
        }
        self.env = next;
        Ok(added)
    }

    pub fn define_exception(&mut self, decls: &[ConstrDecl]) {
        for decl in decls {
            let name = match decl {
                ConstrDecl::Constr0(name) | ConstrDecl::Constr1(name, _, _) => name,
            };
            self.env
                .borrow_mut()
                .insert(name.clone(), Value::Constructor(name.clone()));
        }
    }
}

fn eval_expr(expr: &Expr, env: Store) -> Result<Value, EvalError> {
    match &expr.desc {
        ExprDesc::Constant(StructConstant::Atom(atom)) => Ok(match atom {
            AtomicConstant::Int(n) => Value::Int(*n),
            AtomicConstant::Float(n) => Value::Float(*n),
            AtomicConstant::Str(s) => Value::String(Rc::new(RefCell::new(s.clone()))),
            AtomicConstant::Char(c) => Value::Char(*c),
        }),
        ExprDesc::Ident(reference) => lookup_or_constructor(ref_name(reference), &env),
        ExprDesc::Tuple(items) => Ok(Value::Tuple(
            items
                .iter()
                .map(|item| eval_expr(item, env.clone()))
                .collect::<Result<_, _>>()?,
        )),
        ExprDesc::Vector(items) => Ok(Value::Vector(Rc::new(RefCell::new(
            items
                .iter()
                .map(|item| eval_expr(item, env.clone()))
                .collect::<Result<_, _>>()?,
        )))),
        ExprDesc::Construct0(reference) => {
            Ok(Value::Constructed(ref_name(reference).to_string(), None))
        }
        ExprDesc::Construct1(reference, arg) => Ok(Value::Constructed(
            ref_name(reference).to_string(),
            Some(Box::new(eval_expr(arg, env)?)),
        )),
        ExprDesc::Apply(function, args) => {
            if matches!(&function.desc, ExprDesc::Ident(reference) if ref_name(reference) == "printf")
            {
                let values = args
                    .iter()
                    .map(|arg| eval_expr(arg, env.clone()))
                    .collect::<Result<Vec<_>, _>>()?;
                return primitive_apply("printf", values);
            }
            let mut value = eval_expr(function, env.clone())?;
            for arg in args {
                value = apply(value, eval_expr(arg, env.clone())?)?;
            }
            Ok(value)
        }
        ExprDesc::Assign(reference, rhs) => {
            let name = ref_name(reference);
            let value = eval_expr(rhs, env.clone())?;
            let slot = env
                .borrow()
                .get(name)
                .cloned()
                .ok_or_else(|| EvalError::Unbound(name.to_string()))?;
            match slot {
                Value::Ref(cell) => *cell.borrow_mut() = value,
                _ => {
                    env.borrow_mut().insert(name.to_string(), value);
                }
            }
            Ok(Value::Unit)
        }
        ExprDesc::Record(fields) => Ok(Value::Record(
            fields
                .iter()
                .map(|(name, value)| {
                    Ok((ref_name(name).to_string(), eval_expr(value, env.clone())?))
                })
                .collect::<Result<_, EvalError>>()?,
        )),
        ExprDesc::RecordAccess(record, label) => match eval_expr(record, env)? {
            Value::Record(fields) => fields
                .get(ref_name(label))
                .cloned()
                .ok_or(EvalError::PatternMatch),
            _ => Err(EvalError::Runtime("record access on non-record".into())),
        },
        ExprDesc::RecordUpdate(record, label, rhs) => {
            let mut record = match eval_expr(record, env.clone())? {
                Value::Record(fields) => fields,
                _ => return Err(EvalError::Runtime("record update on non-record".into())),
            };
            record.insert(ref_name(label).to_string(), eval_expr(rhs, env)?);
            Ok(Value::Record(record))
        }
        ExprDesc::Constraint(value, _) => eval_expr(value, env),
        ExprDesc::Condition(condition, then_expr, else_expr) => {
            match eval_expr(condition, env.clone())? {
                Value::Bool(true) => eval_expr(then_expr, env),
                Value::Bool(false) => eval_expr(else_expr, env),
                _ => Err(EvalError::Runtime("condition is not bool".into())),
            }
        }
        ExprDesc::Sequence(first, second) => {
            eval_expr(first, env.clone())?;
            eval_expr(second, env)
        }
        ExprDesc::While(condition, body) => {
            while matches!(eval_expr(condition, env.clone())?, Value::Bool(true)) {
                eval_expr(body, env.clone())?;
            }
            Ok(Value::Unit)
        }
        ExprDesc::For {
            var,
            start,
            stop,
            up,
            body,
        } => {
            let a = int(eval_expr(start, env.clone())?)?;
            let b = int(eval_expr(stop, env.clone())?)?;
            let mut i = a;
            loop {
                if (*up && i > b) || (!*up && i < b) {
                    break;
                }
                env.borrow_mut()
                    .insert(ref_name(var).to_string(), Value::Int(i));
                eval_expr(body, env.clone())?;
                if *up {
                    i += 1;
                } else {
                    i -= 1;
                }
            }
            Ok(Value::Unit)
        }
        ExprDesc::Function(cases) => Ok(Value::Closure(Rc::new(Closure {
            cases: cases
                .iter()
                .map(|(patterns, body)| Case {
                    patterns: patterns.clone(),
                    body: body.clone(),
                    env: env.clone(),
                })
                .collect(),
        }))),
        ExprDesc::Let(rec_flag, bindings, body) => {
            let mut evaluator = Evaluator { env: env.clone() };
            evaluator.eval_let(*rec_flag, bindings)?;
            eval_expr(body, evaluator.env)
        }
        ExprDesc::TryWith(body, cases) => match eval_expr(body, env.clone()) {
            Err(EvalError::Raised(value)) => {
                for (pattern, action) in cases {
                    let mut bindings = HashMap::new();
                    if match_pattern(pattern, &value, &mut bindings) {
                        let local = Rc::new(RefCell::new(env.borrow().clone()));
                        local.borrow_mut().extend(bindings);
                        return eval_expr(action, local);
                    }
                }
                Err(EvalError::Raised(value))
            }
            result => result,
        },
        ExprDesc::When(condition, action) => {
            if matches!(eval_expr(condition, env.clone())?, Value::Bool(true)) {
                eval_expr(action, env)
            } else {
                Ok(Value::Unit)
            }
        }
    }
}

fn apply(function: Value, argument: Value) -> Result<Value, EvalError> {
    match function {
        Value::Constructor(name) => Ok(Value::Constructed(name, Some(Box::new(argument)))),
        Value::Closure(closure) => {
            for case in &closure.cases {
                if case.patterns.is_empty() {
                    continue;
                }
                let mut bindings = HashMap::new();
                if match_pattern(&case.patterns[0], &argument, &mut bindings) {
                    let local = Rc::new(RefCell::new(case.env.borrow().clone()));
                    local.borrow_mut().extend(bindings);
                    if case.patterns.len() == 1 {
                        return eval_expr(&case.body, local);
                    }
                    return Ok(Value::Closure(Rc::new(Closure {
                        cases: vec![Case {
                            patterns: case.patterns[1..].to_vec(),
                            body: case.body.clone(),
                            env: local,
                        }],
                    })));
                }
            }
            Err(EvalError::PatternMatch)
        }
        Value::Primitive(name) => primitive_apply(&name, vec![argument]),
        Value::Partial(name, mut args) => {
            args.push(argument);
            primitive_apply(&name, args)
        }
        _ => Err(EvalError::InvalidApplication),
    }
}

fn lookup_or_constructor(name: &str, env: &Store) -> Result<Value, EvalError> {
    if let Some(value) = env.borrow().get(name) {
        if !matches!(value, Value::Uninitialized) {
            return Ok(value.clone());
        }
    }
    match name {
        "true" => Ok(Value::Bool(true)),
        "false" => Ok(Value::Bool(false)),
        "()" => Ok(Value::Unit),
        "[]" => Ok(Value::Constructed("[]".into(), None)),
        "::" => Ok(Value::Constructor("::".into())),
        _ => Ok(Value::Primitive(name.into())),
    }
}

fn match_pattern(pattern: &Pattern, value: &Value, bindings: &mut HashMap<String, Value>) -> bool {
    match &pattern.desc {
        PatternDesc::Wild => true,
        PatternDesc::Var(name) => {
            bindings.insert(ref_name(name).to_string(), value.clone());
            true
        }
        PatternDesc::Alias(inner, name) => {
            if match_pattern(inner, value, bindings) {
                bindings.insert(ref_name(name).to_string(), value.clone());
                true
            } else {
                false
            }
        }
        PatternDesc::Constant(atom) => match (atom, value) {
            (AtomicConstant::Int(a), Value::Int(b)) => a == b,
            (AtomicConstant::Float(a), Value::Float(b)) => a == b,
            (AtomicConstant::Char(a), Value::Char(b)) => a == b,
            (AtomicConstant::Str(a), Value::String(b)) => *a == *b.borrow(),
            _ => false,
        },
        PatternDesc::Tuple(patterns) => {
            matches!(value, Value::Tuple(values) if patterns.len() == values.len() && patterns.iter().zip(values).all(|(p, v)| match_pattern(p, v, bindings)))
        }
        PatternDesc::Construct0(name) => {
            matches!(value, Value::Bool(true) if ref_name(name) == "true")
                || matches!(value, Value::Bool(false) if ref_name(name) == "false")
                || matches!(value, Value::Unit if ref_name(name) == "()")
                || matches!(value, Value::Constructed(n, None) if n == ref_name(name))
        }
        PatternDesc::Construct1(name, inner) => {
            matches!(value, Value::Constructed(n, Some(arg)) if n == ref_name(name) && match_pattern(inner, arg, bindings))
        }
        PatternDesc::Or(left, right) => {
            match_pattern(left, value, bindings) || match_pattern(right, value, bindings)
        }
        PatternDesc::Constraint(inner, _) => match_pattern(inner, value, bindings),
        PatternDesc::Record(fields) => {
            matches!(value, Value::Record(values) if fields.iter().all(|(name, p)| values.get(ref_name(name)).is_some_and(|v| match_pattern(p, v, bindings))))
        }
        PatternDesc::App(_, _) => false,
    }
}

fn pattern_names(pattern: &Pattern) -> Vec<String> {
    let mut names = Vec::new();
    collect_pattern_names(pattern, &mut names);
    names
}

fn collect_pattern_names(pattern: &Pattern, names: &mut Vec<String>) {
    match &pattern.desc {
        PatternDesc::Var(name) => names.push(ref_name(name).to_string()),
        PatternDesc::Alias(inner, name) => {
            names.push(ref_name(name).to_string());
            collect_pattern_names(inner, names);
        }
        PatternDesc::Tuple(items) => items.iter().for_each(|p| collect_pattern_names(p, names)),
        PatternDesc::Construct1(_, p) | PatternDesc::Constraint(p, _) => {
            collect_pattern_names(p, names)
        }
        PatternDesc::Record(fields) => fields
            .iter()
            .for_each(|(_, p)| collect_pattern_names(p, names)),
        PatternDesc::Or(a, b) => {
            collect_pattern_names(a, names);
            collect_pattern_names(b, names);
        }
        _ => {}
    }
}

fn int(value: Value) -> Result<i64, EvalError> {
    if let Value::Int(n) = value {
        Ok(n)
    } else {
        Err(EvalError::Runtime("expected int".into()))
    }
}
fn bool_value(value: Value) -> Result<bool, EvalError> {
    if let Value::Bool(b) = value {
        Ok(b)
    } else {
        Err(EvalError::Runtime("expected bool".into()))
    }
}
fn ref_name(reference: &GlobalRef) -> &str {
    match reference {
        GlobalRef::Name(name) => name,
        GlobalRef::Symbol(_, name) => name,
        GlobalRef::Modname(q) => &q.id,
    }
}

fn primitive_apply(name: &str, args: Vec<Value>) -> Result<Value, EvalError> {
    if name == "printf" {
        if args.len() < 2 {
            return Ok(Value::Partial(name.to_string(), args));
        }
        let format = string_value(args[0].clone())?;
        let output = format_printf(&format, &args[1..])?;
        print!("{output}");
        return Ok(Value::Unit);
    }

    let binary = |args: &[Value]| {
        if args.len() < 2 {
            return Ok(Value::Partial(name.to_string(), args.to_vec()));
        }
        let a = &args[0];
        let b = &args[1];
        let result = match name {
            "+" | "add_int" => Value::Int(int(a.clone())? + int(b.clone())?),
            "-" | "sub_int" => Value::Int(int(a.clone())? - int(b.clone())?),
            "*" | "mult_int" => Value::Int(int(a.clone())? * int(b.clone())?),
            "/" | "div_int" | "quo" => Value::Int(int(a.clone())? / int(b.clone())?),
            "mod" => Value::Int(int(a.clone())? % int(b.clone())?),
            "=" | "==" => Value::Bool(display_value(a) == display_value(b)),
            "<>" | "!=" => Value::Bool(display_value(a) != display_value(b)),
            "<" => Value::Bool(int(a.clone())? < int(b.clone())?),
            "<=" => Value::Bool(int(a.clone())? <= int(b.clone())?),
            ">" => Value::Bool(int(a.clone())? > int(b.clone())?),
            ">=" => Value::Bool(int(a.clone())? >= int(b.clone())?),
            "^" => Value::String(Rc::new(RefCell::new(
                string_value(a.clone())? + &string_value(b.clone())?,
            ))),
            ":=" => {
                if let Value::Ref(cell) = a {
                    *cell.borrow_mut() = b.clone();
                    Value::Unit
                } else {
                    return Err(EvalError::Runtime("assignment to non-reference".into()));
                }
            }
            "+." => Value::Float(float(a.clone())? + float(b.clone())?),
            "-." => Value::Float(float(a.clone())? - float(b.clone())?),
            "*." => Value::Float(float(a.clone())? * float(b.clone())?),
            "/." => Value::Float(float(a.clone())? / float(b.clone())?),
            _ => return Ok(Value::Partial(name.to_string(), args.to_vec())),
        };
        Ok(result)
    };
    match name {
        "+" | "-" | "*" | "/" | "mod" | "add_int" | "sub_int" | "mult_int" | "div_int" | "quo"
        | "=" | "<>" | "<" | "<=" | ">" | ">=" | "==" | "!=" | "^" | ":=" | "+." | "-." | "*."
        | "/." => binary(&args),
        "minus" | "minus_int" => Ok(Value::Int(-int(args
            .into_iter()
            .next()
            .ok_or(EvalError::InvalidApplication)?)?)),
        "not" => Ok(Value::Bool(!bool_value(
            args.into_iter()
                .next()
                .ok_or(EvalError::InvalidApplication)?,
        )?)),
        "succ" => Ok(Value::Int(
            int(args
                .into_iter()
                .next()
                .ok_or(EvalError::InvalidApplication)?)?
                + 1,
        )),
        "pred" => Ok(Value::Int(
            int(args
                .into_iter()
                .next()
                .ok_or(EvalError::InvalidApplication)?)?
                - 1,
        )),
        "ref" => Ok(Value::Ref(Rc::new(RefCell::new(
            args.into_iter()
                .next()
                .ok_or(EvalError::InvalidApplication)?,
        )))),
        "!" => match args
            .into_iter()
            .next()
            .ok_or(EvalError::InvalidApplication)?
        {
            Value::Ref(cell) => Ok(cell.borrow().clone()),
            _ => Err(EvalError::Runtime("dereference of non-reference".into())),
        },
        "raise" => Err(EvalError::Raised(
            args.into_iter()
                .next()
                .ok_or(EvalError::InvalidApplication)?,
        )),
        "failwith" | "invalid_arg" => Err(EvalError::Raised(Value::Constructed(
            name.into(),
            Some(Box::new(
                args.into_iter()
                    .next()
                    .ok_or(EvalError::InvalidApplication)?,
            )),
        ))),
        "print_int" => {
            println!(
                "{}",
                int(args
                    .into_iter()
                    .next()
                    .ok_or(EvalError::InvalidApplication)?)?
            );
            Ok(Value::Unit)
        }
        "print_string" | "print_endline" | "print" => {
            let s = string_value(
                args.into_iter()
                    .next()
                    .ok_or(EvalError::InvalidApplication)?,
            )?;
            if name == "print_endline" {
                println!("{s}");
            } else {
                print!("{s}");
            }
            Ok(Value::Unit)
        }
        "string_of_int" => Ok(Value::String(Rc::new(RefCell::new(
            int(args
                .into_iter()
                .next()
                .ok_or(EvalError::InvalidApplication)?)?
            .to_string(),
        )))),
        "int_of_string" => Ok(Value::Int(
            string_value(
                args.into_iter()
                    .next()
                    .ok_or(EvalError::InvalidApplication)?,
            )?
            .parse()
            .map_err(|_| EvalError::Runtime("invalid integer".into()))?,
        )),
        "string_of_bool" => Ok(Value::String(Rc::new(RefCell::new(
            bool_value(
                args.into_iter()
                    .next()
                    .ok_or(EvalError::InvalidApplication)?,
            )?
            .to_string(),
        )))),
        _ => Ok(Value::Partial(name.to_string(), args)),
    }
}

fn string_value(value: Value) -> Result<String, EvalError> {
    if let Value::String(s) = value {
        Ok(s.borrow().clone())
    } else {
        Err(EvalError::Runtime("expected string".into()))
    }
}
fn float(value: Value) -> Result<f64, EvalError> {
    if let Value::Float(n) = value {
        Ok(n)
    } else {
        Err(EvalError::Runtime("expected float".into()))
    }
}

fn format_printf(format: &str, args: &[Value]) -> Result<String, EvalError> {
    let mut output = String::new();
    let mut chars = format.chars();
    let mut index = 0;
    while let Some(ch) = chars.next() {
        if ch != '%' {
            output.push(ch);
            continue;
        }
        let specifier = chars
            .next()
            .ok_or_else(|| EvalError::Runtime("incomplete printf format".into()))?;
        if specifier == '%' {
            output.push('%');
            continue;
        }
        let value = args
            .get(index)
            .ok_or_else(|| EvalError::Runtime("not enough printf arguments".into()))?;
        index += 1;
        match specifier {
            'd' | 'i' => output.push_str(&int(value.clone())?.to_string()),
            'f' => output.push_str(&float(value.clone())?.to_string()),
            's' => output.push_str(&string_value(value.clone())?),
            'c' => match value {
                Value::Char(c) => output.push(*c),
                _ => return Err(EvalError::Runtime("printf %c expects char".into())),
            },
            _ => {
                return Err(EvalError::Runtime(format!(
                    "unsupported printf format: %{specifier}"
                )));
            }
        }
    }
    if index != args.len() {
        return Err(EvalError::Runtime("too many printf arguments".into()));
    }
    Ok(output)
}

fn display_value(value: &Value) -> String {
    match value {
        Value::Int(n) => n.to_string(),
        Value::Float(n) => n.to_string(),
        Value::Char(c) => format!("{c:?}"),
        Value::String(s) => format!("{:?}", s.borrow()),
        Value::Bool(b) => b.to_string(),
        Value::Unit => "()".into(),
        Value::Tuple(items) => format!(
            "({})",
            items
                .iter()
                .map(display_value)
                .collect::<Vec<_>>()
                .join(", ")
        ),
        Value::Vector(items) => format!(
            "[|{}|]",
            items
                .borrow()
                .iter()
                .map(display_value)
                .collect::<Vec<_>>()
                .join("; ")
        ),
        Value::Record(fields) => format!(
            "{{{}}}",
            fields
                .iter()
                .map(|(k, v)| format!("{k} = {}", display_value(v)))
                .collect::<Vec<_>>()
                .join("; ")
        ),
        Value::Constructed(name, None) => name.clone(),
        Value::Constructed(name, Some(v)) => format!("({name} {})", display_value(v)),
        Value::Constructor(name) => format!("<constructor {name}>"),
        Value::Ref(_) => "<ref>".into(),
        Value::Closure(_) | Value::Primitive(_) | Value::Partial(_, _) => "<fun>".into(),
        Value::Uninitialized => "<uninitialized>".into(),
    }
}
