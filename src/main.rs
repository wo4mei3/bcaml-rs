#![allow(dead_code, private_interfaces, unused_mut)]

mod ast;
mod eval;
mod infer;
pub mod symbol;
pub mod token;
mod types;

use std::io::{self, BufRead, IsTerminal, Write};

use lalrpop_util::lalrpop_mod;
use lalrpop_util::ParseError;

use ast::ImplPhrase;
use eval::Evaluator;
use infer::{Env, TypeCtx, TypeError};
use token::Tok;
use types::{GlobalTables, TypeAbbrev, TypDesc, TypId, TypLink, NOTGENERIC};

lalrpop_util::lalrpop_mod!(pub parser);

fn main() {
    let source_path = std::env::args().nth(1);
    let repl_mode = source_path.is_none();
    let mut tables = GlobalTables::new();
    let mut ctx = TypeCtx::new(&mut tables);
    let mut env: Env = Vec::new();
    let mut evaluator = Evaluator::new();
    let mut names = symbol::NameTable::new();
    let mut resolver = symbol::Resolver::new();

    if let Some(path) = source_path {
        let input = match std::fs::read_to_string(path) {
            Ok(input) => input,
            Err(error) => {
                eprintln!("failed to read source: {error}");
                std::process::exit(1);
            }
        };
        process_input(
            &input,
            repl_mode,
            &mut ctx,
            &mut env,
            &mut evaluator,
            &mut names,
            &mut resolver,
        );
    } else {
        let stdin = io::stdin();
        let interactive = io::stdin().is_terminal();
        let mut phrase = String::new();
        if interactive {
            print!("> ");
            let _ = io::stdout().flush();
        }
        for line in stdin.lock().lines() {
            let line = match line {
                Ok(line) => line,
                Err(error) => {
                    eprintln!("failed to read input: {error}");
                    break;
                }
            };
            phrase.push_str(&line);
            phrase.push('\n');
            if repl_phrase_complete(&phrase, &mut names) {
                process_input(
                    &phrase,
                    true,
                    &mut ctx,
                    &mut env,
                    &mut evaluator,
                    &mut names,
                    &mut resolver,
                );
                phrase.clear();
                if interactive {
                    print!("> ");
                    let _ = io::stdout().flush();
                }

            }
        }
        if !phrase.trim().is_empty() {
            eprintln!("incomplete phrase: expected `;;`");
        }
    }
}

fn repl_phrase_complete(input: &str, names: &mut symbol::NameTable) -> bool {
    let mut nesting = 0usize;
    let lexer = match token::Lexer::new_with_names(input, names) {
        Ok(lexer) => lexer,
        Err(_) => return false,
    };
    for token in lexer {
        let Ok((_, token, _)) = token else {
            return false;
        };
        match token {
            Tok::Sig | Tok::Struct | Tok::Begin => nesting += 1,
            Tok::End => nesting = nesting.saturating_sub(1),
            Tok::SemiSemi if nesting == 0 => return true,
            _ => {}
        }
    }
    false
}

fn process_input(
    input: &str,
    repl_mode: bool,
    ctx: &mut TypeCtx<'_>,
    env: &mut Env,
    evaluator: &mut Evaluator,
    names: &mut symbol::NameTable,
    resolver: &mut symbol::Resolver,
) {
    let lexer = match token::Lexer::new_with_names(input, names) {
        Ok(lexer) => lexer,
        Err(error) => {
            eprintln!("lexical error: {error}");
            return;
        }
    };
    let phrases = match parser::ImplementationParser::new().parse(lexer) {
        Ok(phrases) => phrases,
        Err(error) => {
            report_parse_error(input, error);
            return;
        }
    };

    for mut phrase in phrases {
        match &mut phrase {
            ImplPhrase::Expr(e) => ast::resolve_expr(names, resolver, e),
            ImplPhrase::LetDef(rec, bindings) => {
                if *rec {
                    for (p, _) in bindings.iter_mut() {
                        ast::resolve_pattern(names, resolver, p);
                    }
                }
                for (p, e) in bindings {
                    if !*rec {
                        ast::resolve_expr(names, resolver, e);
                        ast::resolve_pattern(names, resolver, p);
                    } else {
                        ast::resolve_expr(names, resolver, e);
                    }
                }
            }
            _ => {}
        }
        match phrase {
            ImplPhrase::Expr(e) => match ctx.type_expr(&env, &e) {
                Ok(ty) => match evaluator.eval_expr(&e) {
                    Ok(value) if repl_mode => {
                        println!("- : {} = {value:?}", fmt_type(ctx.tables, ty))
                    }
                    Ok(_) => {}
                    Err(err) => eprintln!("evaluation error: {err}"),
                },
                Err(err) => report_type_error(input, &err),
            },
            ImplPhrase::LetDef(rec_flag, bindings) => {
                match ctx.type_let_decl(&env, rec_flag, &bindings) {
                    Ok(new_env) => {
                        let values = match evaluator.eval_let(rec_flag, &bindings) {
                            Ok(values) => values,
                            Err(err) => {
                                eprintln!("evaluation error: {err}");
                                continue;
                            }
                        };
                        if repl_mode {
                            for (name, (ty, _mut_flag)) in
                                new_env.iter().take(new_env.len() - env.len())
                            {
                                let value = values
                                    .iter()
                                    .find(|(value_name, _)| value_name == name)
                                    .map(|(_, value)| format!("{value:?}"))
                                    .unwrap_or_else(|| "<unavailable>".to_string());
                                println!("val {name} : {} = {value}", fmt_type(ctx.tables, *ty));
                            }
                            for (name, value) in values.iter().filter(|(name, _)| name == "_") {
                                if let Some((_, expression)) = bindings.iter().find(|(pattern, _)| {
                                    matches!(&pattern.desc, ast::PatternDesc::Wild)
                                        || matches!(
                                            &pattern.desc,
                                            ast::PatternDesc::Var(ast::GlobalRef::Name(pattern_name))
                                                | ast::PatternDesc::Var(ast::GlobalRef::Symbol(_, pattern_name))
                                                if pattern_name == "_"
                                        )
                                }) {
                                    match ctx.type_expr(env, expression) {
                                        Ok(ty) => println!(
                                            "val {name} : {} = {value:?}",
                                            fmt_type(ctx.tables, ty)
                                        ),
                                        Err(err) => report_type_error(input, &err),
                                    }
                                }
                            }
                        }
                        *env = new_env;
                    }
                    Err(err) => report_type_error(input, &err),
                }
            }
            ImplPhrase::TypeDef(decls) => match ctx.elaborate_type_decls(&decls) {
                Ok(()) => {
                    if repl_mode {
                        for (name, _, _) in &decls {
                            println!("type {name} defined");
                        }
                    }
                }
                Err(err) => report_type_error(input, &err),
            },
            ImplPhrase::ExcDef(decls) => match ctx.elaborate_exc_decls(&decls) {
                Ok(()) => {
                    evaluator.define_exception(&decls);
                    if repl_mode {
                        for c in &decls {
                            let name = match c {
                                ast::ConstrDecl::Constr0(n) => n,
                                ast::ConstrDecl::Constr1(n, _, _) => n,
                            };
                            println!("exception {name} defined");
                        }
                    }
                }
                Err(err) => report_type_error(input, &err),
            },
            ImplPhrase::Directive(directive) => {
                if directive.name == "show" {
                    let path = directive.arg.trim();
                    match ctx.lookup_module_type(path) {
                        Some(id) => {
                            let abbrev = ctx.tables.type_constrs.get(id).info.ty_abbr.clone();
                            let ty = match abbrev {
                                TypeAbbrev::Tabbrev(_, body) => body,
                                TypeAbbrev::Tnotabbrev => ctx.tables.types.alloc(
                                    TypDesc::Tconstr(id, Vec::new()),
                                    NOTGENERIC,
                                ),
                            };
                            println!(
                                "{path} : {} (internal type id: {})",
                                fmt_type(ctx.tables, ty),
                                id.0
                            );
                        }
                        None => eprintln!("show: unbound module type `{path}`"),
                    }
                } else {
                    eprintln!("unknown directive `#{}`", directive.name);
                }
            }
            ImplPhrase::Module(name, module) => match evaluator.eval_module(&module) {
                Ok(value) => {
                    if let Err(err) = ctx.register_module(&name, &module, env) {
                        report_type_error(input, &err);
                    } else {
                        evaluator.install_module(name, value);
                    }
                }
                Err(err) => eprintln!("module evaluation error: {err}"),
            },
            ImplPhrase::ModuleType(name, sig) => {
                if let Err(err) = ctx.register_module_type(&name, &sig) {
                    report_type_error(input, &err);
                }
                if repl_mode {
                    println!("module type {name} defined");
                }
            }
        }
    }
}

fn report_type_error(input: &str, err: &TypeError) {
    let location = match err {
        TypeError::UnboundValue(_, loc)
        | TypeError::UnboundConstr(_, loc)
        | TypeError::UnboundLabel(_, loc)
        | TypeError::UnboundTypeConstr(_, loc)
        | TypeError::UnboundTypeVar(_, loc)
        | TypeError::TypeArityErr { loc, .. }
        | TypeError::NonLinearPattern(_, loc)
        | TypeError::OrpatShouldBeClosed(loc)
        | TypeError::PatWrongType(loc)
        | TypeError::ExprWrongType(loc)
        | TypeError::ApplicationOfNonFunction(loc)
        | TypeError::IllShapedMatch(loc)
        | TypeError::NotMutable(_, loc)
        | TypeError::LabelMultiplyDefined(loc)
        | TypeError::LabelUndefined(loc)
        | TypeError::LabelNotBelong(loc)
        | TypeError::LabelNotMutable(loc)
        | TypeError::NonConstantConstr(loc)
        | TypeError::ConstantConstr(loc)
        | TypeError::RecursiveAbbrevErr(loc)
        | TypeError::MalformedApp(loc)
        | TypeError::BadFormatLetter(loc, _) => *loc,
    };
    let message = match err {
        TypeError::ExprWrongType(_) => "expression has an incompatible type".to_owned(),
        TypeError::UnboundValue(name, _) => format!("unbound value `{name}`"),
        TypeError::UnboundConstr(name, _) => format!("unbound constructor `{name}`"),
        TypeError::UnboundLabel(name, _) => format!("unbound label `{name}`"),
        TypeError::UnboundTypeConstr(name, _) => format!("unbound type constructor `{name}`"),
        other => format!("type error: {other:?}"),
    };
    let (line, column, source_line, line_start) = source_position(input, location.start);
    eprintln!("type error at line {line}, column {column}: {message}");
    if let Some(source_line) = source_line {
        let width = location.end.saturating_sub(location.start).max(1);
        eprintln!("  {line} | {source_line}");
        eprintln!(
            "    | {}{}",
            " ".repeat(location.start.saturating_sub(line_start)),
            "^".repeat(width.min(source_line.len().max(1)))
        );
    }
}

fn report_parse_error(input: &str, error: ParseError<usize, Tok, token::LexicalError>) {
    let (location, message) = match error {
        ParseError::InvalidToken { location } => (
            location,
            "invalid token".to_owned(),
        ),
        ParseError::UnrecognizedEof { location, expected } => (
            location,
            format!("unexpected end of input; expected {}", expected_list(&expected)),
        ),
        ParseError::UnrecognizedToken {
            token: (start, token, _),
            expected,
        } => (
            start,
            format!(
                "unexpected {}; expected {}",
                token_description(&token),
                expected_list(&expected)
            ),
        ),
        ParseError::ExtraToken {
            token: (start, token, _),
        } => (
            start,
            format!("unexpected extra {}", token_description(&token)),
        ),
        ParseError::User { error } => {
            eprintln!("parse error: {error}");
            return;
        }
    };

    let (line, column, source_line, line_start) = source_position(input, location);
    eprintln!("parse error at line {line}, column {column}: {message}");
    if let Some(source_line) = source_line {
        eprintln!("  {line} | {source_line}");
        eprintln!(
            "    | {}^",
            " ".repeat(location.saturating_sub(line_start))
        );
    }
}

fn source_position(input: &str, location: usize) -> (usize, usize, Option<&str>, usize) {
    let location = location.min(input.len());
    let line_start = input[..location].rfind('\n').map_or(0, |index| index + 1);
    let line = input[..location].bytes().filter(|&byte| byte == b'\n').count() + 1;
    let column = input[line_start..location].chars().count() + 1;
    let source_line = input[line_start..]
        .split_once('\n')
        .map_or_else(|| input[line_start..].strip_suffix('\r'), |(line, _)| {
            Some(line.strip_suffix('\r').unwrap_or(line))
        });
    (line, column, source_line, line_start)
}

fn expected_list(expected: &[String]) -> String {
    match expected {
        [] => "no token".to_owned(),
        [only] => format!("`{only}`"),
        many => many
            .iter()
            .map(|item| format!("`{item}`"))
            .collect::<Vec<_>>()
            .join(", "),
    }
}

fn token_description(token: &Tok) -> String {
    match token {
        Tok::Ident(name) => format!("identifier `{name}`"),
        Tok::Int(value) => format!("integer `{value}`"),
        Tok::Float(value) => format!("float `{value}`"),
        Tok::Str(value) => format!("string literal {value:?}"),
        Tok::Char(value) => format!("character literal {value:?}"),
        Tok::SemiSemi => "`;;`".to_owned(),
        Tok::LParen => "`(`".to_owned(),
        Tok::RParen => "`)`".to_owned(),
        Tok::Dot => "`.`".to_owned(),
        Tok::Equal => "`=`".to_owned(),
        Tok::Colon => "`:`".to_owned(),
        Tok::MinusGreater => "`->`".to_owned(),
        other => format!("`{other:?}`"),
    }
}

fn fmt_type(tables: &mut GlobalTables, ty: TypId) -> String {
    let mut names: std::collections::HashMap<TypId, String> = std::collections::HashMap::new();
    let mut next = 0u32;
    fmt_rec(tables, ty, &mut names, &mut next)
}

fn fresh_var_name(next: &mut u32) -> String {
    let n = *next;
    *next += 1;
    let letter = (b'a' + (n % 26) as u8) as char;
    if n < 26 {
        format!("'{letter}")
    } else {
        format!("'{letter}{}", n / 26)
    }
}

fn fmt_rec(
    tables: &mut GlobalTables,
    ty: TypId,
    names: &mut std::collections::HashMap<TypId, String>,
    next: &mut u32,
) -> String {
    let ty = infer::type_repr(&mut tables.types, ty);
    match tables.types.get(ty).desc.clone() {
        TypDesc::Tvar(TypLink::Tnolink) => names
            .entry(ty)
            .or_insert_with(|| fresh_var_name(next))
            .clone(),
        TypDesc::Tvar(TypLink::Tlinkto(_)) => unreachable!("type_repr already resolved this"),
        TypDesc::Tarrow(t1, t2) => {
            let s1 = fmt_rec(tables, t1, names, next);
            let s2 = fmt_rec(tables, t2, names, next);
            format!("({s1} -> {s2})")
        }
        TypDesc::Tproduct(list) => {
            let parts: Vec<String> = list
                .into_iter()
                .map(|t| fmt_rec(tables, t, names, next))
                .collect();
            format!("({})", parts.join(" * "))
        }
        TypDesc::Tconstr(cstr, args) => {
            let name = tables.type_constrs.get(cstr).qualid.id.clone();
            if args.is_empty() {
                name
            } else {
                let parts: Vec<String> = args
                    .into_iter()
                    .map(|t| fmt_rec(tables, t, names, next))
                    .collect();
                if parts.len() == 1 {
                    format!("{} {name}", parts[0])
                } else {
                    format!("({}) {name}", parts.join(", "))
                }
            }
        }
    }
}
