#![allow(dead_code, private_interfaces, unused_mut)]

mod ast;
mod eval;
mod infer;
pub mod token;
mod types;

use std::io::{self, BufRead, IsTerminal, Write};

use lalrpop_util::lalrpop_mod;

use ast::ImplPhrase;
use eval::Evaluator;
use infer::{Env, TypeCtx, TypeError};
use types::{GlobalTables, TypDesc, TypId, TypLink};

lalrpop_util::lalrpop_mod!(pub parser);

fn main() {
    let source_path = std::env::args().nth(1);
    let repl_mode = source_path.is_none();
    let mut tables = GlobalTables::new();
    let mut ctx = TypeCtx::new(&mut tables);
    let mut env: Env = Vec::new();
    let mut evaluator = Evaluator::new();

    if let Some(path) = source_path {
        let input = match std::fs::read_to_string(path) {
            Ok(input) => input,
            Err(error) => {
                eprintln!("failed to read source: {error}");
                std::process::exit(1);
            }
        };
        process_input(&input, repl_mode, &mut ctx, &mut env, &mut evaluator);
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
            if phrase.contains(";;") {
                process_input(&phrase, true, &mut ctx, &mut env, &mut evaluator);
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

fn process_input(
    input: &str,
    repl_mode: bool,
    ctx: &mut TypeCtx<'_>,
    env: &mut Env,
    evaluator: &mut Evaluator,
) {
    let lexer = match token::Lexer::new(input) {
        Ok(lexer) => lexer,
        Err(error) => {
            eprintln!("lexical error: {error}");
            return;
        }
    };
    let phrases = match parser::ImplementationParser::new().parse(lexer) {
        Ok(phrases) => phrases,
        Err(error) => {
            eprintln!("parse error: {error:?}");
            return;
        }
    };

    for phrase in phrases {
        match phrase {
            ImplPhrase::Expr(e) => match ctx.type_expr(&env, &e) {
                Ok(ty) => match evaluator.eval_expr(&e) {
                    Ok(value) if repl_mode => {
                        println!("- : {} = {value:?}", fmt_type(ctx.tables, ty))
                    }
                    Ok(_) => {}
                    Err(err) => eprintln!("evaluation error: {err}"),
                },
                Err(err) => report_type_error(&err),
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
                                            ast::PatternDesc::Var(pattern_name) if pattern_name == "_"
                                        )
                                }) {
                                    match ctx.type_expr(env, expression) {
                                        Ok(ty) => println!(
                                            "val {name} : {} = {value:?}",
                                            fmt_type(ctx.tables, ty)
                                        ),
                                        Err(err) => report_type_error(&err),
                                    }
                                }
                            }
                        }
                        *env = new_env;
                    }
                    Err(err) => report_type_error(&err),
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
                Err(err) => report_type_error(&err),
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
                Err(err) => report_type_error(&err),
            },
            ImplPhrase::Directive(_) => {
                eprintln!("(Directive processing is not supported yet)");
            }
        }
    }
}

fn report_type_error(err: &TypeError) {
    eprintln!("type error: {err:?}");
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
