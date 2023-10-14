use std::{collections::HashSet, process::exit};

use clap::{Parser as Clap, ValueEnum};
use clap_stdin::FileOrStdin;
use cps::Cps;
use lex::Lexer;
use parse::Parser;

mod cps;
mod lex;
mod naming;
mod parse;

#[cfg(test)]
mod fixtures;

#[derive(Clap)]
#[command(author, version, about)]
struct Args {
    #[arg(
        long = "Xdump",
        help = "Debug dump after various phases of the compiler."
    )]
    dump: Vec<Phase>,

    input: FileOrStdin,
}

#[derive(Clone, Copy, Eq, PartialEq, Hash, ValueEnum)]
enum Phase {
    #[value(name = "lex")]
    Lexer,
    #[value(name = "parse")]
    Parser,
    #[value(name = "naming")]
    Naming,
    #[value(name = "cps")]
    Cps,
}

fn main() {
    let args = Args::parse();
    let debug_phases: HashSet<_> = args.dump.iter().copied().collect();

    let lex = Lexer::new(&args.input);
    if debug_phases.contains(&Phase::Lexer) {
        println!("Tokens:");
        for token in lex.clone() {
            println!("{token:?}");
        }
        println!("\n");
    }

    let ast = match Parser::parse(lex) {
        Ok(ast) => ast,
        Err(err) => {
            eprintln!("Error parsing input: {err}");
            exit(4);
        }
    };

    if debug_phases.contains(&Phase::Parser) {
        println!("AST: {ast:#?}\n");
    }

    let dbj = naming::pass(ast);
    if debug_phases.contains(&Phase::Naming) {
        println!("Naming: {dbj:#?}\n");
    }

    let cps = Cps::convert(dbj);
    if debug_phases.contains(&Phase::Cps) {
        println!("CPS: {cps:#?}\n");
    }
}
