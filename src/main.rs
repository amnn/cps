use std::{collections::HashSet, process::exit};

use clap::{Parser as Clap, ValueEnum};
use clap_stdin::FileOrStdin;

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

    let toks = lex::pass(&args.input);
    if debug_phases.contains(&Phase::Lexer) {
        println!("Tokens:");
        for token in toks.clone() {
            println!("{token:?}");
        }
        println!("\n");
    }

    let astp = match parse::pass(toks) {
        Ok(ast) => ast,
        Err(err) => {
            eprintln!("Error parsing input: {err}");
            exit(1);
        }
    };

    if debug_phases.contains(&Phase::Parser) {
        println!("AST: {astp:#?}\n");
    }

    let astn = naming::pass(astp);
    if debug_phases.contains(&Phase::Naming) {
        println!("Naming: {astn:#?}\n");
    }

    let astc = cps::pass(astn);
    if debug_phases.contains(&Phase::Cps) {
        println!("CPS: {astc:#?}\n");
    }
}
