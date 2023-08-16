use std::process::exit;

use clap::Parser as Clap;
use clap_stdin::FileOrStdin;
use cps::Cps;
use lex::Lexer;
use parse::Parser;

mod cps;
mod lex;
mod parse;

#[cfg(test)]
mod fixtures;

#[derive(Clap)]
#[command(author, version, about)]
struct Args {
    #[arg(long = "Xdump-lex", help = "Debug dump tokens from lexer.")]
    dump_lex: bool,

    #[arg(long = "Xdump-ast", help = "Debug dump AST, after parsing.")]
    dump_ast: bool,

    #[arg(long = "Xdump-cps", help = "Debug dump IR after CPS transform.")]
    dump_cps: bool,

    input: FileOrStdin,
}

fn main() {
    let args = Args::parse();

    let lex = Lexer::new(&args.input);
    if args.dump_lex {
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

    if args.dump_ast {
        println!("AST: {ast:#?}\n");
    }

    let cps = Cps::convert(ast);
    if args.dump_cps {
        println!("CPS: {cps:#?}\n");
    }
}
