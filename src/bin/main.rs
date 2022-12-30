use std::collections::BTreeMap;
use std::fmt;

use clap::{Arg, ArgAction};
use rustyline::{config::Configurer, error::ReadlineError, Editor};

use killercage::DigitSet;

/// Helper for grouping digitsets. Field order corresponds to sort order
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
struct SetGroup {
    len: u8,
    sum: u8,
}

impl fmt::Display for SetGroup {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "[{} in {}]", self.sum, self.len)
    }
}

/// Handle a constraint sentence command
fn handle_sentence(input: &str) {
    // allocate a new list every time, trade a bit of allocation overhead for simplicity, since
    // caching a vec means using a mutex or ugly thread-local code.
    let mut constraints = Vec::new();
    if let Err(err) = killercage::parse_sentence(input, &mut constraints) {
        println!("Error: {err}");
        return;
    }

    let sets = killercage::matching_sets(&constraints);
    if sets.is_empty() {
        println!("[no matching sets]");
        return;
    }

    // Group sets by length and sum. The BTreeMap handles ordering by the SetGroup (length and then
    // sum), and matching_sets already returns results in order so the Vec for each group will be
    // sorted already.
    let mut map = BTreeMap::<SetGroup, Vec<DigitSet>>::new();
    for set in sets {
        let group = SetGroup { len: set.len(), sum: set.sum() };
        map.entry(group).or_default().push(set);
    }

    for (group, sets) in map {
        print!("{}{} ", group, if group.sum >= 10 { "" } else { " " });
        let mut first = true;
        for set in sets {
            if first {
                print!("{set}");
                first = false;
            } else {
                print!(" {set}");
            }
        }
        println!();
    }
}

fn run_interactive() {
    let mut input = Editor::<()>::new().expect("failed to init readline");
    input.set_auto_add_history(true);
    println!("Welcome to the Killer Sudoku cage calculator!");

    let mut ctrlc = false;
    loop {
        match input.readline("> ").as_deref() {
            Ok("q" | "quit" | "exit") => break,
            Ok("h" | "help" | "?" | "/?") => println!("[TODO: help text goes here]"),
            Ok(emptyline) if emptyline.trim().is_empty() => continue,
            Ok(line) => handle_sentence(line),
            Err(ReadlineError::Interrupted) => {
                if ctrlc {
                    println!("Use 'quit' to exit");
                }
                ctrlc = true;
                continue;
            }
            Err(ReadlineError::Eof) => {
                println!("Ctrl-D");
                break;
            }
            Err(err) => {
                println!("Fatal: {err:?}");
                break;
            }
        }

        ctrlc = false;
        println!();
    }
    println!("Goodbye!");
}

fn main() {
    serif::Config::new().with_default(tracing::Level::WARN).init();

    let args = clap::command!()
        .about("Helper for getting possibile sets of digits for Killer Sudoku cages")
        .arg(
            Arg::new("interactive")
                .short('i')
                .long("interactive")
                .action(ArgAction::SetTrue)
                .help("Run in interactive mode. This is the default if no SENTENCE is specified."),
        )
        .arg(
            Arg::new("sentences")
                .action(ArgAction::Append)
                .required(false)
                .value_name("SENTENCE")
                .conflicts_with("interactive")
                .help("Test a single command sentence rather than starting an interactive shell."),
        )
        .get_matches();

    if args.get_flag("interactive") || !args.contains_id("sentences") {
        run_interactive();
    } else {
        for sentence in args.get_many::<String>("sentences").unwrap() {
            handle_sentence(sentence);
        }
    }
}
