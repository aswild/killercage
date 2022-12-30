use std::collections::BTreeMap;
use std::fmt;

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

fn main() {
    serif::Config::new().with_default(tracing::Level::WARN).init();

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
