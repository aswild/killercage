use rustyline::{config::Configurer, error::ReadlineError, Editor};

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

    // matching sets will already be sorted by length, group them for better readability.
    // TODO: find some way to group by both length and sum
    let mut last_len = sets[0].len();
    let mut first = true;

    for set in sets {
        if set.len() != last_len {
            println!();
            last_len = set.len();
            first = true;
        }

        if first {
            print!("[len {}]", set.len());
        }
        print!(" {set}");
        first = false;
    }
    println!();
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
