fn main() {
    let mut constraints = Vec::new();
    for arg in std::env::args().skip(1) {
        constraints.clear();
        match killercage::constraint::parse_many(&arg, &mut constraints) {
            Ok(()) => {
                let sets = killercage::matching_sets(&constraints);
                print!("{arg}: {constraints:?}: ");
                let mut first = true;
                for set in sets {
                    print!("{}{}", if first { "" } else { " " }, set);
                    first = false;
                }
                println!();
            }
            Err(err) => println!("Error: {err}"),
        }
    }
}
