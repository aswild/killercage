use killercage::constraint::Constraint;

fn main() {
    let cons = [Constraint::Count(5), Constraint::Sum(25)];
    let sets = killercage::matching_sets(&cons);

    for ds in sets {
        println!("{ds}");
    }
}
