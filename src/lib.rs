pub mod constraint;
pub mod digit;

pub use constraint::{parse_sentence, Constraint};
pub use digit::DigitSet;

/// Return a sorted Vec of all DigitSets that match the given list of constraints.
pub fn matching_sets(constraints: &[Constraint]) -> Vec<DigitSet> {
    let mut sets: Vec<DigitSet> =
        DigitSet::iter_all().filter(|set| set.satisfies(constraints)).collect();
    sets.sort_unstable();
    sets
}
