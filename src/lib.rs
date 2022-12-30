pub mod constraint;
pub mod digit;

pub use constraint::{parse_sentence, Constraint};
pub use digit::{Digit, DigitSet};

/// Return a sorted Vec of all DigitSets that match the given list of constraints.
pub fn matching_sets(constraints: &[Constraint]) -> Vec<DigitSet> {
    // DigitSet::iter_all yields elements in sorted order, no need to sort after collecting.
    DigitSet::iter_all().filter(|set| set.satisfies(constraints)).collect()
}
