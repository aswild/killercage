pub mod constraint;
pub mod digit;

use constraint::Constraint;
use digit::DigitSet;

/// Return a sorted Vec of all DigitSets that match the given list of constraints.
pub fn matching_sets(constraints: &[Constraint]) -> Vec<DigitSet> {
    let mut sets: Vec<DigitSet> =
        DigitSet::iter_all().filter(|set| set.satisfies(constraints)).collect();
    sets.sort_unstable();
    sets
}
