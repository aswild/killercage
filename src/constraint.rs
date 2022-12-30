use std::fmt;
use std::num::ParseIntError;
use std::str::FromStr;

use once_cell::sync::OnceCell;
use regex::Regex;
use tracing::{debug, trace};

use crate::digit::{DigitSet, ParseDigitError};

/// regex macro, example in once_cell's docs
macro_rules! regex {
    ($re:literal $(,)?) => {{
        static RE: OnceCell<Regex> = OnceCell::new();
        RE.get_or_init(|| Regex::new($re).unwrap())
    }};
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[non_exhaustive]
pub enum Constraint {
    /// The set must have a given sum (exactly)
    Sum(u8),
    /// The set must have this many digits
    Count(u8),
    /// The set must include all of these digits
    Includes(DigitSet),
    /// The set must not include any of these digits
    Excludes(DigitSet),
}

impl Constraint {
    /// Check whether a [`DigitSet`] satisfies this constraint.
    pub fn matches(self, set: DigitSet) -> bool {
        match self {
            Constraint::Sum(sum) => set.sum() == sum,
            Constraint::Count(count) => set.len() == count,
            Constraint::Includes(digits) => (set & digits) == digits,
            Constraint::Excludes(digits) => (set & digits) == DigitSet::empty(),
        }
    }
}

impl fmt::Display for Constraint {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Constraint::Sum(sum) => write!(f, "={sum}"),
            Constraint::Count(count) => write!(f, "in {count}"),
            Constraint::Includes(digits) => write!(f, "+{digits}"),
            Constraint::Excludes(digits) => write!(f, "-{digits}"),
        }
    }
}

/// self-referential AsRef so that we can treat iterators over Constraint and &Constraint the same
impl AsRef<Constraint> for Constraint {
    #[inline]
    fn as_ref(&self) -> &Constraint {
        self
    }
}

/// A single Constraint is an one-element iterator.
impl IntoIterator for Constraint {
    type Item = Constraint;
    type IntoIter = std::iter::Once<Constraint>;

    #[inline]
    fn into_iter(self) -> Self::IntoIter {
        std::iter::once(self)
    }
}

impl FromStr for Constraint {
    type Err = ParseConstraintError;

    #[tracing::instrument(level = "trace")]
    fn from_str(s: &str) -> Result<Self, Self::Err> {
        // Any single constraint is a not-digit prefix followed by some digits. We strip whitespace
        // off of both because it doesn't really matter.
        let re = regex!(r"^([^\d]*)(\d+)\s*$");
        let caps = re.captures(s).ok_or_else(|| ParseConstraintError::NoMatch(s.into()))?;
        let op = caps.get(1).unwrap().as_str().trim();
        let num = caps.get(2).unwrap().as_str().trim();
        trace!(op = op, num = num, "regex matched for Constraint");

        match op {
            "+" => Ok(Self::Includes(num.parse()?)),
            "-" => Ok(Self::Excludes(num.parse()?)),
            "" | "=" => Ok(Self::Sum(num.parse::<u8>()?)),
            "in" => Ok(Self::Count(num.parse::<u8>()?)),
            other => Err(ParseConstraintError::UnknownOperator(other.to_owned())),
        }
    }
}

#[derive(Debug, Clone, thiserror::Error)]
pub enum ParseConstraintError {
    /// Invalid sudoku digit
    #[error("Invalid sudoku digit: {0}")]
    InvalidDigit(#[from] ParseDigitError),

    /// Invalid numeric value
    #[error("Invalid number: {0}")]
    InvalidNumber(#[from] ParseIntError),

    /// Unknown constraint name/operator
    #[error("Unknown constraint operator: {0:?}")]
    UnknownOperator(String),

    /// Couldn't even find a number, what are you even doing?
    #[error("Couldn't match constraint format in string {0:?}")]
    NoMatch(String),
}

/// Parse a Constraint Sentence (single string of multiple constraints) into a Vec.
///
/// This parses a single string such as "5 in 2 +1" into a series of [`Constraint`]s like `[Sum(5),
/// Count(2), Includes(DigitSet(1))]`.
///
/// Parsed constraints will be appended in order to the `vec` argument. If Err is returned, some
/// constraints may have been added to the vec.
#[tracing::instrument(level = "debug", skip(vec))]
pub fn parse_sentence(mut s: &str, vec: &mut Vec<Constraint>) -> Result<(), ParseConstraintError> {
    // parse one constraint, then optional whitespace, then more stuff. "rest" is the input of the
    // regex match on the next loop.
    let re = regex!(r"^(?P<cons>[^\d]*\d+)\s*(?:(?P<rest>.+)|$)");

    // special case: an empty (or all-whitespace) string is not an error
    if s.trim().is_empty() {
        return Ok(());
    }

    loop {
        let caps = re.captures(s).ok_or_else(|| ParseConstraintError::NoMatch(s.into()))?;
        let cons_str = caps.name("cons").unwrap().as_str();
        debug!(constraint = cons_str, "got one constraint string");
        let cons: Constraint = cons_str.parse()?;
        debug!(constraint = ?cons, "parsed one constraint");
        vec.push(cons);

        s = match caps.name("rest") {
            Some(rest) => rest.as_str(),
            None => break,
        };
    }

    Ok(())
}

#[cfg(test)]
mod tests {
    use super::{Constraint, ParseConstraintError};
    use crate::digit::{Digit, DigitSet, ParseDigitError};

    macro_rules! assert_matches {
        ($expression:expr, $(|)? $($pattern:pat_param)|+ $(if $guard:expr)? $(,)?) => {
            match $expression {
                $($pattern)|+ $(if $guard)? => (),
                res => panic!(
                    "{}: expected {:?} got {:?}",
                    stringify!($expression),
                    stringify!($($pattern)|+ $(if $guard)? => ()),
                    res,
                ),
            }
        };
    }

    #[test]
    fn parse_single() {
        use std::str::FromStr;
        use Digit::*;

        assert_eq!(Constraint::from_str("=10").unwrap(), Constraint::Sum(10));
        assert_eq!(Constraint::from_str("+9").unwrap(), Constraint::Includes(D9.into()));
        assert_eq!(Constraint::from_str("-2").unwrap(), Constraint::Excludes(D2.into()));
        assert_eq!(Constraint::from_str("in 5").unwrap(), Constraint::Count(5));
        assert_eq!(Constraint::from_str("  in5").unwrap(), Constraint::Count(5));
        assert_eq!(Constraint::from_str("15").unwrap(), Constraint::Sum(15));
        assert_eq!(Constraint::from_str("+79").unwrap(), Constraint::Includes([7, 9].into()));
        assert_eq!(Constraint::from_str("-123").unwrap(), Constraint::Excludes([1, 2, 3].into()));

        assert_matches!(
            Constraint::from_str("+10"),
            Err(ParseConstraintError::InvalidDigit(ParseDigitError::InvalidCharacter))
        );
    }

    #[test]
    fn satisfies() {
        let ds1: DigitSet = [1, 2, 5].into();
        let c1 = [Constraint::Count(3), Constraint::Sum(8)];
        // we can iterate directly over the array
        assert!(ds1.satisfies(c1));
        // we can iterate over a slice derived from the array
        assert!(ds1.satisfies(&c1[..]));

        // a vector of constraints this time
        let c2 =
            vec![Constraint::Excludes(Digit::D9.into()), Constraint::Includes(Digit::D1.into())];
        // iterate vector directly
        assert!(ds1.satisfies(c2.iter()));
        // make sure it's a slice
        assert!(ds1.satisfies(c2.as_slice()));
        // we can also just pass the vec by value
        assert!(ds1.satisfies(c2));

        // more tests
        assert!(DigitSet::empty().satisfies(Constraint::Sum(0)));
        assert!(DigitSet::empty().satisfies(Constraint::Count(0)));
        assert!(DigitSet::from([2, 3, 4]).satisfies(Constraint::Sum(9)));

        // includes/excludes with multiple digits
        assert!(ds1.satisfies(Constraint::Includes([1, 2].into())));
        assert!(!ds1.satisfies(Constraint::Includes([1, 3].into())));
        assert!(ds1.satisfies(Constraint::Excludes([7, 8].into())));
        assert!(!ds1.satisfies(Constraint::Excludes([1, 6].into())));
    }

    #[test]
    fn parse_sentence() {
        // explicit type so that this evaluates to slice refs rather than arrays
        let tests: &[(&str, &[Constraint])] = &[
            ("20 in 4", &[Constraint::Sum(20), Constraint::Count(4)]),
            ("10", &[Constraint::Sum(10)]),
            (
                "9 in 3 -1",
                &[Constraint::Sum(9), Constraint::Count(3), Constraint::Excludes(Digit::D1.into())],
            ),
        ];

        let mut cons = Vec::new();
        for (input, expected) in tests {
            cons.clear();
            super::parse_sentence(input, &mut cons).unwrap();
            assert_eq!(&cons, expected);
        }

        // failing tests
        cons.clear();
        assert_matches!(
            super::parse_sentence("1 in foo", &mut cons),
            Err(ParseConstraintError::NoMatch(_))
        );
        assert_matches!(
            super::parse_sentence("meow", &mut cons),
            Err(ParseConstraintError::NoMatch(_))
        );
        assert_matches!(
            super::parse_sentence("8 +0", &mut cons),
            Err(ParseConstraintError::InvalidDigit(ParseDigitError::InvalidCharacter))
        );

        // empty is allowed
        assert_matches!(super::parse_sentence("", &mut cons), Ok(_));
        assert_matches!(super::parse_sentence("  \t\n ", &mut cons), Ok(_));
    }
}
