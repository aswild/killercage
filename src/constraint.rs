use std::fmt;
use std::num::ParseIntError;
use std::str::FromStr;

use crate::digit::{Digit, DigitSet};

/// regex macro, example in once_cell's docs
#[macro_export]
macro_rules! regex {
    ($re:literal $(,)?) => {{
        static RE: once_cell::sync::OnceCell<regex::Regex> = once_cell::sync::OnceCell::new();
        RE.get_or_init(|| regex::Regex::new($re).unwrap())
    }};
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[non_exhaustive]
pub enum Constraint {
    /// The set must have a given sum (exactly)
    Sum(u8),
    /// The set must have this many digits
    Count(u8),
    /// The set must include this digit
    Contains(Digit),
    /// The set must not include this digit
    Excludes(Digit),
}

impl Constraint {
    /// Check whether a [`DigitSet`] satisfies this constraint.
    pub fn matches(self, set: DigitSet) -> bool {
        match self {
            Constraint::Sum(sum) => set.sum() == sum,
            Constraint::Count(count) => set.len() == count,
            Constraint::Contains(digit) => set.contains(digit),
            Constraint::Excludes(digit) => !set.contains(digit),
        }
    }
}

impl fmt::Display for Constraint {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Constraint::Sum(sum) => write!(f, "={sum}"),
            Constraint::Count(count) => write!(f, "in {count}"),
            Constraint::Contains(digit) => write!(f, "+{digit}"),
            Constraint::Excludes(digit) => write!(f, "-{digit}"),
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
    type Err = ParseError;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        let s = s.trim();
        let re = regex!(r"^(?P<prefix>\S*?)\s*(?P<number>\d+)$");
        let caps = re.captures(s).ok_or(ParseError::NoMatch)?;
        let num = caps.name("number").unwrap().as_str();
        let op = caps.name("prefix").unwrap().as_str();

        match op {
            "+" => Ok(Self::Contains(num.parse::<Digit>()?)),
            "-" => Ok(Self::Excludes(num.parse::<Digit>()?)),
            "" | "=" => Ok(Self::Sum(num.parse::<u8>()?)),
            "in" => Ok(Self::Count(num.parse::<u8>()?)),
            other => Err(ParseError::UnknownOperator(other.to_owned())),
        }
    }
}

#[derive(Debug, Clone)]
pub enum ParseError {
    /// A digit value was out of range
    InvalidDigit(ParseIntError),
    /// Unknown constraint name/operator
    UnknownOperator(String),
    /// Couldn't even find a number, what are you even doing?
    NoMatch,
}

impl fmt::Display for ParseError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Self::InvalidDigit(err) => write!(f, "Invalid number: {err}"),
            Self::UnknownOperator(s) => write!(f, "Unknown constraint operator: {s:?}"),
            Self::NoMatch => f.write_str("Input didn't match format"),
        }
    }
}

impl From<ParseIntError> for ParseError {
    fn from(val: ParseIntError) -> Self {
        Self::InvalidDigit(val)
    }
}

impl std::error::Error for ParseError {
    fn source(&self) -> Option<&(dyn std::error::Error + 'static)> {
        match self {
            Self::InvalidDigit(err) => Some(err),
            _ => None,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::{Constraint, ParseError};
    use crate::digit::{Digit, DigitSet};

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
        use std::num::IntErrorKind;
        use std::str::FromStr;

        assert_matches!(Constraint::from_str("=10"), Ok(Constraint::Sum(10)));
        assert_matches!(
            Constraint::from_str("+9"),
            Ok(Constraint::Contains(Digit::D9))
        );
        assert_matches!(
            Constraint::from_str("-2"),
            Ok(Constraint::Excludes(Digit::D2))
        );
        assert_matches!(Constraint::from_str("in 5"), Ok(Constraint::Count(5)));
        assert_matches!(Constraint::from_str("  in5"), Ok(Constraint::Count(5)));
        assert_matches!(Constraint::from_str("15"), Ok(Constraint::Sum(15)));

        assert_matches!(
            Constraint::from_str("+10"),
            Err(ParseError::InvalidDigit(err)) if err.kind() == &IntErrorKind::PosOverflow,
        );
    }

    #[test]
    fn satisfies() {
        let ds1: DigitSet = [1, 2, 5].into();
        let c1 = [Constraint::Count(3), Constraint::Sum(8)];
        // we can iterate directly over the array
        assert!(ds1.satisfies_all(c1));
        // we can iterate over a slice derived from the array
        assert!(ds1.satisfies_all(&c1[..]));

        // a vector of constraints this time
        let c2 = vec![
            Constraint::Excludes(Digit::D9),
            Constraint::Contains(Digit::D1),
        ];
        // iterate vector directly
        assert!(ds1.satisfies_all(c2.iter()));
        // make sure it's a slice
        assert!(ds1.satisfies_all(c2.as_slice()));
        // we can also just pass the vec by value
        assert!(ds1.satisfies_all(c2));

        // more tests
        assert!(DigitSet::empty().satisfies(Constraint::Sum(0)));
        assert!(DigitSet::empty().satisfies(Constraint::Count(0)));
        assert!(DigitSet::from([2, 3, 4]).satisfies_all(Constraint::Sum(9)));
    }
}
