use std::fmt;
use std::num::ParseIntError;
use std::str::FromStr;

use crate::digit::Digit;

/// regex macro, example in once_cell's docs
#[macro_export]
macro_rules! regex {
    ($re:literal $(,)?) => {{
        static RE: once_cell::sync::OnceCell<regex::Regex> = once_cell::sync::OnceCell::new();
        RE.get_or_init(|| regex::Regex::new($re).unwrap())
    }};
}

#[derive(Debug, Clone)]
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
    use crate::digit::Digit;

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
}
