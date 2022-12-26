use std::cmp::Ordering;
use std::fmt;
use std::iter::{FromIterator, Sum};
use std::ops;
use std::str::FromStr;

use crate::constraint::Constraint;

/// A single valid Sudoku digit.
#[repr(u8)]
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub enum Digit {
    D1 = 1,
    D2,
    D3,
    D4,
    D5,
    D6,
    D7,
    D8,
    D9,
}

impl Digit {
    /// All 9 digits, in an array that you can iterate through or whatever
    pub const ALL_DIGITS: [Digit; 9] = [
        Digit::D1,
        Digit::D2,
        Digit::D3,
        Digit::D4,
        Digit::D5,
        Digit::D6,
        Digit::D7,
        Digit::D8,
        Digit::D9,
    ];

    /// Create a new Digit from some numeric value.
    ///
    /// Panics if the value is out of range (see `Digit::try_new`).
    pub fn new(val: impl TryInto<u8>) -> Self {
        Self::try_new(val).expect("value is out of range for Digit")
    }

    /// Try to create a new Digit from some numeric value.
    ///
    /// Returns None if the value can't be converted to u8 successfully, or if the resulting value
    /// is outside of the range 1..=9.
    pub fn try_new(val: impl TryInto<u8>) -> Option<Self> {
        use Digit::*;
        Some(match val.try_into().ok()? {
            1 => D1,
            2 => D2,
            3 => D3,
            4 => D4,
            5 => D5,
            6 => D6,
            7 => D7,
            8 => D8,
            9 => D9,
            _ => return None,
        })
    }

    /// Convert a [`char`] (`'1'..='9'`) into a `Digit`
    pub fn from_char(ch: char) -> Option<Self> {
        match ch {
            '1' => Some(Digit::D1),
            '2' => Some(Digit::D2),
            '3' => Some(Digit::D3),
            '4' => Some(Digit::D4),
            '5' => Some(Digit::D5),
            '6' => Some(Digit::D6),
            '7' => Some(Digit::D7),
            '8' => Some(Digit::D8),
            '9' => Some(Digit::D9),
            _ => None,
        }
    }

    #[inline]
    fn mask_bit(self) -> u16 {
        1u16 << (self as u8)
    }

    #[inline]
    fn value(self) -> u8 {
        self as u8
    }
}

impl fmt::Display for Digit {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        self.value().fmt(f)
    }
}

impl From<Digit> for char {
    fn from(digit: Digit) -> char {
        use Digit::*;
        match digit {
            D1 => '1',
            D2 => '2',
            D3 => '3',
            D4 => '4',
            D5 => '5',
            D6 => '6',
            D7 => '7',
            D8 => '8',
            D9 => '9',
        }
    }
}

impl TryFrom<char> for Digit {
    type Error = ParseDigitError;

    fn try_from(ch: char) -> Result<Self, Self::Error> {
        Self::from_char(ch).ok_or(ParseDigitError::InvalidCharacter)
    }
}

#[derive(Debug, Clone, thiserror::Error)]
#[non_exhaustive]
pub enum ParseDigitError {
    /// String was empty
    #[error("Empty string")]
    Empty,

    /// Extra characters found
    #[error("Extra characters in string")]
    TooLong,

    /// Non-digit character encountered
    #[error("Non-digit character")]
    InvalidCharacter,

    /// Out of range number
    #[error("Out of range numeric value")]
    OutOfRange,
}

impl FromStr for Digit {
    type Err = ParseDigitError;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        match s {
            "1" => Ok(Digit::D1),
            "2" => Ok(Digit::D2),
            "3" => Ok(Digit::D3),
            "4" => Ok(Digit::D4),
            "5" => Ok(Digit::D5),
            "6" => Ok(Digit::D6),
            "7" => Ok(Digit::D7),
            "8" => Ok(Digit::D8),
            "9" => Ok(Digit::D9),
            _ => Err(match s.len() {
                0 => ParseDigitError::Empty,
                1 => ParseDigitError::InvalidCharacter,
                _ => ParseDigitError::TooLong,
            }),
        }
    }
}

// impl "From<Digit> for int", "TryFrom<int> for Digit", and "Sum<Digit> for int"
// for all the unsigned and signed primitive int types. Do this with a macro because due to blanket
// impls and coherence rules, it's basically impossible to write any generic TryFrom impl.
macro_rules! impl_digit_for_ints {
    ($($ty:ident),+) => {
        $(
            impl From<Digit> for $ty {
                #[inline]
                fn from(digit: Digit) -> $ty {
                    (digit as u8) as $ty
                }
            }

            impl TryFrom<$ty> for Digit {
                type Error = ParseDigitError;

                #[inline]
                fn try_from(int: $ty) -> Result<Digit, ParseDigitError> {
                    Digit::try_new(int).ok_or(ParseDigitError::OutOfRange)
                }
            }

            impl Sum<Digit> for $ty {
                fn sum<I: Iterator<Item = Digit>>(iter: I) -> $ty {
                    iter.map($ty::from).sum()
                }
            }
        )+
    };
}
impl_digit_for_ints!(u8, u16, u32, u64, u128);
impl_digit_for_ints!(i8, i16, i32, i64, i128);

/// A set of non-repeating Sudoku digits
#[derive(Clone, Copy, Default)]
pub struct DigitSet {
    /// A bitmask of which digits are present. Invariant: only bits 1-9 (inclusive, zero-indexed)
    /// will ever be set.
    digits: u16,
}

impl DigitSet {
    /// Bitmask of all valid digits
    const VALID_DIGIT_MASK: u16 = 0b0000_0011_1111_1110;

    /// An empty set with no digits set.
    pub fn empty() -> Self {
        Self { digits: 0 }
    }

    /// A digit set with all 9 digits included
    pub fn full() -> Self {
        Self {
            digits: Self::VALID_DIGIT_MASK,
        }
    }

    /// Return an iterator of all possible `DigitSet`s
    #[inline]
    pub fn iter_all() -> AllSets {
        AllSets::new()
    }

    /// Is the set empty?
    pub fn is_empty(self) -> bool {
        self.digits == 0
    }

    /// How many digits are present in this set?
    pub fn len(self) -> u8 {
        self.digits.count_ones() as u8
    }

    /// Add a digit to the set. Does nothing if the digit already exists
    pub fn add(&mut self, digit: Digit) {
        self.digits |= digit.mask_bit()
    }

    /// Remove a digit from the set. Does nothing if the digit already wasn't included.
    pub fn remove(&mut self, digit: Digit) {
        self.digits &= !digit.mask_bit()
    }

    /// Check whether a digit exists in this set.
    pub fn contains(self, digit: Digit) -> bool {
        (self.digits & digit.mask_bit()) != 0
    }

    /// Total of all digits in this set.
    pub fn sum(self) -> u8 {
        self.iter().sum()
    }

    /// Iterate through the digits present in the set.
    pub fn iter(self) -> impl Iterator<Item = Digit> {
        Digit::ALL_DIGITS
            .into_iter()
            .filter(move |d| self.contains(*d))
    }

    /// Check whether this DigitSet satisfies all of the given constraints.
    ///
    /// This function takes an iterator, which can be fullfilled by an array of Constraints,
    /// a slice of Constraints, a single Constraint, or any other iterator that yields Constraint
    /// or &Constraint.
    pub fn satisfies<I>(self, iter: I) -> bool
    where
        I: IntoIterator,
        I::Item: AsRef<Constraint>,
    {
        iter.into_iter().all(|c| c.as_ref().matches(self))
    }

    /// Panic if any invalid bits are set
    #[inline]
    fn debug_check_valid(self) {
        debug_assert_eq!(self.digits & !Self::VALID_DIGIT_MASK, 0);
    }
}

impl fmt::Display for DigitSet {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        if f.alternate() {
            // alternate format, display as a list
            f.debug_list().entries(self.iter().map(u8::from)).finish()
        } else {
            let mut s = String::with_capacity(9);
            if self.is_empty() {
                s.push_str("[empty]");
            } else {
                for digit in self.iter() {
                    s.push(char::from(digit));
                }
            }
            f.pad(&s)
        }
    }
}

impl fmt::Debug for DigitSet {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "DigitSet({self})")
    }
}

impl PartialEq for DigitSet {
    fn eq(&self, rhs: &DigitSet) -> bool {
        self.debug_check_valid();
        rhs.debug_check_valid();
        self.digits == rhs.digits
    }
}

impl Eq for DigitSet {}

impl Ord for DigitSet {
    fn cmp(&self, rhs: &DigitSet) -> Ordering {
        if self == rhs {
            return Ordering::Equal;
        }

        // a smaller set is always less than a bigger set
        match self.len().cmp(&rhs.len()) {
            Ordering::Less => return Ordering::Less,
            Ordering::Greater => return Ordering::Greater,
            Ordering::Equal => (),
        }

        // When the same length, do a lexographic ordering
        for digit in Digit::ALL_DIGITS {
            match (self.contains(digit), rhs.contains(digit)) {
                // we have a digit they don't, we're less
                (true, false) => return Ordering::Less,
                // they have it, we're greater
                (false, true) => return Ordering::Greater,
                // we both do or don't have the digit, keep looking
                _ => (),
            }
        }

        // If we get here, they should be Equal, which was already checked.
        if cfg!(debug_assertions) {
            // panic in debug mode
            unreachable!("Broken Ord::cmp equality check")
        } else {
            // just go with Equal in release mode
            Ordering::Equal
        }
    }
}

impl PartialOrd for DigitSet {
    fn partial_cmp(&self, rhs: &DigitSet) -> Option<Ordering> {
        Some(self.cmp(rhs))
    }
}

impl From<Digit> for DigitSet {
    #[inline]
    fn from(digit: Digit) -> Self {
        let mut set = DigitSet::empty();
        set.add(digit);
        set
    }
}

impl FromStr for DigitSet {
    type Err = ParseDigitError;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        if s.is_empty() {
            // Special case: an empty string is an error.
            Err(ParseDigitError::Empty)
        } else {
            s.chars().try_fold(DigitSet::empty(), |mut ds, ch| {
                ds.add(Digit::try_from(ch)?);
                Ok(ds)
            })
        }
    }
}

// To avoid really broad generic bounds, we only impl From for arrays and slices of Digit and u8,
// rather than for any `T: TryInto<u8>` that could be passed to `Digit::try_new`. Also the u8 from
// here will silently ignore out-of-range u8 values.

impl<const N: usize> From<[Digit; N]> for DigitSet {
    fn from(arr: [Digit; N]) -> Self {
        arr.into_iter().collect()
    }
}

impl<const N: usize> From<[u8; N]> for DigitSet {
    /// Construct a DigitSet from an array of `u8` values. Not all `u8` values represent valid
    /// sudoku digits: out-of-range values will be silently ignored.
    fn from(arr: [u8; N]) -> Self {
        arr.into_iter().filter_map(Digit::try_new).collect()
    }
}

impl From<&[Digit]> for DigitSet {
    fn from(slice: &[Digit]) -> Self {
        slice.iter().copied().collect()
    }
}

impl From<&[u8]> for DigitSet {
    /// Construct a DigitSet from a slice of `u8` values. Not all `u8` values represent valid
    /// sudoku digits: out-of-range values will be silently ignored.
    fn from(slice: &[u8]) -> Self {
        slice.iter().copied().filter_map(Digit::try_new).collect()
    }
}

impl FromIterator<Digit> for DigitSet {
    fn from_iter<I>(iter: I) -> Self
    where
        I: IntoIterator<Item = Digit>,
    {
        let mut set = DigitSet::empty();
        for digit in iter {
            set.add(digit)
        }
        set
    }
}

impl ops::BitAnd for DigitSet {
    type Output = Self;
    fn bitand(self, rhs: DigitSet) -> DigitSet {
        DigitSet {
            digits: self.digits & rhs.digits,
        }
    }
}

impl ops::BitAndAssign for DigitSet {
    fn bitand_assign(&mut self, rhs: DigitSet) {
        self.digits &= rhs.digits;
    }
}

impl ops::BitOr for DigitSet {
    type Output = Self;
    fn bitor(self, rhs: DigitSet) -> DigitSet {
        DigitSet {
            digits: self.digits | rhs.digits,
        }
    }
}

impl ops::BitOrAssign for DigitSet {
    fn bitor_assign(&mut self, rhs: DigitSet) {
        self.digits |= rhs.digits;
    }
}

impl ops::Not for DigitSet {
    type Output = Self;
    fn not(self) -> DigitSet {
        DigitSet {
            digits: (!self.digits) & Self::VALID_DIGIT_MASK,
        }
    }
}

/// Iterator that yields all possible digit sets.
///
/// The iteration order is unspecified, and will not necessarily be sorted.
#[derive(Debug, Clone, Default)]
pub struct AllSets {
    /// Counter from 0 (empty set) to 511 (all 9 digits included).
    pos: u16,
}

impl AllSets {
    /// Create a new Iterator over all possible [`DigitSet`]s
    pub fn new() -> Self {
        Default::default()
    }
}

impl Iterator for AllSets {
    type Item = DigitSet;

    fn next(&mut self) -> Option<Self::Item> {
        if self.pos >= 512 {
            None
        } else {
            // pos counts from 0-512, but DigitSet starts using bit position 1 so shift over
            let ds = DigitSet {
                digits: self.pos << 1,
            };
            ds.debug_check_valid();
            self.pos += 1;
            Some(ds)
        }
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        // we always know exactly how many elements will be yielded
        let count = 512u16.saturating_sub(self.pos) as usize;
        (count, Some(count))
    }
}

// n.b. relies on size_hint being correct
impl ExactSizeIterator for AllSets {}

#[cfg(test)]
mod tests {
    use super::{Digit, DigitSet, ParseDigitError};

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
    fn digit_new() {
        use Digit::*;
        assert_eq!(Digit::new(1u64), D1);
        assert_eq!(Digit::try_new(0u8), None);
        assert_eq!(Digit::try_new(9), Some(D9));
        assert_eq!(Digit::try_new(1234i32), None);
    }

    #[test]
    fn digit_value() {
        use Digit::*;
        assert_eq!(D1 as u8, 1);
        assert_eq!(D2 as u8, 2);
        assert_eq!(D3 as u8, 3);
        assert_eq!(D4 as u8, 4);
        assert_eq!(D5 as u8, 5);
        assert_eq!(D6 as u8, 6);
        assert_eq!(D7 as u8, 7);
        assert_eq!(D8 as u8, 8);
        assert_eq!(D9 as u8, 9);

        assert_eq!(u64::from(D5), 5_u64);
        assert_eq!(i128::from(D8), 8_i128);

        // check that the iterator sum trait works
        assert_eq!(Digit::ALL_DIGITS.into_iter().sum::<u8>(), 45);
        assert_eq!(Digit::ALL_DIGITS.into_iter().sum::<i32>(), 45);
        assert_eq!(Digit::ALL_DIGITS.into_iter().sum::<u64>(), 45);
    }

    #[test]
    fn digit_set_basic() {
        use Digit::*;
        let mut ds = DigitSet::empty();
        ds.add(D1);
        ds.add(D2);
        ds.add(D5);

        assert_eq!(ds.len(), 3);
        assert_eq!(ds.sum(), 8);
        assert!(ds.contains(D2));
        assert!(!ds.contains(D3));

        ds.remove(D1);
        assert!(!ds.contains(D1));
        ds.remove(D1);
        assert!(!ds.contains(D1));
    }

    #[test]
    fn digit_parse() {
        use std::str::FromStr;

        assert_matches!("1".parse::<Digit>(), Ok(Digit::D1));
        assert_matches!("2".parse::<Digit>(), Ok(Digit::D2));
        assert_matches!("3".parse::<Digit>(), Ok(Digit::D3));
        assert_matches!("4".parse::<Digit>(), Ok(Digit::D4));
        assert_matches!("5".parse::<Digit>(), Ok(Digit::D5));
        assert_matches!("6".parse::<Digit>(), Ok(Digit::D6));
        assert_matches!("7".parse::<Digit>(), Ok(Digit::D7));
        assert_matches!("8".parse::<Digit>(), Ok(Digit::D8));
        assert_matches!("9".parse::<Digit>(), Ok(Digit::D9));

        assert_matches!(Digit::from_str(""), Err(ParseDigitError::Empty));
        assert_matches!(Digit::from_str("foo"), Err(ParseDigitError::TooLong));
        assert_matches!(Digit::from_str("10"), Err(ParseDigitError::TooLong));
        assert_matches!(Digit::from_str("0"), Err(ParseDigitError::InvalidCharacter));

        let evens: DigitSet = [2, 4, 6, 8].into();
        assert_eq!("2468".parse::<DigitSet>().unwrap(), evens);
        assert_eq!("8642".parse::<DigitSet>().unwrap(), evens);
        assert_matches!(
            "123foo".parse::<DigitSet>(),
            Err(ParseDigitError::InvalidCharacter)
        );
        assert_matches!("".parse::<DigitSet>(), Err(ParseDigitError::Empty));
    }

    #[test]
    fn digit_set_iter() {
        let ds = [1, 2, 3, 4, 5]
            .into_iter()
            .map(Digit::new)
            .collect::<DigitSet>();
        assert_eq!(ds.sum(), 15);
        assert_eq!(ds.len(), 5);

        let ds = [9, 6, 3, 1]
            .into_iter()
            .map(Digit::new)
            .collect::<DigitSet>();
        assert_eq!(ds.sum(), 19);
        assert_eq!(ds.len(), 4);

        // we can iterate over the digit set and get integers back out. They're always sorted
        let v = ds.iter().map(u32::from).collect::<Vec<u32>>();
        assert_eq!(v, &[1, 3, 6, 9]);
    }

    #[test]
    fn digit_set_ops() {
        use Digit::*;

        let evens: DigitSet = [D2, D4, D6, D8].into();
        let odds: DigitSet = [1, 3, 5, 7, 9].into();
        let all = evens | odds;
        assert_eq!(all.sum(), 45);

        let mut ds: DigitSet = [1, 2, 3].into();
        ds |= DigitSet::from([D4]);
        assert_eq!(ds, [1, 2, 3, 4].into());

        let inv = !ds;
        assert_eq!(inv, [5, 6, 7, 8, 9].into());
    }

    #[test]
    fn allsets_iter() {
        // verify that the AllDigits size hint is implemented properly
        // ExactsizeIterator::is_empty() is unstable for now, can be tested with Nightly.
        let mut count = 0;
        let mut it = DigitSet::iter_all();
        assert_eq!(it.size_hint(), (512, Some(512)));
        assert_eq!(it.len(), 512);
        //assert!(!it.is_empty());

        for _ in 0..256 {
            let _ = it.next();
            count += 1;
        }
        assert_eq!(count, 256);
        assert_eq!(it.size_hint(), (256, Some(256)));
        assert_eq!(it.len(), 256);
        //assert!(!it.is_empty());

        for _ in it.by_ref() {
            count += 1;
        }
        assert_eq!(count, 512);
        assert_eq!(it.size_hint(), (0, Some(0)));
        assert_eq!(it.len(), 0);
        //assert!(it.is_empty());
    }
}
