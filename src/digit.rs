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

impl FromStr for Digit {
    type Err = std::num::ParseIntError;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        let val: u8 = s.parse()?;
        // I want to use std's ParseIntError because it's got all the attributes we need, except
        // that there's no proper way to construct one directly. However, I can do a conversion
        // that I know will fail and return that as the error.
        if val < 1 {
            // IntErrorKind::NegOverflow
            Err("-300".parse::<i8>().unwrap_err())
        } else if val > 9 {
            // IntErrorKind::PosOverflow
            Err("300".parse::<u8>().unwrap_err())
        } else {
            // already checked that we're in range, can't panic
            Ok(Self::new(val))
        }
    }
}

macro_rules! impl_int_from_digit {
    ($($ty:ident),+) => {
        $(impl From<Digit> for $ty {
            #[inline]
            fn from(digit: Digit) -> $ty {
                (digit as u8) as $ty
            }
        })+
    };
}
impl_int_from_digit!(u8, u16, u32, u64, u128);
impl_int_from_digit!(i8, i16, i32, i64, i128);

impl Sum<Digit> for u8 {
    fn sum<I>(iter: I) -> Self
    where
        I: Iterator<Item = Digit>,
    {
        iter.map(u8::from).sum()
    }
}

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
    use super::{Digit, DigitSet};

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
    fn digit_set_parse() {
        use std::num::IntErrorKind;

        assert_eq!("1".parse::<Digit>(), Ok(Digit::D1));
        assert_eq!("9".parse::<Digit>(), Ok(Digit::D9));

        assert_eq!(
            "".parse::<Digit>().unwrap_err().kind(),
            &IntErrorKind::Empty
        );
        assert_eq!(
            "foo".parse::<Digit>().unwrap_err().kind(),
            &IntErrorKind::InvalidDigit
        );
        // negative numbers happen to give InvalidDigit rather than NegOverflow because '-' is
        // always an invalid character in an unsigned conversion (unlike '+' which can be optional)
        assert_eq!(
            "-1".parse::<Digit>().unwrap_err().kind(),
            &IntErrorKind::InvalidDigit
        );
        assert_eq!(
            "0".parse::<Digit>().unwrap_err().kind(),
            &IntErrorKind::NegOverflow
        );
        // out of range only for sudoku
        assert_eq!(
            "10".parse::<Digit>().unwrap_err().kind(),
            &IntErrorKind::PosOverflow
        );
        // out of range for u8
        assert_eq!(
            "1000".parse::<Digit>().unwrap_err().kind(),
            &IntErrorKind::PosOverflow
        );
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
