use std::cmp::Ordering;
use std::fmt;
use std::iter::{FromIterator, Sum};
use std::ops;
use std::str::FromStr;
use std::sync::OnceLock;

use crate::constraint::Constraint;

/// A single valid Sudoku digit.
///
/// `Digit` is represented as a `u8` with the same value, so it can be trivially converted to any
/// integer type using `as` or [`From`].
///
/// ```
/// # use killercage::digit::Digit;
/// assert_eq!(Digit::D1 as u8, 1u8);
/// assert_eq!(Digit::D2 as u32, 2u32);
/// assert_eq!(i32::from(Digit::D3), 3i32);
/// ```
///
/// `Digit` can also be created from integer types and characters using [`TryFrom`], or from
/// strings using [`FromStr`].
///
/// ```
/// # use killercage::digit::Digit;
/// assert_eq!(Digit::try_from(5).unwrap(), Digit::D5);
/// assert_eq!(Digit::try_from('6').unwrap(), Digit::D6);
/// assert_eq!("7".parse::<Digit>().unwrap(), Digit::D7);
/// assert!(Digit::try_from(10).is_err());
/// assert!("foobar".parse::<Digit>().is_err());
/// ```
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

/// self-referential AsRef so that we can generically treat iterators over Digit and &Digit the same
impl AsRef<Digit> for Digit {
    #[inline]
    fn as_ref(&self) -> &Digit {
        self
    }
}

/// Errors that may occur when parsing a [`Digit`]
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

/// A set of non-repeating Sudoku digits.
///
/// [`DigitSet`] is a small, efficient, [`Copy`] type, therefore most methods accept `self` by
/// value rather than by reference.
///
/// Like standard Killer Sudoku rules, `DigitSet`s do not include repeating digits, and no ordering
/// is stored.
///
/// ```
/// # use killercage::digit::{Digit, DigitSet};
/// let mut set1 = DigitSet::empty();
/// set1.add(Digit::D1);
/// set1.add(Digit::D2);
/// set1.add(Digit::D3);
/// set1.add(Digit::D1);
/// set1.remove(Digit::D3);
///
/// let mut set2 = DigitSet::from([2, 1]);
///
/// assert_eq!(set1, set2);
/// ```
///
/// # Constructing
/// There are many ways to construct a DigitSet:
///  * Start with one of the constructors and then use the `add` and `remove` methods
///  * Collect from an iterator that yields `Digit` or `&Digit` (or any other `AsRef<Digit>`) items
///  * Convert from a slice or array of digits
///  * Convert from a slice or array of `u8`s. When converting this way, invalid values (outside
///    the range `1..=9`) are silently ignored.
///  * Use the `|` operator with `Digit`s or other `DigitSet`s
///  * From a string of digits like `"1234"`.
///
/// ```
/// # use killercage::digit::{Digit, DigitSet};
/// let mut set = DigitSet::empty();
/// set.add(Digit::D1);
/// set.add(Digit::D2);
///
/// let mut set = DigitSet::full();
/// set.remove(Digit::D7);
/// set.remove(Digit::D8);
///
/// let set: DigitSet = Digit::D1 | Digit::D2;
/// let set2 = set | Digit::D3;
/// let set3 = Digit::D3 | set;
/// assert_eq!(set2, set3);
///
/// let mut set = DigitSet::from(Digit::D1);
/// set |= Digit::D2;
/// assert_eq!(set, DigitSet::from([1, 2]));
///
/// let set: DigitSet = [1, 2, 3, 100].into();
/// assert_eq!(set, set2);
///
/// let odds_from_iter = Digit::ALL_DIGITS
///     .iter()
///     .filter(|d| (**d as u8) % 2 == 1)
///     .collect::<DigitSet>();
///
/// let odds_from_str: DigitSet = "13579".parse().unwrap();
/// let odds_or = Digit::D1 | Digit::D3 | Digit::D5 | Digit::D7 | Digit::D9;
/// assert_eq!(odds_from_iter, odds_from_str);
/// assert_eq!(odds_from_iter, odds_or);
/// ```
///
/// # Formatting
/// `DigitSet` implements [`Display`]. By default, digits are formatted with no space in between
/// them, and format's [fill/alignment] is respected. The empty set is formatted as `[empty]`. When
/// formatted with the alternate `#` mode, digits are rendered as a list.
///
/// [`Display`]: std::fmt::Display
/// [fill/alignment]: https://doc.rust-lang.org/std/fmt/index.html#fillalignment
///
/// ```
/// # use killercage::DigitSet;
/// let set = DigitSet::from([1, 2, 5]);
/// assert_eq!(format!("{set}"), "125");
/// assert_eq!(format!("{set:9}"), "125      ");
/// assert_eq!(format!("{set:>9}"), "      125");
/// assert_eq!(format!("{set:-<5}"), "125--");
/// assert_eq!(format!("{set:#}"), "[1, 2, 5]");
/// assert_eq!(format!("{set:?}"), "DigitSet([1, 2, 5])");
/// ```
///
/// # Ordering
/// `DigitSet` implements [`Ord`] and is ordered as followes:
///  * A smaller set (i.e. containing fewer digits) is always less than a larger set
///  * Two sets of equal length are sorted lexicographically
///  * Two sets are equal when they contain exactly the same digits.
///
/// ```
/// # use killercage::{Digit, DigitSet};
/// let set_789: DigitSet = [7, 8, 9].into();
/// let set_1345: DigitSet = [1, 3, 4, 5].into();
/// let set_1239: DigitSet = [1, 2, 3, 9].into();
/// assert!(set_789 < set_1345);
/// assert!(set_1239 < set_1345);
/// ```
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
    pub const fn empty() -> Self {
        Self { digits: 0 }
    }

    /// A digit set with all 9 digits included
    pub const fn full() -> Self {
        Self { digits: Self::VALID_DIGIT_MASK }
    }

    /// Get a slice of all possible `DigitSet`s.
    ///
    /// There are 512 possible sets (including the empty set), since each digit 1-9 is either
    /// included or excluded. The returned slice will be sorted by length first, and then
    /// lexicographically by the digits that are present.
    pub fn all_sets() -> &'static [DigitSet] {
        // Lazily initialize the list in a static OnceLock. Technically this "leaks" memory for the
        // rest of the program, but is's only a 1K allocation.
        static CELL: OnceLock<Vec<DigitSet>> = OnceLock::new();

        // auto-deref helps us out here (&Vec<DigitSet> -> &[DigitSet])
        CELL.get_or_init(|| {
            let mut vec = Vec::with_capacity(512);
            for n in 0..512 {
                // There's 9 used bits in DigitSet, we can just iterate through all those
                // integers. But since we start with bit 1 rather than bit 0, shift over 1.
                let ds = DigitSet { digits: n << 1 };
                ds.debug_check_valid();
                vec.push(ds);
            }
            vec.sort_unstable();
            vec
        })
    }

    /// Return an iterator of all possible `DigitSet`s
    ///
    /// This is a shortcut for `DigitSet::all_sets().iter().copied()`, which is exposed through the
    /// slightly unusual return type here. By returning `std`'s iterator types directly, the
    /// resulting iterator implements `DoubleEndedIterator`, `ExactSizeIterator`, and other traits
    /// that provide optimizations within Rust's iterator APIs.
    #[inline]
    pub fn iter_all() -> std::iter::Copied<std::slice::Iter<'static, DigitSet>> {
        DigitSet::all_sets().iter().copied()
    }

    /// Is the set empty?
    pub fn is_empty(self) -> bool {
        self.debug_check_valid();
        self.digits == 0
    }

    /// How many digits are present in this set?
    pub fn len(self) -> u8 {
        self.debug_check_valid();
        self.digits.count_ones() as u8
    }

    /// Add a digit to the set.
    pub fn add(&mut self, digit: Digit) {
        self.digits |= digit.mask_bit();
        self.debug_check_valid();
    }

    /// Remove a digit from the set.
    pub fn remove(&mut self, digit: Digit) {
        self.digits &= !digit.mask_bit();
        self.debug_check_valid();
    }

    /// Check whether a digit exists in this set.
    pub fn contains(self, digit: Digit) -> bool {
        self.debug_check_valid();
        (self.digits & digit.mask_bit()) != 0
    }

    /// Total value of all digits in this set.
    pub fn sum(self) -> u8 {
        self.iter().sum()
    }

    /// Iterate through the digits present in the set.
    ///
    /// Digits will be yielded in increasing order.
    pub fn iter(self) -> impl Iterator<Item = Digit> {
        Digit::ALL_DIGITS.into_iter().filter(move |d| self.contains(*d))
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

    /// Panic if any invalid bits are set, only when debug assertions are enabled.
    #[inline]
    fn debug_check_valid(self) {
        debug_assert_eq!(self.digits & !Self::VALID_DIGIT_MASK, 0);
    }
}

impl fmt::Display for DigitSet {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        /// Dumb workaround for formatting DigitSet with the alternate flag.
        /// I want something like "[1, 2, 3]" with the help of DebugList, but since the alternate
        /// flag is set in DigitSet::fmt, it gets printed by std's alternate-debug representation
        /// with newlines. Use this wrapper to obtain a DebugList in "normal" mode.
        struct DigitSetList(DigitSet);
        impl fmt::Display for DigitSetList {
            fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
                f.debug_list().entries(self.0.iter().map(u8::from)).finish()
            }
        }

        if f.alternate() {
            // Alternate format, display as a list
            write!(f, "{}", DigitSetList(*self))
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
        write!(f, "DigitSet({self:#})")
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

        // When the same length, do a lexicographic ordering
        for (ours, theirs) in self.iter().zip(rhs.iter()) {
            match ours.cmp(&theirs) {
                Ordering::Less => return Ordering::Less,
                Ordering::Greater => return Ordering::Greater,
                Ordering::Equal => (),
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

/// A single Digit converts into a DigitSet containing only that digit.
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

/// Construct a DigitSet from an array of `u8` values. Not all `u8` values represent valid sudoku
/// digits: out-of-range values will be silently ignored.
impl<const N: usize> From<[u8; N]> for DigitSet {
    fn from(arr: [u8; N]) -> Self {
        arr.into_iter().filter_map(Digit::try_new).collect()
    }
}

impl From<&[Digit]> for DigitSet {
    fn from(slice: &[Digit]) -> Self {
        slice.iter().copied().collect()
    }
}

/// Construct a DigitSet from a slice of `u8` values. Not all `u8` values represent valid sudoku
/// digits: out-of-range values will be silently ignored.
impl From<&[u8]> for DigitSet {
    fn from(slice: &[u8]) -> Self {
        slice.iter().copied().filter_map(Digit::try_new).collect()
    }
}

/// Construct a Digit set from an iterator that yields Digits.
impl<T> FromIterator<T> for DigitSet
where
    T: AsRef<Digit>,
{
    fn from_iter<I>(iter: I) -> Self
    where
        I: IntoIterator<Item = T>,
    {
        let mut set = DigitSet::empty();
        for digit in iter {
            set.add(*digit.as_ref());
        }
        set
    }
}

/// Return the set intersection between two DigitSets
impl ops::BitAnd for DigitSet {
    type Output = Self;
    fn bitand(self, rhs: DigitSet) -> DigitSet {
        DigitSet { digits: self.digits & rhs.digits }
    }
}

impl ops::BitAndAssign for DigitSet {
    fn bitand_assign(&mut self, rhs: DigitSet) {
        self.digits &= rhs.digits;
    }
}

/// Return the set union between two DigitSets
impl ops::BitOr for DigitSet {
    type Output = Self;
    fn bitor(self, rhs: DigitSet) -> DigitSet {
        DigitSet { digits: self.digits | rhs.digits }
    }
}

impl ops::BitOrAssign for DigitSet {
    fn bitor_assign(&mut self, rhs: DigitSet) {
        self.digits |= rhs.digits;
    }
}

/// Return the inverse of a DigitSet
impl ops::Not for DigitSet {
    type Output = Self;
    fn not(self) -> DigitSet {
        DigitSet { digits: (!self.digits) & Self::VALID_DIGIT_MASK }
    }
}

// BitOr interoperability between Digit and DigitSet

/// Digits can be or'd together to form a DigitSet
impl ops::BitOr<Digit> for Digit {
    type Output = DigitSet;

    #[inline]
    fn bitor(self, rhs: Digit) -> DigitSet {
        let mut set = DigitSet::empty();
        set.add(self);
        set.add(rhs);
        set
    }
}

/// Digits can be or'd with a DigitSet to produce a new DigitSet
impl ops::BitOr<DigitSet> for Digit {
    type Output = DigitSet;

    #[inline]
    fn bitor(self, mut set: DigitSet) -> DigitSet {
        set.add(self);
        set
    }
}

/// Digits can be or'd with a DigitSet to produce a new DigitSet
impl ops::BitOr<Digit> for DigitSet {
    type Output = DigitSet;

    #[inline]
    fn bitor(mut self, digit: Digit) -> DigitSet {
        self.add(digit);
        self
    }
}

/// Add a digit to the set. Equivalent to [`DigitSet::add`].
impl ops::BitOrAssign<Digit> for DigitSet {
    fn bitor_assign(&mut self, rhs: Digit) {
        self.add(rhs);
    }
}

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
        assert_matches!("123foo".parse::<DigitSet>(), Err(ParseDigitError::InvalidCharacter));
        assert_matches!("".parse::<DigitSet>(), Err(ParseDigitError::Empty));
    }

    #[test]
    fn digit_set_iter() {
        let ds = [1, 2, 3, 4, 5].into_iter().map(Digit::new).collect::<DigitSet>();
        assert_eq!(ds.sum(), 15);
        assert_eq!(ds.len(), 5);

        let ds = [9, 6, 3, 1].into_iter().map(Digit::new).collect::<DigitSet>();
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
        // is_sorted is unstable, implement it (naively) ourselves
        //assert!(DigitSet::all_sets().is_sorted());
        let all_sets: &[DigitSet] = DigitSet::all_sets();
        assert_eq!(all_sets.len(), 512);
        for i in 1..all_sets.len() {
            assert!(all_sets[i - 1] < all_sets[i]);
        }

        // make sure iterating all_sets is equivalent to iter_all
        for (a, b) in all_sets.iter().zip(DigitSet::iter_all()) {
            assert_eq!(*a, b);
        }

        // These tests were written for a custom AllSets iterator type, but they still pass when
        // exposing a slice and using std's iterator types.
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
