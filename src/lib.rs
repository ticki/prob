//! Convinience types for calculating probabilities of independent events.
//!
//! This crate provides a simple type which represents a probability of an isolated event
//! happening.
//!
//! It intergrates nicely with the Rust syntax by overloading various operations.
//!
//! # Example
//!
//! ```rust
//! use prob::Probability;
//!
//! let p1 = Probability(0.5);
//! let p2 = Probability(0.5);
//!
//! let Probability(and) = p1 & p2;
//! let Probability(or)  = p1 | p2;
//! let Probability(xor) = p1 ^ p2;
//!
//! assert_eq!(or,  0.75);
//! assert_eq!(and, 0.25);
//! assert_eq!(xor, 0.5);
//! ```

#![warn(missing_docs)]

extern crate num;

use num::Num;
use std::ops;

/// An independent probability.
///
/// This represents some probability of some abstract, isolated event occuring. Note that the even
/// have to be isolated (independent of any other event) for the operations to be correct. As such,
/// you shouldn't do calculations with conditional events. Stronger methods needs to be used for
/// this.
///
/// This newtype simply wraps some numeral type and provides it with operations:
///
/// - `&` for **independent and**.
/// - `|` for **independent or**.
/// - `^` for **independent mutual exclusivity**.
/// - `!` for **inverse probability**.
#[derive(Copy, Clone, PartialEq, Eq, Debug)]
pub struct Probability<T: Num>(pub T);

impl<T: Num> Probability<T> {
    /// The probability representing a "almost certain" condition.
    ///
    /// "Almost certain" (a.c.) should not be equated with "certain", because something can be
    /// practically certain, but not impossible to fail. For example, pick a random natural number
    /// from an uniform distribution. Not picking a specific number would be almost certain, but
    /// it is not impossible, because an argument for impossibility could be applied to any number.
    ///
    /// For practical purposes, though, there is no difference between certain and almost certain.
    pub fn certain() -> Probability<T> {
        Probability(T::one())
    }

    /// The inverse of an "almost certain" condition (almost never).
    pub fn never() -> Probability<T> {
        !Probability::certain()
    }

    /// Half the probability.
    pub fn half(self) -> Probability<T> {
        Probability(self.0 / (T::one() + T::one()))
    }

    /// A fifty-fifty probability (0.5).
    pub fn fifty() -> Probability<T> {
        Probability::certain().half()
    }

    /// 'or' for mutually exclusive events
    pub fn disjointed_or(self, rhs: Probability<T>) -> Probability<T> {
        Probability(self.0 + rhs.0)
    }
}

impl<T: Num> ops::Not for Probability<T> {
    type Output = Probability<T>;

    fn not(self) -> Probability<T> {
        Probability(T::one() - self.0)
    }
}

impl<T: Num> ops::BitAnd for Probability<T> {
    type Output = Probability<T>;

    fn bitand(self, rhs: Probability<T>) -> Probability<T> {
        Probability(self.0 * rhs.0)
    }
}

impl<T: Num + Copy> ops::BitOr for Probability<T> {
    type Output = Probability<T>;

    fn bitor(self, rhs: Probability<T>) -> Probability<T> {
        Probability(self.0 + rhs.0 - self.0 * rhs.0)
    }
}

impl<T: Num + Copy> ops::BitXor for Probability<T> {
    type Output = Probability<T>;

    fn bitxor(self, rhs: Probability<T>) -> Probability<T> {
        (self & !rhs).disjointed_or(rhs & !self)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    type F32Probability = Probability<f32>;

    #[test]
    fn and() {
        assert_eq!(F32Probability::fifty() & F32Probability::fifty(), F32Probability::fifty().half());
        assert_eq!(F32Probability::certain() & F32Probability::certain(), F32Probability::certain());
        assert_eq!(F32Probability::never() & F32Probability::certain(), F32Probability::never());
        assert_eq!(F32Probability::never() & F32Probability::never(), F32Probability::never());
        assert_eq!(F32Probability::fifty() & F32Probability::fifty(), Probability::fifty().half());
    }

    #[test]
    fn or() {
        assert_eq!(F32Probability::fifty() | F32Probability::never(), F32Probability::fifty());
        assert_eq!(F32Probability::fifty() | F32Probability::never(), F32Probability::fifty());
        assert_eq!(F32Probability::never() | F32Probability::never(), F32Probability::never());
        assert_eq!(F32Probability::certain() | F32Probability::certain(), F32Probability::certain());
        assert_eq!(Probability::fifty() | Probability::fifty(), Probability(0.75));
    }

    #[test]
    fn xor() {
        assert_eq!(F32Probability::fifty() ^ F32Probability::never(), F32Probability::fifty());
        assert_eq!(F32Probability::fifty() ^ F32Probability::never(), F32Probability::fifty());
        assert_eq!(F32Probability::never() ^ F32Probability::never(), F32Probability::never());
        assert_eq!(F32Probability::certain() ^ F32Probability::certain(), F32Probability::never());
        assert_eq!(F32Probability::certain() ^ F32Probability::never(), F32Probability::certain());
        assert_eq!(F32Probability::fifty() ^ F32Probability::fifty(), F32Probability::fifty());
    }

    #[test]
    fn not() {
        assert_eq!(!F32Probability::fifty(), F32Probability::fifty());
        assert_eq!(!F32Probability::fifty(), F32Probability::fifty());
        assert_eq!(!Probability(0.75), Probability::fifty().half());
    }
}
