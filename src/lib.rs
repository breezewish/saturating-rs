//! Provides [`Saturating<T>`](`Saturating`), an intentionally-saturating arithmetic wrapper,
//! similar to [`std::num::Wrapping`].
//!
//! # Examples
//!
//! ```
//! use saturating::Saturating;
//!
//! let foo = Saturating(253u8);
//! let bar = Saturating(100u8);
//!
//! assert_eq!(std::u8::MAX, (foo + bar).0);
//! ```

#![no_std]

use core::fmt;
use core::iter;
use core::ops::*;

/// Provides intentionally-saturating arithmetic on `T`.
///
/// The underlying value can be retrieved through the `.0` index of the
/// `Saturating` tuple.
#[derive(PartialEq, Eq, PartialOrd, Ord, Clone, Copy, Default, Hash)]
#[repr(transparent)]
pub struct Saturating<T>(pub T);

impl<T: fmt::Debug> fmt::Debug for Saturating<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.0.fmt(f)
    }
}

impl<T: fmt::Display> fmt::Display for Saturating<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.0.fmt(f)
    }
}

impl<T: fmt::Binary> fmt::Binary for Saturating<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.0.fmt(f)
    }
}

impl<T: fmt::Octal> fmt::Octal for Saturating<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.0.fmt(f)
    }
}

impl<T: fmt::LowerHex> fmt::LowerHex for Saturating<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.0.fmt(f)
    }
}

impl<T: fmt::UpperHex> fmt::UpperHex for Saturating<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.0.fmt(f)
    }
}

// implements the unary operator "op &T"
// based on "op T" where T is expected to be `Copy`able
macro_rules! forward_ref_unop {
    (impl $imp:ident, $method:ident for $t:ty) => {
        impl $imp for &$t {
            type Output = <$t as $imp>::Output;

            #[inline]
            fn $method(self) -> <$t as $imp>::Output {
                $imp::$method(*self)
            }
        }
    };
}

// implements binary operators "&T op U", "T op &U", "&T op &U"
// based on "T op U" where T and U are expected to be `Copy`able
macro_rules! forward_ref_binop {
    (impl $imp:ident, $method:ident for $t:ty, $u:ty) => {
        impl<'a> $imp<$u> for &'a $t {
            type Output = <$t as $imp<$u>>::Output;

            #[inline]
            fn $method(self, other: $u) -> <$t as $imp<$u>>::Output {
                $imp::$method(*self, other)
            }
        }

        impl $imp<&$u> for $t {
            type Output = <$t as $imp<$u>>::Output;

            #[inline]
            fn $method(self, other: &$u) -> <$t as $imp<$u>>::Output {
                $imp::$method(self, *other)
            }
        }

        impl $imp<&$u> for &$t {
            type Output = <$t as $imp<$u>>::Output;

            #[inline]
            fn $method(self, other: &$u) -> <$t as $imp<$u>>::Output {
                $imp::$method(*self, *other)
            }
        }
    };
}

// implements "T op= &U", based on "T op= U"
// where U is expected to be `Copy`able
macro_rules! forward_ref_op_assign {
    (impl $imp:ident, $method:ident for $t:ty, $u:ty) => {
        impl $imp<&$u> for $t {
            #[inline]
            fn $method(&mut self, other: &$u) {
                $imp::$method(self, *other);
            }
        }
    };
}

macro_rules! saturating_impl {
    ($($t:ty)*) => ($(
        impl Add for Saturating<$t> {
            type Output = Saturating<$t>;

            #[inline]
            fn add(self, other: Saturating<$t>) -> Saturating<$t> {
                Saturating(self.0.saturating_add(other.0))
            }
        }
        forward_ref_binop! { impl Add, add for Saturating<$t>, Saturating<$t> }

        impl AddAssign for Saturating<$t> {
            #[inline]
            fn add_assign(&mut self, other: Saturating<$t>) {
                *self = *self + other;
            }
        }
        forward_ref_op_assign! { impl AddAssign, add_assign for Saturating<$t>, Saturating<$t> }

        impl Sub for Saturating<$t> {
            type Output = Saturating<$t>;

            #[inline]
            fn sub(self, other: Saturating<$t>) -> Saturating<$t> {
                Saturating(self.0.saturating_sub(other.0))
            }
        }
        forward_ref_binop! { impl Sub, sub for Saturating<$t>, Saturating<$t> }

        impl SubAssign for Saturating<$t> {
            #[inline]
            fn sub_assign(&mut self, other: Saturating<$t>) {
                *self = *self - other;
            }
        }
        forward_ref_op_assign! { impl SubAssign, sub_assign for Saturating<$t>, Saturating<$t> }

        impl Mul for Saturating<$t> {
            type Output = Saturating<$t>;

            #[inline]
            fn mul(self, other: Saturating<$t>) -> Saturating<$t> {
                Saturating(self.0.saturating_mul(other.0))
            }
        }
        forward_ref_binop! { impl Mul, mul for Saturating<$t>, Saturating<$t> }

        impl MulAssign for Saturating<$t> {
            #[inline]
            fn mul_assign(&mut self, other: Saturating<$t>) {
                *self = *self * other;
            }
        }
        forward_ref_op_assign! { impl MulAssign, mul_assign for Saturating<$t>, Saturating<$t> }

        impl Neg for Saturating<$t> {
            type Output = Self;
            #[inline]
            fn neg(self) -> Self {
                Saturating(0) - self
            }
        }
        forward_ref_unop! { impl Neg, neg for Saturating<$t> }

        impl iter::Sum for Saturating<$t> {
            fn sum<I: Iterator<Item = Self>>(iter: I) -> Self {
                iter.fold(Saturating(0), Add::add)
            }
        }

        impl<'a> iter::Sum<&'a Saturating<$t>> for Saturating<$t> {
            fn sum<I: Iterator<Item = &'a Self>>(iter: I) -> Self {
                iter.fold(Saturating(0), Add::add)
            }
        }

        impl iter::Product for Saturating<$t> {
            fn product<I: Iterator<Item = Self>>(iter: I) -> Self {
                iter.fold(Saturating(1), Mul::mul)
            }
        }

        impl<'a> iter::Product<&'a Saturating<$t>> for Saturating<$t> {
            fn product<I: Iterator<Item = &'a Self>>(iter: I) -> Self {
                iter.fold(Saturating(1), Mul::mul)
            }
        }
    )*)
}

saturating_impl! { usize u8 u16 u32 u64 u128 isize i8 i16 i32 i64 i128 }
