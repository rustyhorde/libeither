// Copyright (c) 2018 libeither developers
//
// Licensed under the Apache License, Version 2.0
// <LICENSE-APACHE or http://www.apache.org/licenses/LICENSE-2.0> or the MIT
// license <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. All files in the project carrying such notice may not be copied,
// modified, or distributed except according to those terms.

//! Either struct
//!
//! This is heavily influenced by the [Either](https://docs.rs/either/latest)
//! enum library.  A struct version was required to be serializable to/from TOML,
//! where enums are not valid.  If you don't need struct specific
//! serialization, you may want to use the enum Either instead.
//!
//! # Features
//! * `serde` - Enable serialization (on by default)
//! * `use_std` - Enable the standard library (on by default)
//! * `unstable` - Enable unstable options (nightly only, off by default)
//!
//! # Examples
//! ```
//! # use failure::Fallible;
//! # use libeither::Either;
//! #
//! # fn main() -> Fallible<()> {
//! let mut left: Either<&str, &str> = Either::new_left("lefty");
//!
//! // Check for left or right
//! assert!(left.is_left());
//! assert!(!left.is_right());
//!
//! // Check a reference to the contained value.
//! assert_eq!(left.left_ref()?, &"lefty");
//! assert!(left.right_ref().is_err());
//!
//! // Mutate the contained value.
//! *(left.left_mut()?) = "left handed";
//! assert_eq!(left.left_ref()?, &"left handed");
//! assert!(left.right_mut().is_err());
//!
//! // Flip the value
//! let flipped = left.flip()?;
//! assert_eq!(flipped.right_ref()?, &"left handed");
//! assert!(flipped.left_ref().is_err());
//!
//! // Map a function over the left
//! let mapped_left: Either<usize, _> = left.map_left(|x| x.len())?;
//! assert_eq!(mapped_left.left_ref()?, &11);
//!
//! // Chain execution
//! let new_left: Either<&str, &str> = Either::new_left("lefty");
//! let and_then_left: Either<usize, _> = new_left
//!     .and_then_left(|x| Either::new_left(x.len()))?
//!     .and_then_left(|x| Either::new_left(x * 10))?;
//! assert_eq!(and_then_left.left_ref()?, &50);
//!
//! let new_right: Either<&str, &str> = Either::new_right("righty");
//! assert!(new_right
//!     .and_then_left(|x: &str| Either::new_left(x.len())).is_err()
//! );
//! #   Ok(())
//! # }
//! ```
#![cfg_attr(feature = "unstable", feature(tool_lints, try_from))]
#![cfg_attr(feature = "unstable", deny(clippy::all, clippy::pedantic))]
#![cfg_attr(feature = "unstable", warn(clippy::use_self))]
#![deny(
    macro_use_extern_crate,
    missing_copy_implementations,
    missing_debug_implementations,
    missing_docs,
    trivial_casts,
    trivial_numeric_casts,
    unused
)]
#![warn(
    absolute_paths_not_starting_with_crate,
    anonymous_parameters,
    bare_trait_objects,
    box_pointers,
    elided_lifetimes_in_paths,
    ellipsis_inclusive_range_patterns,
    keyword_idents,
    question_mark_macro_sep,
    single_use_lifetimes,
    unreachable_pub,
    unsafe_code,
    unused_extern_crates,
    unused_import_braces,
    unused_labels,
    unused_lifetimes,
    unused_qualifications,
    unused_results,
    variant_size_differences
)]
#![doc(html_root_url = "https://docs.rs/libeither/0.1.0")]

#[cfg(feature = "unstable")]
use failure::Error;
use failure::Fallible;
#[cfg(feature = "serde")]
use serde::{Deserialize, Serialize};
#[cfg(feature = "unstable")]
use std::convert::TryInto;
use std::fmt;
use std::io::{self, BufRead, Read, Write};

/// A struct representing either a left value, or a right value.
#[cfg_attr(feature = "serde", derive(Deserialize, Serialize))]
#[derive(Copy, Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Either<L, R> {
    /// The left value in the struct.
    left: Option<L>,
    /// The right value in the struct.
    right: Option<R>,
}

macro_rules! either {
    ($either:expr, $pattern:pat => $result:expr) => {
        if let Some($pattern) = $either.left {
            $result
        } else if let Some($pattern) = $either.right {
            $result
        }
    };
}

macro_rules! either_else {
    ($either:expr, $pattern:pat => $result:expr, $else_exp:expr) => {
        if let Some($pattern) = $either.left {
            $result
        } else if let Some($pattern) = $either.right {
            $result
        } else {
            $else_exp
        }
    };
}

impl<L, R> Either<L, R> {
    /// Create an `Either` with the left value populated.
    pub fn new_left(val: L) -> Self {
        Self {
            left: Some(val),
            right: None,
        }
    }

    /// Create an `Either` with the right value populated.
    pub fn new_right(val: R) -> Self {
        Self {
            left: None,
            right: Some(val),
        }
    }

    /// Check if this `Either` is the left variant.
    ///
    /// ```
    /// # use libeither::Either;
    /// #
    /// let left: Either<&str, &str> = Either::new_left("lefty");
    /// assert!(left.is_left());
    /// assert!(!left.is_right());
    /// ```
    pub fn is_left(&self) -> bool {
        self.left.is_some()
    }

    /// Check if this `Either` is the right variant.
    ///
    /// ```
    /// # use libeither::Either;
    /// #
    /// let right: Either<&str, &str> = Either::new_right("righty");
    /// assert!(right.is_right());
    /// assert!(!right.is_left());
    /// ```
    pub fn is_right(&self) -> bool {
        self.right.is_some()
    }

    /// Extract a reference to the left value.
    ///
    /// ```
    /// # use failure::Fallible;
    /// # use libeither::Either;
    /// #
    /// # fn main() -> Fallible<()> {
    /// let left: Either<&str, &str> = Either::new_left("lefty");
    /// assert_eq!(left.left_ref()?, &"lefty");
    /// #   Ok(())
    /// # }
    /// ```
    pub fn left_ref(&self) -> Fallible<&L> {
        self.left
            .as_ref()
            .ok_or_else(|| failure::err_msg("Unable to extract Left value"))
    }

    /// Extract a reference to the right value.
    ///
    /// ```
    /// # use failure::Fallible;
    /// # use libeither::Either;
    /// #
    /// # fn main() -> Fallible<()> {
    /// let right: Either<&str, &str> = Either::new_right("righty");
    /// assert_eq!(right.right_ref()?, &"righty");
    /// #   Ok(())
    /// # }
    /// ```
    pub fn right_ref(&self) -> Fallible<&R> {
        self.right
            .as_ref()
            .ok_or_else(|| failure::err_msg("Unable to extract Right value"))
    }

    /// Extract a mutable reference to the left value.
    ///
    /// ```
    /// # use failure::Fallible;
    /// # use libeither::Either;
    /// #
    /// # fn main() -> Fallible<()> {
    /// let mut left: Either<&str, &str> = Either::new_left("lefty");
    /// assert_eq!(left.left_ref()?, &"lefty");
    /// *(left.left_mut()?) = "left handed";
    /// assert_eq!(left.left_ref()?, &"left handed");
    /// #   Ok(())
    /// # }
    /// ```
    pub fn left_mut(&mut self) -> Fallible<&mut L> {
        self.left
            .as_mut()
            .ok_or_else(|| failure::err_msg("Unable to extract Left value"))
    }

    /// Extract a mutable reference to the right value.
    ///
    /// ```
    /// # use failure::Fallible;
    /// # use libeither::Either;
    /// #
    /// # fn main() -> Fallible<()> {
    /// let mut right: Either<&str, &str> = Either::new_right("righty");
    /// assert_eq!(right.right_ref()?, &"righty");
    /// *(right.right_mut()?) = "right handed";
    /// assert_eq!(right.right_ref()?, &"right handed");
    /// #   Ok(())
    /// # }
    /// ```
    pub fn right_mut(&mut self) -> Fallible<&mut R> {
        self.right
            .as_mut()
            .ok_or_else(|| failure::err_msg("Unable to extract Right value"))
    }

    /// Convert `Either<L, R>` to `Either<R, L>`
    ///
    /// ```
    /// # use failure::Fallible;
    /// # use libeither::Either;
    /// #
    /// # fn main() -> Fallible<()> {
    /// let left: Either<&str, &str> = Either::new_left("lefty");
    /// let right = left.flip()?;
    /// assert!(right.is_right());
    /// assert_eq!(right.right_ref()?, &"lefty");
    /// #   Ok(())
    /// # }
    /// ```
    pub fn flip(self) -> Fallible<Either<R, L>> {
        if let Some(l) = self.left {
            Ok(Either::new_right(l))
        } else if let Some(r) = self.right {
            Ok(Either::new_left(r))
        } else {
            Err(failure::err_msg("Invalid Either "))
        }
    }

    /// Apply the function `f` on the `Left` value, returning the result
    /// in a `Left`. If this is applied to a `Right`, the `Right` is
    /// returned.
    ///
    /// ```
    /// # use failure::Fallible;
    /// # use libeither::Either;
    /// #
    /// # fn main() -> Fallible<()> {
    /// let left: Either<u8, u8> = Either::new_left(10);
    /// let mapped_left = left.map_left(|x| x * 10)?;
    /// assert!(mapped_left.is_left());
    /// assert_eq!(mapped_left.left_ref()?, &100);
    /// #   Ok(())
    /// # }
    /// ```
    pub fn map_left<F, FL>(self, f: F) -> Fallible<Either<FL, R>>
    where
        F: FnOnce(L) -> FL,
    {
        if let Some(l) = self.left {
            Ok(Either::new_left(f(l)))
        } else if let Some(r) = self.right {
            Ok(Either::new_right(r))
        } else {
            Err(failure::err_msg("Invalid Either"))
        }
    }

    /// Apply the function `f` on the `Right` value, returning the result
    /// in a `Right`.  If this is applied to a `Left`, the `Left` is
    /// returned.
    ///
    /// ```
    /// # use failure::Fallible;
    /// # use libeither::Either;
    /// #
    /// # fn main() -> Fallible<()> {
    /// let right: Either<u8, u8> = Either::new_right(10);
    /// let mapped_right = right.map_right(|x| x * 10)?;
    /// assert!(mapped_right.is_right());
    /// assert_eq!(mapped_right.right_ref()?, &100);
    /// #   Ok(())
    /// # }
    /// ```
    pub fn map_right<F, FR>(self, f: F) -> Fallible<Either<L, FR>>
    where
        F: FnOnce(R) -> FR,
    {
        if let Some(l) = self.left {
            Ok(Either::new_left(l))
        } else if let Some(r) = self.right {
            Ok(Either::new_right(f(r)))
        } else {
            Err(failure::err_msg("Invalid Either"))
        }
    }

    /// Apply the function `f` on the value in the `Left` variant if it
    /// is present. If this is applied to a `Right`, a failure is generated.
    ///
    /// ```
    /// # use failure::Fallible;
    /// # use libeither::Either;
    /// #
    /// # fn main() -> Fallible<()> {
    /// let left: Either<u16, u16> = Either::new_left(10);
    /// let and_then_left: Either<u16, _> = left
    ///     .and_then_left(|x| Either::new_left(x * 10))?
    ///     .and_then_left(|x: u16| Either::new_left(x * 10))?;
    /// assert!(and_then_left.is_left());
    /// assert_eq!(and_then_left.left_ref()?, &1000);
    /// #   Ok(())
    /// # }
    pub fn and_then_left<F, S>(self, f: F) -> Fallible<Either<S, R>>
    where
        F: FnOnce(L) -> Either<S, R>,
    {
        if let Some(l) = self.left {
            Ok(f(l))
        } else if self.right.is_some() {
            Err(failure::err_msg("Right encountered in and_then_left"))
        } else {
            Err(failure::err_msg("Invalid Either"))
        }
    }

    /// Apply the function `f` on the value in the `Right` variant if it
    /// is present. If this is applied to a `Left`, the `Left` is
    /// returned.
    ///
    /// ```
    /// # use failure::Fallible;
    /// # use libeither::Either;
    /// #
    /// # fn main() -> Fallible<()> {
    /// let right: Either<u16, u16> = Either::new_right(10);
    /// let and_then_right: Either<u16, u16> = right
    ///     .and_then_right(|x| Either::new_right(x * 10))?
    ///     .and_then_right(|x: u16| Either::new_right(x * 10))?;
    /// assert!(and_then_right.is_right());
    /// assert_eq!(and_then_right.right_ref()?, &1000);
    /// #   Ok(())
    /// # }
    pub fn and_then_right<F, S>(self, f: F) -> Fallible<Either<L, S>>
    where
        F: FnOnce(R) -> Either<L, S>,
    {
        if self.left.is_some() {
            Err(failure::err_msg("Left encountered in and_then_right"))
        } else if let Some(r) = self.right {
            Ok(f(r))
        } else {
            Err(failure::err_msg("Invalid Either"))
        }
    }

    /// Convert the inners to iters
    #[cfg_attr(feature = "unstable", allow(clippy::should_implement_trait))]
    pub fn into_iter(self) -> Fallible<Either<L::IntoIter, R::IntoIter>>
    where
        L: IntoIterator,
        R: IntoIterator<Item = L::Item>,
    {
        if let Some(l) = self.left {
            Ok(Either::new_left(l.into_iter()))
        } else if let Some(r) = self.right {
            Ok(Either::new_right(r.into_iter()))
        } else {
            Err(failure::err_msg("Invalid Either"))
        }
    }
}

impl<L, R> From<Result<L, R>> for Either<L, R> {
    fn from(r: Result<L, R>) -> Self {
        match r {
            Ok(o) => Self::new_left(o),
            Err(e) => Self::new_right(e),
        }
    }
}

#[cfg(feature = "unstable")]
impl<L, R> TryInto<Result<L, R>> for Either<L, R> {
    type Error = Error;

    fn try_into(self) -> Result<Result<L, R>, Error> {
        if let Some(l) = self.left {
            Ok(Ok(l))
        } else if let Some(r) = self.right {
            Ok(Err(r))
        } else {
            Err(failure::err_msg("Unable to convert Either into Result!"))
        }
    }
}

impl<L, R, A> Extend<A> for Either<L, R>
where
    L: Extend<A>,
    R: Extend<A>,
{
    fn extend<T>(&mut self, iter: T)
    where
        T: IntoIterator<Item = A>,
    {
        either!(*self, ref mut inner => inner.extend(iter))
    }
}

impl<L, R> Iterator for Either<L, R>
where
    L: Iterator,
    R: Iterator<Item = L::Item>,
{
    type Item = L::Item;

    fn next(&mut self) -> Option<Self::Item> {
        either_else!(*self, ref mut inner => inner.next(), None)
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        either_else!(self, ref inner => inner.size_hint(), (0, None))
    }

    fn fold<Acc, G>(self, init: Acc, f: G) -> Acc
    where
        G: FnMut(Acc, Self::Item) -> Acc,
    {
        either_else!(self, inner => inner.fold(init, f), init)
    }

    fn count(self) -> usize {
        either_else!(self, inner => inner.count(), 0)
    }

    fn last(self) -> Option<Self::Item> {
        either_else!(self, inner => inner.last(), None)
    }

    fn nth(&mut self, n: usize) -> Option<Self::Item> {
        either_else!(*self, ref mut inner => inner.nth(n), None)
    }

    fn all<F>(&mut self, f: F) -> bool
    where
        F: FnMut(Self::Item) -> bool,
    {
        either_else!(*self, ref mut inner => inner.all(f), false)
    }
}

impl<L, R> DoubleEndedIterator for Either<L, R>
where
    L: DoubleEndedIterator,
    R: DoubleEndedIterator<Item = L::Item>,
{
    fn next_back(&mut self) -> Option<Self::Item> {
        either_else!(*self, ref mut inner => inner.next_back(), None)
    }
}

fn io_err(msg: &str) -> io::Error {
    io::Error::new(io::ErrorKind::Other, msg)
}

impl<L, R> Read for Either<L, R>
where
    L: Read,
    R: Read,
{
    fn read(&mut self, buf: &mut [u8]) -> io::Result<usize> {
        either_else!(*self, ref mut inner => inner.read(buf), Err(io_err("Invalid Either (Read)")))
    }

    fn read_to_end(&mut self, buf: &mut Vec<u8>) -> io::Result<usize> {
        either_else!(*self, ref mut inner => inner.read_to_end(buf), Err(io_err("Invalid Either (Read)")))
    }
}

impl<L, R> BufRead for Either<L, R>
where
    L: BufRead,
    R: BufRead,
{
    fn fill_buf(&mut self) -> io::Result<&[u8]> {
        either_else!(*self, ref mut inner => inner.fill_buf(), Err(io_err("Invalid Either (BufRead)")))
    }

    fn consume(&mut self, amt: usize) {
        either!(*self, ref mut inner => inner.consume(amt))
    }
}

impl<L, R> Write for Either<L, R>
where
    L: Write,
    R: Write,
{
    fn write(&mut self, buf: &[u8]) -> io::Result<usize> {
        either_else!(*self, ref mut inner => inner.write(buf), Err(io_err("Invalid Either (Write)")))
    }

    fn flush(&mut self) -> io::Result<()> {
        either_else!(*self, ref mut inner => inner.flush(), Err(io_err("Invalid Either (Write)")))
    }
}

impl<L, R> std::error::Error for Either<L, R>
where
    L: std::error::Error,
    R: std::error::Error,
{
    fn description(&self) -> &str {
        either_else!(&self, ref inner => inner.description(), "Invalid Either (Error")
    }

    fn cause(&self) -> Option<&dyn std::error::Error> {
        either_else!(&self, ref inner => inner.cause(), None)
    }
}

impl<L, R> fmt::Display for Either<L, R>
where
    L: fmt::Display,
    R: fmt::Display,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        either_else!(&self, ref inner => inner.fmt(f), Err(fmt::Error))
    }
}

#[cfg(test)]
mod tests {
    use super::{io_err, Either};
    use failure::Fallible;
    #[cfg(feature = "unstable")]
    use std::convert::TryInto;
    use std::error::Error;
    use std::io::{self, Cursor, Read, Write};

    fn invalid<'a>() -> Either<&'a str, &'a str> {
        Either {
            left: None,
            right: None,
        }
    }

    fn lefty<'a>() -> Either<&'a str, &'a str> {
        Either::new_left("lefty")
    }

    fn righty<'a>() -> Either<&'a str, &'a str> {
        Either::new_right("righty")
    }

    #[test]
    fn io_err_works() {
        assert_eq!(
            io_err("test").description(),
            io::Error::new(io::ErrorKind::Other, "test").description()
        );
    }

    #[test]
    fn make_left() {
        let left = lefty();
        assert!(left.is_left());
        assert!(!left.is_right());
    }

    #[test]
    fn make_right() {
        let right = righty();
        assert!(right.is_right());
        assert!(!right.is_left());
    }

    #[test]
    fn left_ref() -> Fallible<()> {
        assert_eq!(lefty().left_ref()?, &"lefty");
        Ok(())
    }

    #[test]
    fn right_ref_on_left() {
        assert!(
            lefty().right_ref().is_err(),
            "right_ref on Left should not work!"
        );
    }

    #[test]
    fn right_ref() -> Fallible<()> {
        assert_eq!(righty().right_ref()?, &"righty");
        Ok(())
    }

    #[test]
    fn left_ref_on_right() {
        assert!(
            righty().left_ref().is_err(),
            "left_ref on Right should not work!"
        );
    }

    #[test]
    fn left_ref_mut() -> Fallible<()> {
        let mut left = lefty();
        assert_eq!(left.left_ref()?, &"lefty");
        *(left.left_mut()?) = "left handed";
        assert_eq!(left.left_ref()?, &"left handed");
        Ok(())
    }

    #[test]
    fn left_ref_mut_invalid() -> Fallible<()> {
        let mut invalid = invalid();
        assert!(invalid.left_mut().is_err());
        Ok(())
    }

    #[test]
    fn right_mut_on_left() {
        assert!(
            lefty().right_mut().is_err(),
            "right_mut on Left should not work!"
        );
    }

    #[test]
    fn right_ref_mut() -> Fallible<()> {
        let mut right = righty();
        assert_eq!(right.right_ref()?, &"righty");
        *(right.right_mut()?) = "right handed";
        assert_eq!(right.right_ref()?, &"right handed");
        Ok(())
    }

    #[test]
    fn right_ref_mut_invalid() -> Fallible<()> {
        let mut invalid = invalid();
        assert!(invalid.right_mut().is_err());
        Ok(())
    }

    #[test]
    fn left_mut_on_right() {
        assert!(
            righty().left_mut().is_err(),
            "left_mut on Right should not work!"
        );
    }

    #[test]
    fn flip() -> Fallible<()> {
        let mut left = lefty();
        let right = left.flip()?;
        assert!(right.is_right());
        assert_eq!(right.right_ref()?, &"lefty");
        left = right.flip()?;
        assert!(left.is_left());
        assert_eq!(left.left_ref()?, &"lefty");
        Ok(())
    }

    #[test]
    fn flip_invalid() -> Fallible<()> {
        let invalid: Either<&str, &str> = Either {
            left: None,
            right: None,
        };
        assert!(invalid.flip().is_err());
        Ok(())
    }

    #[test]
    fn map_left() -> Fallible<()> {
        let left: Either<u8, u8> = Either::new_left(10);
        let mapped_left = left.map_left(|x| x * 10)?;
        assert!(mapped_left.is_left());
        assert_eq!(mapped_left.left_ref()?, &100);
        Ok(())
    }

    #[test]
    fn map_left_invalid() -> Fallible<()> {
        let invalid = invalid();
        assert!(invalid.map_left(|x| x.to_string()).is_err());
        Ok(())
    }

    #[test]
    fn map_left_on_right() -> Fallible<()> {
        let right: Either<u8, u8> = Either::new_right(10);
        let mapped_right = right.map_left(|x| x * 10)?;
        assert_eq!(right, mapped_right);
        Ok(())
    }

    #[test]
    fn map_right() -> Fallible<()> {
        let right: Either<u8, u8> = Either::new_right(10);
        let mapped_right = right.map_right(|x| x * 10)?;
        assert!(mapped_right.is_right());
        assert_eq!(mapped_right.right_ref()?, &100);
        Ok(())
    }

    #[test]
    fn map_right_invalid() -> Fallible<()> {
        let invalid = invalid();
        assert!(invalid.map_right(|x| x.to_string()).is_err());
        Ok(())
    }

    #[test]
    fn map_right_on_left() -> Fallible<()> {
        let left: Either<u8, u8> = Either::new_left(10);
        let mapped_left = left.map_right(|x| x * 10)?;
        assert_eq!(left, mapped_left);
        Ok(())
    }

    #[test]
    fn and_then_left() -> Fallible<()> {
        let left: Either<u16, u16> = Either::new_left(10);
        let and_then_left: Either<u16, u16> = left
            .and_then_left(|x| Either::new_left(x * 10))?
            .and_then_left(|x: u16| Either::new_left(x * 10))?;
        assert!(and_then_left.is_left());
        assert_eq!(and_then_left.left_ref()?, &1000);
        Ok(())
    }

    #[test]
    fn and_then_left_on_right() -> Fallible<()> {
        let right: Either<u8, u8> = Either::new_right(10);
        assert!(right.and_then_left(|x| Either::new_left(x * 10)).is_err());
        Ok(())
    }

    #[test]
    fn and_then_left_invalid() -> Fallible<()> {
        let invalid = invalid();
        assert!(
            invalid
                .and_then_left(|x| Either::new_left(x.len()))
                .is_err()
        );
        Ok(())
    }

    #[test]
    fn and_then_right() -> Fallible<()> {
        let right: Either<u16, u16> = Either::new_right(10);
        let and_then_right: Either<u16, u16> = right
            .and_then_right(|x| Either::new_right(x * 10))?
            .and_then_right(|x| Either::new_right(x * 10))?;
        assert!(and_then_right.is_right());
        assert_eq!(and_then_right.right_ref()?, &1000);
        Ok(())
    }

    #[test]
    fn and_then_right_on_left() -> Fallible<()> {
        let left: Either<u8, u8> = Either::new_left(10);
        assert!(left.and_then_right(|x| Either::new_right(x * 10)).is_err());
        Ok(())
    }

    #[test]
    fn and_then_right_invalid() -> Fallible<()> {
        let invalid = invalid();
        assert!(
            invalid
                .and_then_right(|x| Either::new_right(x.len()))
                .is_err()
        );
        Ok(())
    }

    #[test]
    fn from_ok_result() -> Fallible<()> {
        let result: Result<&str, &str> = Ok("ok");
        let left = Either::from(result);
        assert!(left.is_left());
        assert_eq!(left.left_ref()?, &"ok");
        Ok(())
    }

    #[test]
    fn from_err_result() -> Fallible<()> {
        let err: Result<&str, &str> = Err("err");
        let right = Either::from(err);
        assert!(right.is_right());
        assert_eq!(right.right_ref()?, &"err");
        Ok(())
    }

    #[test]
    #[cfg(feature = "unstable")]
    fn try_into_left_result() -> Fallible<()> {
        let left = lefty();
        let result: Result<&str, &str> = Either::try_into(left)?;
        assert!(result.is_ok());
        assert_eq!(result.unwrap(), "lefty");
        Ok(())
    }

    #[test]
    #[cfg(feature = "unstable")]
    fn try_into_right_result() -> Fallible<()> {
        let right = righty();
        let result: Result<&str, &str> = Either::try_into(right)?;
        assert!(result.is_err());
        assert_eq!(result, Err("righty"));
        Ok(())
    }

    #[test]
    #[cfg(feature = "unstable")]
    fn try_into_invalid() -> Fallible<()> {
        let invalid = invalid();
        let result: Result<Result<&str, &str>, failure::Error> = Either::try_into(invalid);
        assert!(result.is_err());
        Ok(())
    }

    #[test]
    fn either_left_read() -> Fallible<()> {
        let left_cursor = Cursor::new(vec![1, 2, 3, 4, 5]);
        let mut left: Either<Cursor<Vec<u8>>, Cursor<Vec<u8>>> = Either::new_left(left_cursor);
        let mut left_buf = [0_u8; 5];
        assert_eq!(left.read(&mut left_buf)?, left_buf.len());
        assert_eq!(left_buf, &vec![1, 2, 3, 4, 5][..]);
        Ok(())
    }

    #[test]
    fn either_right_read() -> Fallible<()> {
        let right_cursor = Cursor::new(vec![10, 9, 8, 7, 6]);
        let mut right: Either<Cursor<Vec<u8>>, Cursor<Vec<u8>>> = Either::new_right(right_cursor);
        let mut right_buf = [0_u8; 5];
        assert_eq!(right.read(&mut right_buf)?, right_buf.len());
        assert_eq!(right_buf, &vec![10, 9, 8, 7, 6][..]);
        Ok(())
    }

    #[test]
    fn either_left_write() -> Fallible<()> {
        let left_buf = Vec::new();
        let hello = b"hello";

        let mut left: Either<Vec<u8>, Vec<u8>> = Either::new_left(left_buf);
        assert_eq!(left.write(hello)?, 5);
        assert_eq!(&left.left_ref()?[..], b"hello");
        Ok(())
    }

    #[test]
    fn either_right_write() -> Fallible<()> {
        let right_buf = Vec::new();
        let hello = b"hello";

        let mut right: Either<Vec<u8>, Vec<u8>> = Either::new_right(right_buf);
        assert_eq!(right.write(hello)?, 5);
        assert_eq!(&right.right_ref()?[..], b"hello");
        Ok(())
    }

    #[test]
    fn either_left_iter() -> Fallible<()> {
        let left: Either<Vec<u32>, Vec<u32>> = Either::new_left(vec![1, 2, 3, 4, 5]);
        let mut right: Either<Vec<u32>, Vec<u32>> = Either::new_right(vec![5, 4, 3, 2, 1]);
        right.extend(left.into_iter()?);
        assert_eq!(right.right_ref()?, &vec![5, 4, 3, 2, 1, 1, 2, 3, 4, 5]);
        Ok(())
    }

    #[test]
    fn either_right_iter() -> Fallible<()> {
        let mut left: Either<Vec<u32>, Vec<u32>> = Either::new_left(vec![1, 2, 3, 4, 5]);
        let right: Either<Vec<u32>, Vec<u32>> = Either::new_right(vec![5, 4, 3, 2, 1]);
        left.extend(right.into_iter()?);
        assert_eq!(left.left_ref()?, &vec![1, 2, 3, 4, 5, 5, 4, 3, 2, 1]);
        Ok(())
    }

    #[test]
    fn invalid_into_iter() -> Fallible<()> {
        let invalid: Either<Vec<u32>, Vec<u32>> = Either {
            left: None,
            right: None,
        };
        assert!(invalid.into_iter().is_err());
        Ok(())
    }

    #[test]
    #[cfg(feature = "serde")]
    fn serialize_json_left() -> Fallible<()> {
        let left = lefty();
        let json = serde_json::to_string(&left)?;
        assert_eq!(json, r#"{"left":"lefty","right":null}"#);
        Ok(())
    }

    #[test]
    #[cfg(feature = "serde")]
    fn serialize_toml_left() -> Fallible<()> {
        let left = lefty();
        let toml = toml::to_string(&left)?;
        assert_eq!(
            toml,
            r#"left = "lefty"
"#
        );
        Ok(())
    }

    #[test]
    #[cfg(feature = "serde")]
    fn serialize_json_right() -> Fallible<()> {
        let right = righty();
        let json = serde_json::to_string(&right)?;
        assert_eq!(json, r#"{"left":null,"right":"righty"}"#);
        Ok(())
    }

    #[test]
    #[cfg(feature = "serde")]
    fn serialize_toml_right() -> Fallible<()> {
        let right = righty();
        let toml = toml::to_string(&right)?;
        assert_eq!(
            toml,
            r#"right = "righty"
"#
        );
        Ok(())
    }

    #[test]
    #[cfg(feature = "serde")]
    fn deserialize_json_left() -> Fallible<()> {
        let json = r#"{"left":"lefty","right":null}"#;
        let left: Either<&str, &str> = serde_json::from_str(&json)?;
        assert!(left.is_left());
        assert_eq!(left.left_ref()?, &"lefty");
        Ok(())
    }

    #[test]
    #[cfg(feature = "serde")]
    fn deserialize_toml_left() -> Fallible<()> {
        let toml = r#"left = "lefty"
"#;
        let left: Either<&str, &str> = toml::from_str(&toml)?;
        assert!(left.is_left());
        assert_eq!(left.left_ref()?, &"lefty");
        Ok(())
    }

    #[test]
    #[cfg(feature = "serde")]
    fn deserialize_json_right() -> Fallible<()> {
        let json = r#"{"left":null,"right":"righty"}"#;
        let right: Either<&str, &str> = serde_json::from_str(&json)?;
        assert!(right.is_right());
        assert_eq!(right.right_ref()?, &"righty");
        Ok(())
    }

    #[test]
    #[cfg(feature = "serde")]
    fn deserialize_toml_right() -> Fallible<()> {
        let toml = r#"right = "righty"
"#;
        let right: Either<&str, &str> = toml::from_str(&toml)?;
        assert!(right.is_right());
        assert_eq!(right.right_ref()?, &"righty");
        Ok(())
    }
}
