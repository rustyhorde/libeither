// Copyright (c) 2018 libeither developers
//
// Licensed under the Apache License, Version 2.0
// <LICENSE-APACHE or http://www.apache.org/licenses/LICENSE-2.0> or the MIT
// license <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. All files in the project carrying such notice may not be copied,
// modified, or distributed except according to those terms.

//! Either Struct
#![feature(crate_visibility_modifier, tool_lints, try_from)]
#![deny(
    clippy::all,
    clippy::pedantic,
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
    clippy::use_self,
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

use failure::Fallible;
#[cfg(feature = "serde")]
use serde::{Deserialize, Serialize};

/// A struct representing either a left value, or a right value.
#[cfg_attr(feature = "serde", derive(Deserialize, Serialize))]
#[derive(Copy, Clone, Debug, Eq, PartialEq)]
pub struct Either<L, R> {
    /// The left value in the struct.
    left: Option<L>,
    /// The right value in the struct.
    right: Option<R>,
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
    /// # use libeither::Either;
    /// #
    /// let left: Either<&str, &str> = Either::new_left("lefty");
    /// match left.left_ref() {
    ///     Ok(val) => assert!(*val == "lefty"),
    ///     Err(_) => assert!(false, "Unable to extract left value from Left"),
    /// }
    /// ```
    pub fn left_ref(&self) -> Fallible<&L> {
        self.left
            .as_ref()
            .ok_or_else(|| failure::err_msg("Unable to extract Left value"))
    }

    /// Extract a reference to the right value.
    ///
    /// ```
    /// # use libeither::Either;
    /// #
    /// let right: Either<&str, &str> = Either::new_right("righty");
    /// match right.right_ref() {
    ///     Ok(val) => assert!(*val == "righty"),
    ///     Err(_) => assert!(false, "Unable to extract right value from Right"),
    /// }
    /// ```
    pub fn right_ref(&self) -> Fallible<&R> {
        self.right
            .as_ref()
            .ok_or_else(|| failure::err_msg("Unable to extract Right value"))
    }

    /// Extract a mutable reference to the left value.
    ///
    /// ```
    /// # use libeither::Either;
    /// #
    /// let mut left: Either<&str, &str> = Either::new_left("lefty");
    /// match left.left_mut() {
    ///     Ok(val) => *val = &mut "left handed",
    ///     Err(e) => assert!(false, e.to_string()),
    /// }
    /// assert_eq!(left, Either::new_left("left handed"));
    /// ```
    pub fn left_mut(&mut self) -> Fallible<&mut L> {
        if self.is_left() {
            self.left
                .as_mut()
                .ok_or_else(|| failure::err_msg("Unable to extract Left value"))
        } else {
            Err(failure::err_msg("Cannot mutate the right value of a Left"))
        }
    }

    /// Convert `Either<L, R>` to `Either<R, L>`
    ///
    /// ```
    /// # use libeither::Either;
    /// #
    /// let left: Either<&str, &str> = Either::new_left("lefty");
    /// match left.flip() {
    ///     Ok(right) => {
    ///         assert!(right.is_right());
    ///
    ///         match right.right_ref() {
    ///             Ok(val) => assert!(*val == "lefty"),
    ///             Err(e) => assert!(false, e.to_string()),
    ///         }
    ///     }
    ///     Err(e) => assert!(false, e.to_string()),
    /// }
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
    /// in a `Left`.
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
}

#[cfg(test)]
mod tests {
    use super::Either;

    fn lefty<'a>() -> Either<&'a str, &'a str> {
        Either::new_left("lefty")
    }

    fn righty<'a>() -> Either<&'a str, &'a str> {
        Either::new_right("righty")
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

    fn check_left_val<L, R>(left: &Either<L, R>, expected: &L)
    where
        L: PartialEq,
    {
        match left.left_ref() {
            Ok(val) => assert!(val == expected),
            Err(e) => assert!(false, e.to_string()),
        }
    }

    fn check_right_val<L, R>(right: &Either<L, R>, expected: &R)
    where
        R: PartialEq,
    {
        match right.right_ref() {
            Ok(val) => assert!(val == expected),
            Err(e) => assert!(false, e.to_string()),
        }
    }

    #[test]
    fn left_ref() {
        let left = lefty();
        check_left_val(&left, &"lefty");
        match left.right_ref() {
            Ok(_) => assert!(false, "Not expected to extract right ref from Left"),
            Err(_) => assert!(true),
        }
    }

    #[test]
    fn right_ref() {
        let right = righty();
        check_right_val(&right, &"righty");
        match right.left_ref() {
            Ok(_) => assert!(false, "Not expected to extract left ref from Right"),
            Err(_) => assert!(true),
        }
    }

    #[test]
    fn left_ref_mut() {
        let mut left = lefty();
        match left.left_mut() {
            Ok(val) => *val = &mut "left handed",
            Err(e) => assert!(false, e.to_string()),
        }
        assert_eq!(left, Either::new_left("left handed"));
        match left.right_mut() {
            Ok(_) => assert!(false, "Not expected to extract right ref mut from Left"),
            Err(_) => assert!(true),
        }
    }

    #[test]
    fn right_ref_mut() {
        let mut right = righty();
        match right.right_mut() {
            Ok(val) => *val = &mut "right handed",
            Err(e) => assert!(false, e.to_string()),
        }
        assert_eq!(right, Either::new_right("right handed"));
        match right.left_mut() {
            Ok(_) => assert!(false, "Not expected to extract left ref mut from Right"),
            Err(_) => assert!(true),
        }
    }

    #[test]
    fn flip() {
        let left = lefty();
        match left.flip() {
            Ok(right) => {
                assert!(right.is_right());
                check_right_val(&right, &"lefty");
            }
            Err(e) => assert!(false, e.to_string()),
        }
    }

    #[test]
    fn map_left() {
        let left: Either<u8, u8> = Either::new_left(10);
        match left.map_left(|x| x * 10) {
            Ok(new_left) => {
                assert!(new_left.is_left());
                check_left_val(&new_left, &100);
            }
            Err(e) => assert!(false, e.to_string()),
        }
    }
}
