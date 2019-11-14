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
//! * `serialization` - Enable serialization via serde (on by default)
//! * `unstable` - Enable unstable options (nightly only, off by default)
//!
//! # Examples
//! ```
//! # use libeither::{Either, Result};
//! #
//! # fn main() -> Result<()> {
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
//! assert_eq!(new_right
//!     .and_then_left(|x: &str| Either::new_left(x.len()))?.right_ref()?, &"righty"
//! );
//! #   Ok(())
//! # }
//! ```
#![cfg_attr(feature = "unstable", feature(error_iter))]
#![deny(
    absolute_paths_not_starting_with_crate,
    anonymous_parameters,
    bare_trait_objects,
    clippy::all,
    clippy::pedantic,
    box_pointers,
    dead_code,
    deprecated,
    deprecated_in_future,
    elided_lifetimes_in_paths,
    ellipsis_inclusive_range_patterns,
    explicit_outlives_requirements,
    exported_private_dependencies,
    ill_formed_attribute_input,
    illegal_floating_point_literal_pattern,
    improper_ctypes,
    incomplete_features,
    indirect_structural_match,
    intra_doc_link_resolution_failure,
    invalid_value,
    irrefutable_let_patterns,
    keyword_idents,
    late_bound_lifetime_arguments,
    macro_use_extern_crate,
    meta_variable_misuse,
    missing_copy_implementations,
    missing_debug_implementations,
    // missing_doc_code_examples,
    missing_docs,
    mutable_borrow_reservation_conflict,
    no_mangle_generic_items,
    non_ascii_idents,
    non_camel_case_types,
    non_shorthand_field_patterns,
    non_snake_case,
    non_upper_case_globals,
    overlapping_patterns,
    path_statements,
    patterns_in_fns_without_body,
    plugin_as_library,
    // private_doc_tests,
    private_in_public,
    proc_macro_derive_resolution_fallback,
    redundant_semicolon,
    renamed_and_removed_lints,
    safe_packed_borrows,
    single_use_lifetimes,
    stable_features,
    trivial_bounds,
    trivial_casts,
    trivial_numeric_casts,
    type_alias_bounds,
    tyvar_behind_raw_pointer,
    unconditional_recursion,
    unknown_lints,
    unnameable_test_items,
    unreachable_code,
    unreachable_patterns,
    unreachable_pub,
    unsafe_code,
    unstable_name_collisions,
    unused_allocation,
    unused_assignments,
    unused_attributes,
    unused_comparisons,
    unused_doc_comments,
    unused_extern_crates,
    unused_features,
    unused_import_braces,
    unused_imports,
    unused_labels,
    unused_lifetimes,
    unused_macros,
    unused_must_use,
    unused_mut,
    unused_parens,
    unused_qualifications,
    unused_results,
    unused_unsafe,
    unused_variables,
    variant_size_differences,
    where_clauses_object_safety,
    while_true
)]
#![cfg_attr(feature = "unstable", allow(unstable_features))]
#![cfg_attr(not(feature = "unstable"), deny(unstable_features))]
#![allow(clippy::use_self)]
#![doc(html_root_url = "https://docs.rs/libeither/0.4.0")]

mod either;
mod error;

pub use either::Either;
pub use error::{Error, Result};
