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
#![cfg_attr(all(nightly_lints, feature = "unstable"), feature(error_iter))]
// rustc lints
#![cfg_attr(
    msrv,
    deny(
        absolute_paths_not_starting_with_crate,
        anonymous_parameters,
        array_into_iter,
        asm_sub_register,
        bad_asm_style,
        bare_trait_objects,
        bindings_with_variant_name,
        // box_pointers,
        break_with_label_and_loop,
        clashing_extern_declarations,
        coherence_leak_check,
        confusable_idents,
        const_evaluatable_unchecked,
        const_item_mutation,
        dead_code,
        deprecated,
        deprecated_in_future,
        deprecated_where_clause_location,
        deref_into_dyn_supertrait,
        deref_nullptr,
        drop_bounds,
        duplicate_macro_attributes,
        dyn_drop,
        elided_lifetimes_in_paths,
        ellipsis_inclusive_range_patterns,
        explicit_outlives_requirements,
        exported_private_dependencies,
        // Unstable
        // ffi_unwind_calls,
        forbidden_lint_groups,
        function_item_references,
        // Unstable
        // fuzzy_provenance_casts,
        illegal_floating_point_literal_pattern,
        improper_ctypes,
        improper_ctypes_definitions,
        incomplete_features,
        indirect_structural_match,
        inline_no_sanitize,
        invalid_doc_attributes,
        invalid_value,
        irrefutable_let_patterns,
        keyword_idents,
        large_assignments,
        late_bound_lifetime_arguments,
        legacy_derive_helpers,
        let_underscore_drop,
        // Unstable
        // lossy_provenance_casts,
        macro_use_extern_crate,
        meta_variable_misuse,
        missing_abi,
        missing_copy_implementations,
        missing_debug_implementations,
        missing_docs,
        mixed_script_confusables,
        // Unstable
        // must_not_suspend,
        named_arguments_used_positionally,
        no_mangle_generic_items,
        non_ascii_idents,
        non_camel_case_types,
        // Unstable
        // non_exhaustive_omitted_patterns,
        non_fmt_panics,
        non_shorthand_field_patterns,
        non_snake_case,
        non_upper_case_globals,
        nontrivial_structural_match,
        noop_method_call,
        overlapping_range_endpoints,
        path_statements,
        pointer_structural_match,
        private_in_public,
        redundant_semicolons,
        renamed_and_removed_lints,
        repr_transparent_external_private_fields,
        rust_2021_incompatible_closure_captures,
        rust_2021_incompatible_or_patterns,
        rust_2021_prefixes_incompatible_syntax,
        rust_2021_prelude_collisions,
        semicolon_in_expressions_from_macros,
        single_use_lifetimes,
        special_module_name,
        stable_features,
        suspicious_auto_trait_impls,
        temporary_cstring_as_ptr,
        trivial_bounds,
        trivial_casts,
        trivial_numeric_casts,
        type_alias_bounds,
        tyvar_behind_raw_pointer,
        uncommon_codepoints,
        unconditional_recursion,
        unexpected_cfgs,
        // Unstable
        // unfulfilled_lint_expectations,
        uninhabited_static,
        unknown_lints,
        unnameable_test_items,
        unreachable_code,
        unreachable_patterns,
        unreachable_pub,
        unsafe_code,
        unsafe_op_in_unsafe_fn,
        unstable_name_collisions,
        unstable_syntax_pre_expansion,
        unsupported_calling_conventions,
        unused_allocation,
        unused_assignments,
        unused_attributes,
        unused_braces,
        unused_comparisons,
        // unused_crate_dependencies,
        unused_doc_comments,
        unused_extern_crates,
        unused_features,
        unused_import_braces,
        unused_imports,
        unused_labels,
        unused_lifetimes,
        unused_macro_rules,
        unused_macros,
        unused_must_use,
        unused_mut,
        unused_parens,
        unused_qualifications,
        unused_results,
        unused_tuple_struct_fields,
        unused_unsafe,
        unused_variables,
        variant_size_differences,
        where_clauses_object_safety,
        while_true,
))]
// nightly only lints
// #![cfg_attr(all(msrv, nightly_lints),deny())]
// nightly or beta only lints
#![cfg_attr(
    all(msrv, any(beta_lints, nightly_lints)),
    deny(for_loops_over_fallibles, opaque_hidden_inferred_bound)
)]
// beta only lints
// #![cfg_attr( all(msrv, beta_lints), deny())]
// beta or stable only lints
// #![cfg_attr(all(msrv, any(beta_lints, stable_lints)), deny())]
// stable only lints
// #![cfg_attr(all(msrv, stable_lints), deny())]
// clippy lints
#![cfg_attr(msrv, deny(clippy::all, clippy::pedantic))]
// #![cfg_attr(msrv, allow())]
// rustdoc lints
#![cfg_attr(
    msrv,
    deny(
        rustdoc::bare_urls,
        rustdoc::broken_intra_doc_links,
        rustdoc::invalid_codeblock_attributes,
        rustdoc::invalid_html_tags,
        rustdoc::missing_crate_level_docs,
        // rustdoc::missing_doc_code_examples,
        rustdoc::private_doc_tests,
        rustdoc::private_intra_doc_links,
    )
)]
#![cfg_attr(
    all(msrv, feature = "unstable", nightly_lints),
    allow(unstable_features)
)]
#![cfg_attr(all(msrv, not(feature = "unstable")), deny(unstable_features))]

mod either;
mod error;

pub use either::Either;
pub use error::{Error, Result};
