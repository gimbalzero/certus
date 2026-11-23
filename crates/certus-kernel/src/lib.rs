//! The Certus kernel: an independent type checker for the Lean 4 kernel
//! language, reading `lean4export` files.
//!
//! What is checked, for every declaration:
//! - axioms: the type is well formed;
//! - definitions, theorems, opaques: the value has the declared type
//!   (theorem types must be propositions);
//! - inductive types: well-formedness, strict positivity and universe
//!   constraints, and recursors regenerated from scratch and compared
//!   (nested inductive types via auxiliary types, as in Lean's kernel);
//! - quotients: the four built-in constants have exactly the built-in types.
//!
//! Not supported yet (rejected, never skipped): `unsafe` and `partial`
//! declarations.

pub mod check;
pub mod env;
pub mod inductive;
pub mod quot;
pub mod stream;
pub mod tc;
pub mod term;

pub use check::{CheckError, Report, check, check_jobs, check_with};
pub use tc::KError;
#[doc(hidden)]
pub use tc::set_collect_threshold_for_tests;
