//! Certus core: read Lean 4 kernel exports, give every declaration a content
//! hash, and compute what each theorem depends on.
//!
//! The type checker itself lives in `certus-kernel`.

pub mod cache;
pub mod deps;
pub mod export;
pub mod hash;
pub mod pretty;
pub mod report;
pub mod write;

pub use export::{Decl, Env, Expr, Level, Name, ParseError, parse};
