//! Certus core: read Lean 4 kernel exports, give every declaration a content
//! hash, and compute what each theorem depends on.
//!
//! This is Phase 0. There is no type checker here yet; see `docs/PLAN.md`.

pub mod deps;
pub mod export;
pub mod hash;

pub use export::{Decl, Env, Expr, Level, Name, ParseError, parse};
