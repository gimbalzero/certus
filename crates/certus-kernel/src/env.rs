//! The kernel environment: every constant that has been checked so far.

use crate::term::E;
use certus_core::export::NameId;
use rustc_hash::FxHashMap;
use std::sync::Arc;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Hints {
    Opaque,
    Abbrev,
    Regular(u32),
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum QuotKind {
    Type,
    Ctor,
    Lift,
    Ind,
}

#[derive(Clone, Debug)]
pub struct RecRule {
    pub ctor: NameId,
    pub nfields: u32,
    pub rhs: E,
}

#[derive(Clone, Debug)]
pub enum Kind {
    Axiom,
    Def {
        val: E,
        hints: Hints,
    },
    Thm {
        val: E,
    },
    Opaque,
    Quot(QuotKind),
    Induct {
        num_params: u32,
        num_indices: u32,
        all: Vec<NameId>,
        ctors: Vec<NameId>,
        is_rec: bool,
    },
    Ctor {
        induct: NameId,
        cidx: u32,
        num_params: u32,
        num_fields: u32,
    },
    Rec {
        major_induct: NameId,
        num_params: u32,
        num_indices: u32,
        num_motives: u32,
        num_minors: u32,
        rules: Vec<RecRule>,
        k: bool,
    },
}

#[derive(Clone, Debug)]
pub struct ConstInfo {
    pub lparams: Vec<NameId>,
    pub ty: E,
    pub kind: Kind,
}

/// Names the kernel treats specially (literals, `Nat` acceleration, quotients).
/// A name that does not occur in the export stays `None`, and the feature
/// that needs it is off.
#[derive(Default, Clone, Debug)]
pub struct Builtins {
    pub nat: Option<NameId>,
    pub nat_zero: Option<NameId>,
    pub nat_succ: Option<NameId>,
    pub nat_ops: Vec<(NameId, NatOp)>,
    pub bool_true: Option<NameId>,
    pub bool_false: Option<NameId>,
    pub string: Option<NameId>,
    pub string_mk: Option<NameId>,
    pub char: Option<NameId>,
    pub char_of_nat: Option<NameId>,
    pub list_nil: Option<NameId>,
    pub list_cons: Option<NameId>,
    pub eq: Option<NameId>,
    pub eq_refl: Option<NameId>,
    pub quot: Option<NameId>,
    pub quot_mk: Option<NameId>,
    pub quot_lift: Option<NameId>,
    pub quot_ind: Option<NameId>,
    pub opt_param: Option<NameId>,
    pub out_param: Option<NameId>,
    pub semi_out_param: Option<NameId>,
    pub auto_param: Option<NameId>,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum NatOp {
    Add,
    Sub,
    Mul,
    Div,
    Mod,
    Gcd,
    Beq,
    Ble,
    Land,
    Lor,
    Xor,
    ShiftLeft,
    ShiftRight,
    Pow,
    Log2,
}

impl Builtins {
    pub fn resolve(lookup: impl Fn(&str) -> Option<NameId>) -> Self {
        use NatOp::*;
        let ops = [
            ("Nat.add", Add),
            ("Nat.sub", Sub),
            ("Nat.mul", Mul),
            ("Nat.div", Div),
            ("Nat.mod", Mod),
            ("Nat.gcd", Gcd),
            ("Nat.beq", Beq),
            ("Nat.ble", Ble),
            ("Nat.land", Land),
            ("Nat.lor", Lor),
            ("Nat.xor", Xor),
            ("Nat.shiftLeft", ShiftLeft),
            ("Nat.shiftRight", ShiftRight),
            ("Nat.pow", Pow),
            ("Nat.log2", Log2),
        ];
        Builtins {
            nat: lookup("Nat"),
            nat_zero: lookup("Nat.zero"),
            nat_succ: lookup("Nat.succ"),
            nat_ops: ops.iter().filter_map(|(s, op)| lookup(s).map(|n| (n, *op))).collect(),
            bool_true: lookup("Bool.true"),
            bool_false: lookup("Bool.false"),
            string: lookup("String"),
            string_mk: lookup("String.mk"),
            char: lookup("Char"),
            char_of_nat: lookup("Char.ofNat"),
            list_nil: lookup("List.nil"),
            list_cons: lookup("List.cons"),
            eq: lookup("Eq"),
            eq_refl: lookup("Eq.refl"),
            quot: lookup("Quot"),
            quot_mk: lookup("Quot.mk"),
            quot_lift: lookup("Quot.lift"),
            quot_ind: lookup("Quot.ind"),
            opt_param: lookup("optParam"),
            out_param: lookup("outParam"),
            semi_out_param: lookup("semiOutParam"),
            auto_param: lookup("autoParam"),
        }
    }
}

#[derive(Default)]
pub struct KEnv {
    pub consts: FxHashMap<NameId, Arc<ConstInfo>>,
    pub builtins: Builtins,
}

impl KEnv {
    pub fn get(&self, n: NameId) -> Option<Arc<ConstInfo>> {
        self.consts.get(&n).cloned()
    }
}
