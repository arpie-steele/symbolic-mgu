//! Boolean evaluation of terms.
//!
//! This module provides functionality for evaluating terms where
//! all metavariables and nodes are boolean-valued. It supports
//! tautology testing and truth table evaluation using bit-wise
//! operations on primitive unsigned integers and `BigUint`.
//!
//! # Primary Use Case: Tautology Testing
//!
//! The main purpose of this module is to verify that logical formulas
//! are tautologies (true for all possible variable assignments). This
//! is critical for:
//!
//! - **Condensed detachment**: Verifying axioms and derived theorems
//! - **Theorem proving**: Checking that proof steps are logically valid
//! - **Truth table generation**: Computing truth values for all input combinations
//!
//! The module automatically selects the most efficient evaluation strategy
//! based on the number of Boolean variables in the formula:
//!
//! | Variables | Type Used | Truth Table Size | Memory |
//! |-----------|-----------|------------------|--------|
//! | 0         | `bool`    | 1 row            | 1 bit  |
//! | 1-3       | `u8`      | 2-8 rows         | 8 bits |
//! | 4         | `u16`     | 16 rows          | 16 bits |
//! | 5         | `u32`     | 32 rows          | 32 bits |
//! | 6         | `u64`     | 64 rows          | 64 bits |
//! | 7         | `u128`    | 128 rows         | 128 bits |
//! | 8-20      | `BigUint` | 256-1,048,576 rows | Variable |
//!
//! # Future Enhancements
//!
//! The evaluator could be enhanced with structural short-circuit
//! evaluation for tautological patterns:
//!
//! - **`φ → φ`**: Always true (any term implies itself)
//! - **`φ ↔ φ`**: Always true (any term is equivalent to itself)
//!
//! This would enable verification of definitions involving these
//! patterns without requiring full evaluation of the sub-terms.
//! For example, the True definition `⊤ ↔ (∀x x = x → ∀x x = x)`
//! contains the pattern `ψ → ψ` where `ψ = ∀x x = x`, which could
//! be recognized as tautological regardless of whether `ψ` contains
//! quantifiers or other non-propositional constructs.
//!
//! Implementation approach:
//! 1. Before evaluating `Implies(a, b)` or `Biimp(a, b)`, check
//!    if `a` and `b` are structurally identical Boolean-valued
//!    terms
//! 2. If identical, return `true_value(num_bits)` immediately
//!    without recursion
//! 3. Otherwise, proceed with normal evaluation
//!
//! This would require adding an equality check (e.g., `a == b`
//! where `a` and `b` are `EnumTerm` references) before the evaluation
//! logic in `eval_implies` and `eval_biimp` within the `eval_map`
//! function.

pub(crate) mod generated_enum;

use crate::{
    ub_prim_impl, BooleanSimpleOp, Metavariable, MguError, Node, NodeByte, SimpleType, Term, Type,
};
use std::collections::HashSet;
use std::convert::TryInto;
use std::fmt::{Debug as DebugTrait, Display};
use std::marker::PhantomData;
use std::ops::{BitAnd, BitOr, BitXor, Not};

/// A Node wrapper for `BooleanSimpleOp` which works with any Type that implements Boolean.
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub struct BooleanSimpleNode<Ty: Type>(BooleanSimpleOp, PhantomData<Ty>);

impl<Ty: Type> Display for BooleanSimpleNode<Ty> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        Display::fmt(&(self.0), f)
    }
}

impl<Ty: Type> Node for BooleanSimpleNode<Ty> {
    type Type = Ty;

    fn get_type_and_index(&self) -> Result<(Self::Type, usize), MguError> {
        Ok((Self::Type::try_boolean()?, (self.0) as usize))
    }

    fn get_arity(&self) -> Result<usize, MguError> {
        Ok(((self.0) as usize) >> 8)
    }

    fn get_slot_type(&self, index: usize) -> Result<Self::Type, MguError> {
        let n = ((self.0) as usize) >> 8;
        if index < n {
            Ok(Self::Type::try_boolean()?)
        } else {
            Err(MguError::from_index_and_len::<SimpleType, usize, usize>(
                None, index, n,
            ))
        }
    }
}

impl BooleanSimpleOp {
    /// Evaluate the Boolean operator on 0 inputs.
    ///
    /// This works only for `BooleanSimpleOp::True0 `and `BooleanSimpleOp::False0` and returns None for operators with higher arities.
    pub fn eval0<B, U, const N: usize>(&self) -> Option<B>
    where
        B: UnsignedBits<U, N>,
        U: Clone + BitAnd<Output = U> + BitOr<Output = U> + BitXor<Output = U>,
    {
        use BooleanSimpleOp::*;
        if self.get_arity() > 0 {
            return None;
        }
        Some(match self {
            False0 => B::from_bool(false),
            True0 => B::from_bool(true),
            _ => return None,
        })
    }

    /// Evaluate the Boolean operator on 1 input.
    ///
    /// This works for `BooleanSimpleOp::True0` and `BooleanSimpleOp::False0`. but ignores the argument.
    /// This works similarly for `BooleanSimpleOp::True1` and `BooleanSimpleOp::False1` and as expected for `BooleanSimpleOp::NotA1` and `BooleanSimpleOp::IdA1`
    /// and returns None for operators with higher arities.
    pub fn eval1<B, U, const N: usize>(&self, a: &B) -> Option<B>
    where
        B: UnsignedBits<U, N>,
        U: Clone + BitAnd<Output = U> + BitOr<Output = U> + BitXor<Output = U>,
    {
        use BooleanSimpleOp::*;
        if self.get_arity() > 1 {
            return None;
        }
        Some(match self {
            False0 | False1 => B::from_bool(false),
            True0 | True1 => B::from_bool(true),
            NotA1 => !a.clone(),
            IdA1 => a.clone(),
            _ => return None,
        })
    }

    /// Evaluate the Boolean operator on 2 inputs.
    ///
    /// This silently ignores the last arguments if the operator has arity lower than 2
    /// and returns None for higher arities.
    pub fn eval2<B, U, const N: usize>(&self, a: &B, b: &B) -> Option<B>
    where
        B: UnsignedBits<U, N>,
        U: Clone + BitAnd<Output = U> + BitOr<Output = U> + BitXor<Output = U>,
    {
        use BooleanSimpleOp::*;
        if self.get_arity() > 2 {
            return None;
        }
        Some(match self {
            False0 | False1 | False2 => B::from_bool(false),
            True0 | True1 | True2 => B::from_bool(true),
            NotA1 | NotA2 => !a.clone(),
            IdA1 | IdA2 => a.clone(),
            NotB2 => !b.clone(),
            IdB2 => b.clone(),
            NotOrAB2 => !(a.clone() | b.clone()),
            NotImpliesAB2 => a.clone() & !b.clone(),
            NotImpliesBA2 => !a.clone() & b.clone(),
            NotAndAB2 => !(a.clone() & b.clone()),
            XorAB2 => a.clone() ^ b.clone(),
            BiimpAB2 => !(a.clone() ^ b.clone()),
            AndAB2 => a.clone() & b.clone(),
            ImpliesBA2 => a.clone() | !b.clone(),
            ImpliesAB2 => !a.clone() | b.clone(),
            OrAB2 => a.clone() | b.clone(),
            _ => return None,
        })
    }

    /// Evaluate the Boolean operator on 3 inputs.
    ///
    /// This silently ignores the last arguments if the operator has arity lower than 3
    /// and returns None for higher arities, if any are ever defined.
    pub fn eval3<B, U, const N: usize>(&self, a: &B, b: &B, c: &B) -> Option<B>
    where
        B: UnsignedBits<U, N>,
        U: Clone + BitAnd<Output = U> + BitOr<Output = U> + BitXor<Output = U>,
    {
        use BooleanSimpleOp::*;
        if self.get_arity() > 3 {
            return None;
        }
        Some(match self {
            False0 | False1 | False2 | False3 => B::from_bool(false),
            NotOr3ABC3 => !(a.clone() | b.clone() | c.clone()),
            NotOr3NotABC3 => !(!a.clone() | b.clone() | c.clone()),
            NotOrBC3 => !(b.clone() | c.clone()),
            NotOr3ANotBC3 => !(a.clone() | !b.clone() | c.clone()),
            NotOrAC3 => !(a.clone() | c.clone()),
            AndNotCXorAB3 => !c.clone() & (a.clone() ^ b.clone()),
            NotOrCAndAB3 => !(c.clone() | (a.clone() & b.clone())),
            And3ABNotC3 => a.clone() & b.clone() & !c.clone(),
            NotOrCXorAB3 => !(c.clone() | (a.clone() ^ b.clone())),
            NotImpliesAC3 => a.clone() & !c.clone(),
            AndNotCOrANotB3 => !c.clone() & (a.clone() | !b.clone()),
            NotImpliesBC3 => b.clone() & !c.clone(),
            AndNotCOrNotAB3 => !c.clone() & (!a.clone() | b.clone()),
            AndNotCOrAB3 => !c.clone() & (a.clone() | b.clone()),
            NotC3 => !c.clone(),
            NotOr3ABNotC3 => !(a.clone() | b.clone() | !c.clone()),
            NotOrAB2 | NotOrAB3 => !(a.clone() | b.clone()),
            AndNotBXorAC3 => !b.clone() & (a.clone() ^ c.clone()),
            NotOrBAndAC3 => !(b.clone() | (a.clone() & c.clone())),
            AndNotAXorBC3 => !a.clone() & (b.clone() ^ c.clone()),
            NotOrAAndBC3 => !(a.clone() | (b.clone() & c.clone())),
            NotOrAndABNotXor3ABC3 => {
                !((a.clone() & b.clone()) | (!a.clone() ^ b.clone() ^ c.clone()))
            }
            NotMajority3ABC3 => {
                !(a.clone() & b.clone() | a.clone() & c.clone() | b.clone() & c.clone())
            }
            AndBiimpABXorAC3 => !(a.clone() ^ b.clone()) & (a.clone() ^ c.clone()),
            NotOrXorABAndAC3 => !((a.clone() ^ b.clone()) | (a.clone() & c.clone())),
            NotOrBiimpACAndBC3 => !(!(a.clone() ^ c.clone()) | (b.clone() & c.clone())),
            NotIfACB3 => !(a.clone() & c.clone() | !a.clone() & b.clone()),
            NotOrBiimpBCAndAC3 => !(!(b.clone() ^ c.clone()) | (a.clone() & c.clone())),
            NotIfBCA3 => !(b.clone() & c.clone() | !b.clone() & a.clone()),
            XorCOrAB3 => c.clone() ^ (a.clone() | b.clone()),
            ImpliesOrABNotC3 => !(a.clone() | b.clone()) | !c.clone(),
            And3ANotBC3 => a.clone() & !b.clone() & c.clone(),
            NotOrBXorAC3 => !(b.clone() | (a.clone() ^ c.clone())),
            NotImpliesAB2 | NotImpliesAB3 => a.clone() & !b.clone(),
            AndNotBOrANotC3 => !b.clone() & (a.clone() | !c.clone()),
            AndXorABBiimpAC3 => (a.clone() ^ b.clone()) & !(a.clone() ^ c.clone()),
            NotOrXorACAndAB3 => !((a.clone() ^ c.clone()) | (a.clone() & b.clone())),
            NotOrBiimpABAndBC3 => !(!(a.clone() ^ b.clone()) | (b.clone() & c.clone())),
            NotIfABC3 => !(a.clone() & b.clone() | !a.clone() & c.clone()),
            AndAXorBC3 => a.clone() & (b.clone() ^ c.clone()),
            NotOrAndBCXor3ABC3 => !((b.clone() & c.clone()) | (a.clone() ^ b.clone() ^ c.clone())),
            NotOrNotAAndBC3 => !(!a.clone() | (b.clone() & c.clone())),
            NotMajority3NotABC3 => {
                !(!a.clone() & b.clone() | !a.clone() & c.clone() | b.clone() & c.clone())
            }
            AndXorBCOrAB3 => (b.clone() ^ c.clone()) & (a.clone() | b.clone()),
            XorCOrNotAB3 => c.clone() ^ (!a.clone() | b.clone()),
            IfBNotCA3 => b.clone() & !c.clone() | !b.clone() & a.clone(),
            ImpliesImpliesABNotC3 => !(!a.clone() | b.clone()) | !c.clone(),
            NotImpliesCB3 => c.clone() & !b.clone(),
            AndNotBOrNotAC3 => !b.clone() & (!a.clone() | c.clone()),
            AndNotBOrAC3 => !b.clone() & (a.clone() | c.clone()),
            NotB2 | NotB3 => !b.clone(),
            NotOrBiimpBCAndAB3 => !(!(b.clone() ^ c.clone()) | (a.clone() & b.clone())),
            NotIfCBA3 => !(c.clone() & b.clone() | !c.clone() & a.clone()),
            XorBOrAC3 => b.clone() ^ (a.clone() | c.clone()),
            ImpliesOrACNotB3 => !(a.clone() | c.clone()) | !b.clone(),
            AndXorBCOrAC3 => (b.clone() ^ c.clone()) & (a.clone() | c.clone()),
            XorBOrNotAC3 => b.clone() ^ (!a.clone() | c.clone()),
            IfCNotBA3 => c.clone() & !b.clone() | !c.clone() & a.clone(),
            ImpliesImpliesACNotB3 => !(!a.clone() | c.clone()) | !b.clone(),
            XorBC3 => b.clone() ^ c.clone(),
            NotAndBiimpBCOrAB3 => !(!(b.clone() ^ c.clone()) & (a.clone() | b.clone())),
            OrXorCBAndNotCA3 => (c.clone() ^ b.clone()) | (!c.clone() & a.clone()),
            NotAndBC3 => !(b.clone() & c.clone()),
            And3NotABC3 => !a.clone() & b.clone() & c.clone(),
            NotOrAXorBC3 => !(a.clone() | (b.clone() ^ c.clone())),
            AndXorABXorAC3 => (a.clone() ^ b.clone()) & (a.clone() ^ c.clone()),
            NotOrXorBCAndAB3 => !((b.clone() ^ c.clone()) | (a.clone() & b.clone())),
            NotImpliesBA2 | NotImpliesBA3 => !a.clone() & b.clone(),
            AndNotAOrBNotC3 => !a.clone() & (b.clone() | !c.clone()),
            NotOrBiimpABAndAC3 => !(!(a.clone() ^ b.clone()) | (a.clone() & c.clone())),
            NotIfBAC3 => !(b.clone() & a.clone() | !b.clone() & c.clone()),
            AndBXorAC3 => b.clone() & (a.clone() ^ c.clone()),
            NotOrAndACXor3ABC3 => !((a.clone() & c.clone()) | (a.clone() ^ b.clone() ^ c.clone())),
            AndXorACOrAB3 => (a.clone() ^ c.clone()) & (a.clone() | b.clone()),
            BiimpCAndNotAB3 => !(c.clone() ^ (!a.clone() & b.clone())),
            NotOrNotBAndAC3 => !(!b.clone() | (a.clone() & c.clone())),
            NotMajority3ANotBC3 => {
                !(a.clone() & !b.clone() | a.clone() & c.clone() | !b.clone() & c.clone())
            }
            IfANotCB3 => a.clone() & !c.clone() | !a.clone() & b.clone(),
            ImpliesImpliesBANotC3 => !(!b.clone() | a.clone()) | !c.clone(),
            NotImpliesCA3 => c.clone() & !a.clone(),
            AndNotAOrNotBC3 => !a.clone() & (!b.clone() | c.clone()),
            NotOrBiimpACAndAB3 => !(!(a.clone() ^ c.clone()) | (a.clone() & b.clone())),
            NotIfCAB3 => !(c.clone() & a.clone() | !c.clone() & b.clone()),
            AndNotAOrBC3 => !a.clone() & (b.clone() | c.clone()),
            NotA1 | NotA2 | NotA3 => !a.clone(),
            XorAOrBC3 => a.clone() ^ (b.clone() | c.clone()),
            ImpliesOrBCNotA3 => !(b.clone() | c.clone()) | !a.clone(),
            AndXorACOrBC3 => (a.clone() ^ c.clone()) & (b.clone() | c.clone()),
            XorAOrNotBC3 => a.clone() ^ (!b.clone() | c.clone()),
            XorAC3 => a.clone() ^ c.clone(),
            NotAndBiimpACOrAB3 => !(!(a.clone() ^ c.clone()) & (a.clone() | b.clone())),
            IfCNotAB3 => c.clone() & !a.clone() | !c.clone() & b.clone(),
            ImpliesImpliesBCNotA3 => !(!b.clone() | c.clone()) | !a.clone(),
            OrXorACAndNotAB3 => (a.clone() ^ c.clone()) | (!a.clone() & b.clone()),
            NotAndAC3 => !(a.clone() & c.clone()),
            AndCXorAB3 => c.clone() & (a.clone() ^ b.clone()),
            NotOrAndABXor3ABC3 => !((a.clone() & b.clone()) | (a.clone() ^ b.clone() ^ c.clone())),
            AndXorABOrAC3 => (a.clone() ^ b.clone()) & (a.clone() | c.clone()),
            BiimpBAndNotAC3 => !(b.clone() ^ (!a.clone() & c.clone())),
            AndXorABOrBC3 => (a.clone() ^ b.clone()) & (b.clone() | c.clone()),
            BiimpAAndNotBC3 => !(a.clone() ^ (!b.clone() & c.clone())),
            XorAB2 | XorAB3 => a.clone() ^ b.clone(),
            NotAndBiimpABOrAC3 => !(!(a.clone() ^ b.clone()) & (a.clone() | c.clone())),
            NotOrNotOrABXor3ABC3 => {
                !(!(a.clone() | b.clone()) | (a.clone() ^ b.clone() ^ c.clone()))
            }
            NotXor3ABC3 => !a.clone() ^ b.clone() ^ c.clone(),
            XorAAndBC3 => a.clone() ^ (b.clone() & c.clone()),
            OrNotXor3ABCAndANotB3 => {
                (!a.clone() ^ b.clone() ^ c.clone()) | (a.clone() & !b.clone())
            }
            XorBAndAC3 => b.clone() ^ (a.clone() & c.clone()),
            OrNotXor3ABCAndNotAB3 => {
                (!a.clone() ^ b.clone() ^ c.clone()) | (!a.clone() & b.clone())
            }
            OrXorABAndANotC3 => (a.clone() ^ b.clone()) | (a.clone() & !c.clone()),
            ImpliesCXorAB3 => !c.clone() | (a.clone() ^ b.clone()),
            NotOrNotCAndAB3 => !(!c.clone() | (a.clone() & b.clone())),
            NotMajority3ABNotC3 => {
                !(a.clone() & b.clone() | a.clone() & !c.clone() | b.clone() & !c.clone())
            }
            IfANotBC3 => a.clone() & !b.clone() | !a.clone() & c.clone(),
            ImpliesImpliesCANotB3 => !(!c.clone() | a.clone()) | !b.clone(),
            IfBNotAC3 => b.clone() & !a.clone() | !b.clone() & c.clone(),
            ImpliesImpliesCBNotA3 => !(!c.clone() | b.clone()) | !a.clone(),
            OrXorABAndNotAC3 => (a.clone() ^ b.clone()) | (!a.clone() & c.clone()),
            NotAndAB2 | NotAndAB3 => !(a.clone() & b.clone()),
            XorCAndAB3 => c.clone() ^ (a.clone() & b.clone()),
            OrNotXor3ABCAndNotAC3 => {
                (!a.clone() ^ b.clone() ^ c.clone()) | (!a.clone() & c.clone())
            }
            OrXorACAndANotB3 => (a.clone() ^ c.clone()) | (a.clone() & !b.clone()),
            ImpliesBXorAC3 => !b.clone() | (a.clone() ^ c.clone()),
            OrXorCBAndCNotA3 => (c.clone() ^ b.clone()) | (c.clone() & !a.clone()),
            ImpliesAXorBC3 => !a.clone() | (b.clone() ^ c.clone()),
            OrXorABXorAC3 => (a.clone() ^ b.clone()) | (a.clone() ^ c.clone()),
            NotAnd3ABC3 => !(a.clone() & b.clone() & c.clone()),
            And3ABC3 => a.clone() & b.clone() & c.clone(),
            NotOrXorABXorAC3 => !((a.clone() ^ b.clone()) | (a.clone() ^ c.clone())),
            AndABiimpBC3 => a.clone() & !(b.clone() ^ c.clone()),
            AndBiimpBCOrANotB3 => !(b.clone() ^ c.clone()) & (a.clone() | !b.clone()),
            AndBBiimpAC3 => b.clone() & !(a.clone() ^ c.clone()),
            AndBiimpACOrNotAB3 => !(a.clone() ^ c.clone()) & (!a.clone() | b.clone()),
            NotOrAndNotACNotXor3ABC3 => {
                !((!a.clone() & c.clone()) | (!a.clone() ^ b.clone() ^ c.clone()))
            }
            BiimpCAndAB3 => !(c.clone() ^ (a.clone() & b.clone())),
            AndAB2 | AndAB3 => a.clone() & b.clone(),
            AndBiimpABOrANotC3 => !(a.clone() ^ b.clone()) & (a.clone() | !c.clone()),
            AndAOrBNotC3 => a.clone() & (b.clone() | !c.clone()),
            IfBANotC3 => b.clone() & a.clone() | !b.clone() & !c.clone(),
            AndBOrANotC3 => b.clone() & (a.clone() | !c.clone()),
            IfABNotC3 => a.clone() & b.clone() | !a.clone() & !c.clone(),
            Majority3ABNotC3 => {
                a.clone() & b.clone() | a.clone() & !c.clone() | b.clone() & !c.clone()
            }
            ImpliesCAndAB3 => !c.clone() | (a.clone() & b.clone()),
            AndCBiimpAB3 => c.clone() & !(a.clone() ^ b.clone()),
            AndBiimpABOrNotAC3 => !(a.clone() ^ b.clone()) & (!a.clone() | c.clone()),
            NotOrAndNotABNotXor3ABC3 => {
                !((!a.clone() & b.clone()) | (!a.clone() ^ b.clone() ^ c.clone()))
            }
            BiimpBAndAC3 => !(b.clone() ^ (a.clone() & c.clone())),
            NotOrAndANotBNotXor3ABC3 => {
                !((a.clone() & !b.clone()) | (!a.clone() ^ b.clone() ^ c.clone()))
            }
            BiimpAAndBC3 => !(a.clone() ^ (b.clone() & c.clone())),
            Xor3ABC3 => a.clone() ^ b.clone() ^ c.clone(),
            OrXor3ABCNotOrAB3 => (a.clone() ^ b.clone() ^ c.clone()) | !(a.clone() | b.clone()),
            AndBiimpABOrAC3 => !(a.clone() ^ b.clone()) & (a.clone() | c.clone()),
            BiimpAB2 | BiimpAB3 => !(a.clone() ^ b.clone()),
            XorAAndNotBC3 => a.clone() ^ (!b.clone() & c.clone()),
            NotAndXorABOrBC3 => !((a.clone() ^ b.clone()) & (b.clone() | c.clone())),
            XorBAndNotAC3 => b.clone() ^ (!a.clone() & c.clone()),
            NotAndXorABOrAC3 => !((a.clone() ^ b.clone()) & (a.clone() | c.clone())),
            OrXor3ABCAndAB3 => (a.clone() ^ b.clone() ^ c.clone()) | (a.clone() & b.clone()),
            ImpliesXorABNotC3 => !(a.clone() ^ b.clone()) | !c.clone(),
            AndAC3 => a.clone() & c.clone(),
            AndBiimpACOrANotB3 => !(a.clone() ^ c.clone()) & (a.clone() | !b.clone()),
            AndAOrNotBC3 => a.clone() & (!b.clone() | c.clone()),
            IfCANotB3 => c.clone() & a.clone() | !c.clone() & !b.clone(),
            AndBiimpACOrAB3 => !(a.clone() ^ c.clone()) & (a.clone() | b.clone()),
            BiimpAC3 => !(a.clone() ^ c.clone()),
            BiimpAOrNotBC3 => !(a.clone() ^ (!b.clone() | c.clone())),
            NotAndXorACOrBC3 => !((a.clone() ^ c.clone()) & (b.clone() | c.clone())),
            AndAOrBC3 => a.clone() & (b.clone() | c.clone()),
            BiimpAOrBC3 => !(a.clone() ^ (b.clone() | c.clone())),
            IdA1 | IdA2 | IdA3 => a.clone(),
            ImpliesOrBCA3 => !(b.clone() | c.clone()) | a.clone(),
            IfCAB3 => c.clone() & a.clone() | !c.clone() & b.clone(),
            OrBiimpACAndAB3 => !(a.clone() ^ c.clone()) | (a.clone() & b.clone()),
            ImpliesImpliesBCA3 => !(!b.clone() | c.clone()) | a.clone(),
            ImpliesCA3 => !c.clone() | a.clone(),
            AndCOrANotB3 => c.clone() & (a.clone() | !b.clone()),
            IfACNotB3 => a.clone() & c.clone() | !a.clone() & !b.clone(),
            Majority3ANotBC3 => {
                a.clone() & !b.clone() | a.clone() & c.clone() | !b.clone() & c.clone()
            }
            ImpliesBAndAC3 => !b.clone() | (a.clone() & c.clone()),
            XorCAndNotAB3 => c.clone() ^ (!a.clone() & b.clone()),
            NotAndXorACOrAB3 => !((a.clone() ^ c.clone()) & (a.clone() | b.clone())),
            OrXor3ABCAndAC3 => (a.clone() ^ b.clone() ^ c.clone()) | (a.clone() & c.clone()),
            ImpliesXorACNotB3 => !(a.clone() ^ c.clone()) | !b.clone(),
            IfBAC3 => b.clone() & a.clone() | !b.clone() & c.clone(),
            OrBiimpABAndAC3 => !(a.clone() ^ b.clone()) | (a.clone() & c.clone()),
            ImpliesImpliesCBA3 => !(!c.clone() | b.clone()) | a.clone(),
            ImpliesBA2 | ImpliesBA3 => a.clone() | !b.clone(),
            OrXorBCAndAB3 => (b.clone() ^ c.clone()) | (a.clone() & b.clone()),
            NotAndXorABXorAC3 => !((a.clone() ^ b.clone()) & (a.clone() ^ c.clone())),
            OrXorBCA3 => (b.clone() ^ c.clone()) | a.clone(),
            NotAnd3NotABC3 => !(!a.clone() & b.clone() & c.clone()),
            AndBC3 => b.clone() & c.clone(),
            AndBiimpBCOrNotAB3 => !(b.clone() ^ c.clone()) & (!a.clone() | b.clone()),
            AndBiimpBCOrAB3 => !(b.clone() ^ c.clone()) & (a.clone() | b.clone()),
            BiimpBC3 => !(b.clone() ^ c.clone()),
            AndBOrNotAC3 => b.clone() & (!a.clone() | c.clone()),
            IfCBNotA3 => c.clone() & b.clone() | !c.clone() & !a.clone(),
            BiimpBOrNotAC3 => !(b.clone() ^ (!a.clone() | c.clone())),
            NotAndXorBCOrAC3 => !((b.clone() ^ c.clone()) & (a.clone() | c.clone())),
            AndBOrAC3 => b.clone() & (a.clone() | c.clone()),
            BiimpBOrAC3 => !(b.clone() ^ (a.clone() | c.clone())),
            IfCBA3 => c.clone() & b.clone() | !c.clone() & a.clone(),
            OrBiimpBCAndAB3 => !(b.clone() ^ c.clone()) | (a.clone() & b.clone()),
            IdB2 | IdB3 => b.clone(),
            ImpliesOrACB3 => !(a.clone() | c.clone()) | b.clone(),
            ImpliesImpliesACB3 => !(!a.clone() | c.clone()) | b.clone(),
            ImpliesCB3 => !c.clone() | b.clone(),
            AndCOrNotAB3 => c.clone() & (!a.clone() | b.clone()),
            IfBCNotA3 => b.clone() & c.clone() | !b.clone() & !a.clone(),
            BiimpCOrNotAB3 => !(c.clone() ^ (!a.clone() | b.clone())),
            NotAndXorBCOrAB3 => !((b.clone() ^ c.clone()) & (a.clone() | b.clone())),
            Majority3NotABC3 => {
                !a.clone() & b.clone() | !a.clone() & c.clone() | b.clone() & c.clone()
            }
            ImpliesAAndBC3 => !a.clone() | (b.clone() & c.clone()),
            OrXor3ABCAndBC3 => (a.clone() ^ b.clone() ^ c.clone()) | (b.clone() & c.clone()),
            ImpliesXorBCNotA3 => !(b.clone() ^ c.clone()) | !a.clone(),
            IfABC3 => a.clone() & b.clone() | !a.clone() & c.clone(),
            OrBiimpABAndBC3 => !(a.clone() ^ b.clone()) | (b.clone() & c.clone()),
            OrXorACAndAB3 => (a.clone() ^ c.clone()) | (a.clone() & b.clone()),
            OrBiimpABXorAC3 => !(a.clone() ^ b.clone()) | (a.clone() ^ c.clone()),
            ImpliesImpliesCAB3 => !(!c.clone() | a.clone()) | b.clone(),
            ImpliesAB2 | ImpliesAB3 => !a.clone() | b.clone(),
            OrXorACB3 => (a.clone() ^ c.clone()) | b.clone(),
            NotAnd3ANotBC3 => !(a.clone() & !b.clone() & c.clone()),
            AndCOrAB3 => c.clone() & (a.clone() | b.clone()),
            BiimpCOrAB3 => !(c.clone() ^ (a.clone() | b.clone())),
            IfBCA3 => b.clone() & c.clone() | !b.clone() & a.clone(),
            OrBiimpBCAndAC3 => !(b.clone() ^ c.clone()) | (a.clone() & c.clone()),
            IfACB3 => a.clone() & c.clone() | !a.clone() & b.clone(),
            OrBiimpACAndBC3 => !(a.clone() ^ c.clone()) | (b.clone() & c.clone()),
            OrXorABAndAC3 => (a.clone() ^ b.clone()) | (a.clone() & c.clone()),
            OrXorABBiimpAC3 => (a.clone() ^ b.clone()) | !(a.clone() ^ c.clone()),
            Majority3ABC3 => a.clone() & b.clone() | a.clone() & c.clone() | b.clone() & c.clone(),
            OrNotXor3ABCAndAB3 => (!a.clone() ^ b.clone() ^ c.clone()) | (a.clone() & b.clone()),
            OrAndBCA3 => (b.clone() & c.clone()) | a.clone(),
            ImpliesXorBCA3 => !(b.clone() ^ c.clone()) | a.clone(),
            OrAndACB3 => (a.clone() & c.clone()) | b.clone(),
            ImpliesXorACB3 => !(a.clone() ^ c.clone()) | b.clone(),
            OrAB2 | OrAB3 => a.clone() | b.clone(),
            Or3ABNotC3 => a.clone() | b.clone() | !c.clone(),
            IdC3 => c.clone(),
            ImpliesOrABC3 => !(a.clone() | b.clone()) | c.clone(),
            ImpliesImpliesABC3 => !(!a.clone() | b.clone()) | c.clone(),
            ImpliesBC3 => !b.clone() | c.clone(),
            ImpliesImpliesBAC3 => !(!b.clone() | a.clone()) | c.clone(),
            ImpliesAC3 => !a.clone() | c.clone(),
            OrXorABC3 => (a.clone() ^ b.clone()) | c.clone(),
            NotAnd3ABNotC3 => !(a.clone() & b.clone() & !c.clone()),
            OrAndABC3 => (a.clone() & b.clone()) | c.clone(),
            ImpliesXorABC3 => !(a.clone() ^ b.clone()) | c.clone(),
            OrAC3 => a.clone() | c.clone(),
            Or3ANotBC3 => a.clone() | !b.clone() | c.clone(),
            OrBC3 => b.clone() | c.clone(),
            Or3NotABC3 => !a.clone() | b.clone() | c.clone(),
            Or3ABC3 => (a.clone()) | (b.clone()) | (c.clone()),
            True0 | True1 | True2 | True3 => B::from_bool(true),
        })
    }
}

#[cfg(feature = "bigint")]
use num_bigint::BigUint;

/// Checks if a Boolean `NodeByte` node is supported by this module.
///
/// | node | arity |
/// | ---- | ----- |
/// | [`True`] | 0 |
/// | [`False`] | 0 |
/// | [`Not`] | 1 |
/// | [`Implies`] | 2 |
/// | [`Biimp`] | 2 |
/// | [`And`] | 2 |
/// | [`Or`] | 2 |
/// | [`NotAnd`] | 2 |
/// | [`ExclusiveOr`] | 2 |
/// | [`NotOr`] | 2 |
/// | [`And3`] | 3 |
/// | [`Or3`] | 3 |
/// | [`SumFromAdder`] | 3 |
/// | [`CarryFromAdder`] | 3 |
/// | [`LogicalIf`] | 3 |
///
/// [`True`]: `crate::NodeByte::True`
/// [`False`]: `crate::NodeByte::False`
/// [`Not`]: `crate::NodeByte::Not`
/// [`Implies`]: `crate::NodeByte::Implies`
/// [`Biimp`]: `crate::NodeByte::Biimp`
/// [`And`]: `crate::NodeByte::And`
/// [`Or`]: `crate::NodeByte::Or`
/// [`NotAnd`]: `crate::NodeByte::NotAnd`
/// [`ExclusiveOr`]: `crate::NodeByte::ExclusiveOr`
/// [`NotOr`]: `crate::NodeByte::NotOr`
/// [`And3`]: `crate::NodeByte::And3`
/// [`Or3`]: `crate::NodeByte::Or3`
/// [`SumFromAdder`]: `crate::NodeByte::SumFromAdder`
/// [`CarryFromAdder`]: `crate::NodeByte::CarryFromAdder`
/// [`LogicalIf`]: `crate::NodeByte::LogicalIf`
pub fn is_supported_op(node: &NodeByte) -> bool {
    use NodeByte::*;
    matches!(
        node,
        True | False
            | Not
            | Implies
            | Biimp
            | And
            | Or
            | NotAnd
            | ExclusiveOr
            | NotOr
            | And3
            | Or3
            | SumFromAdder // aka `ExclusiveOr3`
            | CarryFromAdder // aka `Majority3`
            | LogicalIf
    )
}

/// Test if a Boolean term is a tautology.
///
/// This function works with any type implementing [`Term`], making it suitable for
/// use with [`crate::EnumTerm`], database-backed terms, or custom term implementations.
///
/// Automatically selects the most efficient evaluation strategy based on the number
/// of Boolean variables:
/// - **0 variables**: Uses `bool` (1 bit)
/// - **1-3 variables**: Uses `u8` (8 bits)
/// - **4 variables**: Uses `u16` (16 bits)
/// - **5 variables**: Uses `u32` (32 bits)
/// - **6 variables**: Uses `u64` (64 bits)
/// - **7 variables**: Uses `u128` (128 bits)
/// - **8-20 variables**: Uses `BigUint` (requires `bigint` feature)
///
/// # Errors
///
/// Returns an error if:
/// - The term contains non-Boolean variables
/// - The term contains more than 20 variables
/// - Evaluation fails
///
/// # Examples
///
/// ```ignore
/// use symbolic_mgu::{EnumTerm, MetaByte, NodeByte, SimpleType, test_tautology};
///
/// // Test law of excluded middle: p ∨ ¬p
/// // Works with any Term implementation, here using EnumTerm:
/// let p = EnumTerm::Leaf(MetaByte::try_from_type_and_index(SimpleType::Boolean, 0)?);
/// let not_p = EnumTerm::NodeOrLeaf(NodeByte::Not, vec![p.clone()]);
/// let law = EnumTerm::NodeOrLeaf(NodeByte::Or, vec![p, not_p]);
///
/// assert!(test_tautology(&law)?);  // Should be true
/// ```
pub fn test_tautology<T, Ty, V, No>(term: &T) -> Result<bool, MguError>
where
    T: Term<Ty, V, No>,
    Ty: Type,
    V: Metavariable<Type = Ty>,
    No: Node<Type = Ty> + TryInto<NodeByte>,
    <No as TryInto<NodeByte>>::Error: Into<MguError>,
{
    // Collect all metavariables
    let mut vars_set: HashSet<V> = HashSet::new();
    term.collect_metavariables(&mut vars_set)?;
    let vars: Vec<V> = vars_set.into_iter().collect();
    let n = vars.len();

    // Check all variables are Boolean
    let all_bools = {
        let mut all_bool = true;
        for var in &vars {
            if var.get_type()? != Ty::try_boolean()? {
                all_bool = false;
                break;
            }
        }
        all_bool
    };

    if !all_bools {
        // Find the first non-Boolean variable to report in error
        let non_bool_type = {
            let mut found_type = Ty::try_boolean()?;
            for var in &vars {
                let var_type = var.get_type()?;
                if var_type != Ty::try_boolean()? {
                    found_type = var_type;
                    break;
                }
            }
            found_type
        };
        let expected_type = Ty::try_boolean()?;
        return Err(MguError::from_found_and_expected_types(
            false,
            &non_bool_type,
            &expected_type,
        ));
    }

    // Select evaluation strategy based on variable count
    match n {
        0 => {
            let result =
                <bool as UnsignedBits<bool, 0>>::eval_boolean_term::<T, Ty, V, No, _>(term, &vars)?;
            let expected = <bool as UnsignedBits<bool, 0>>::from_bool(true);
            Ok(result == expected)
        }
        1..=3 => {
            let result =
                <u8 as UnsignedBits<u8, 3>>::eval_boolean_term::<T, Ty, V, No, _>(term, &vars)?;
            let expected = <u8 as UnsignedBits<u8, 3>>::from_bool(true);
            Ok(result == expected)
        }
        4 => {
            let result =
                <u16 as UnsignedBits<u16, 4>>::eval_boolean_term::<T, Ty, V, No, _>(term, &vars)?;
            let expected = <u16 as UnsignedBits<u16, 4>>::from_bool(true);
            Ok(result == expected)
        }
        5 => {
            let result =
                <u32 as UnsignedBits<u32, 5>>::eval_boolean_term::<T, Ty, V, No, _>(term, &vars)?;
            let expected = <u32 as UnsignedBits<u32, 5>>::from_bool(true);
            Ok(result == expected)
        }
        6 => {
            let result =
                <u64 as UnsignedBits<u64, 6>>::eval_boolean_term::<T, Ty, V, No, _>(term, &vars)?;
            let expected = <u64 as UnsignedBits<u64, 6>>::from_bool(true);
            Ok(result == expected)
        }
        7 => {
            let result =
                <u128 as UnsignedBits<u128, 7>>::eval_boolean_term::<T, Ty, V, No, _>(term, &vars)?;
            let expected = <u128 as UnsignedBits<u128, 7>>::from_bool(true);
            Ok(result == expected)
        }
        #[cfg(feature = "bigint")]
        8..=20 => {
            let result = SomeBits::<20>::eval_boolean_term::<T, Ty, V, No, _>(term, &vars)?;
            let expected = SomeBits::<20>::from_bool(true);
            Ok(result == expected)
        }
        #[cfg(not(feature = "bigint"))]
        8..=20 => Err(MguError::AllocationError(
            "Support for 8-20 variables requires the 'bigint' feature".to_owned(),
        )),
        _ => Err(MguError::AllocationError(
            "Too many variables to represent (maximum is 20)".to_owned(),
        )),
    }
}

/// Isolate the differences between various unsigned representations.
pub trait UnsignedBits<U, const N: usize>:
    Clone
    + DebugTrait
    + BitXor<Output = Self>
    + BitAnd<Output = Self>
    + BitOr<Output = Self>
    + Not<Output = Self>
where
    U: Clone + BitAnd<Output = U> + BitOr<Output = U> + BitXor<Output = U>,
{
    /// Mask for one's complement.
    fn mask() -> U;

    /// Return true if mask is the maximum value supported.
    fn is_mask_maximum(&self) -> bool;

    /// Return number of bits.
    fn n_bits() -> usize {
        1 << N
    }

    /// Return base 2 log of number of bits.
    fn n() -> usize {
        N
    }

    /// Convert a base-type value to this type.
    fn from_orig(orig: U) -> Self;

    /// Convert a Boolean value to this type.
    fn from_bool(orig: bool) -> Self {
        let m = Self::mask();
        Self::from_orig(if orig { m } else { m.clone() ^ m })
    }

    /// Set or reset a bit from 0..`2^N`, inclusive.
    ///
    /// # Errors
    ///
    /// TODO.
    fn set_bit(&mut self, bit_pos: u64, value: bool) -> Result<(), MguError>;

    /// Convenience method to evaluate a single node with no children.
    ///
    /// # Errors
    ///
    /// TODO.
    fn eval_boolean_nullary(node: &NodeByte) -> Result<Self, MguError> {
        use NodeByte::*;
        match node {
            True => Ok(Self::from_bool(true)),
            False => Ok(Self::from_bool(false)),
            _ => Err(MguError::UnknownError(690)),
        }
    }

    /// Convenience method to evaluate a single node with specified child.
    ///
    /// # Errors
    ///
    /// TODO.
    fn eval_boolean_unary<V>(&node: &NodeByte, a: &Self) -> Result<Self, MguError>
    where
        V: Metavariable,
    {
        use NodeByte::*;
        match node {
            Not => Ok(!a.clone()),
            _ => Err(MguError::UnknownError(691)),
        }
    }

    /// Convenience method to evaluate a single node with specified children.
    ///
    /// # Errors
    ///
    /// TODO.
    fn eval_boolean_binary<V>(node: &NodeByte, a: &Self, b: &Self) -> Result<Self, MguError>
    where
        V: Metavariable,
    {
        use NodeByte::*;
        match node {
            Implies => Ok((!a.clone()) | b.clone()),
            Biimp => Ok(!(a.clone() ^ b.clone())),
            And => Ok(a.clone() & b.clone()),
            Or => Ok(a.clone() | b.clone()),
            NotAnd => Ok(!(a.clone() & b.clone())),
            ExclusiveOr => Ok(a.clone() ^ b.clone()),
            NotOr => Ok(!(a.clone() | b.clone())),
            _ => Err(MguError::UnknownError(692)),
        }
    }

    /// Convenience method to evaluate a single node with specified children.
    ///
    /// # Errors
    ///
    /// TODO.
    fn eval_boolean_ternary<V>(
        node: &NodeByte,
        a: &Self,
        b: &Self,
        c: &Self,
    ) -> Result<Self, MguError>
    where
        V: Metavariable,
    {
        use NodeByte::*;
        match node {
            And3 => Ok(a.clone() & b.clone() & c.clone()),
            Or3 => Ok(a.clone() | b.clone() | c.clone()),
            SumFromAdder => Ok(a.clone() ^ b.clone() ^ c.clone()),
            CarryFromAdder => {
                Ok((a.clone() & b.clone()) | (a.clone() & c.clone()) | (b.clone() & c.clone()))
            }
            LogicalIf => Ok((a.clone() & b.clone()) | (!a.clone() & c.clone())),
            _ => Err(MguError::UnknownError(693)),
        }
    }

    /// Convenience method to evaluate a single node with specified children.
    ///
    /// # Errors
    ///
    /// TODO.
    fn eval_boolean_node<V>(node: &NodeByte, children: &[Self]) -> Result<Self, MguError>
    where
        V: Metavariable,
    {
        use NodeByte::*;
        match node {
            True | False => {
                let len = children.len();
                if len != 0 {
                    return Err(MguError::SlotsMismatch(len, 0));
                }
                Self::eval_boolean_nullary(node)
            }
            Not => {
                let len = children.len();
                if len != 1 {
                    return Err(MguError::SlotsMismatch(len, 1));
                }
                Self::eval_boolean_unary::<V>(node, &children[0])
            }
            Implies | Biimp | And | Or | NotAnd | ExclusiveOr | NotOr => {
                let len = children.len();
                if len != 2 {
                    return Err(MguError::SlotsMismatch(len, 2));
                }
                Self::eval_boolean_binary::<V>(node, &children[0], &children[1])
            }
            And3 | Or3 | SumFromAdder | CarryFromAdder | LogicalIf => {
                let len = children.len();
                if len != 3 {
                    return Err(MguError::SlotsMismatch(len, 3));
                }
                Self::eval_boolean_ternary::<V>(node, &children[0], &children[1], &children[2])
            }
            _ => Err(MguError::UnknownError(700)),
        }
    }

    /// Evaluate a Boolean term with N variables to a truth table representation.
    ///
    /// This method works with any type implementing [`Term`], recursively evaluating
    /// the term using bit-wise operations to compute all possible truth values in parallel.
    ///
    /// # Parameters
    ///
    /// - `term`: The term to evaluate (any implementation of [`Term`])
    /// - `vars`: Ordered list of variables appearing in the term
    ///
    /// # Errors
    ///
    /// Returns an error if:
    /// - A metavariable is not Boolean-typed
    /// - A variable is not in the provided `vars` list
    /// - The variable index exceeds the bit capacity (N)
    /// - Node conversion fails
    fn eval_boolean_term<T, Ty, V, No, CvtErr>(
        term: &T,
        vars: &[V],
    ) -> Result<Self, MguError>
    where
        T: Term<Ty, V, No>,
        Ty: Type,
        V: Metavariable<Type = Ty>,
        No: Node<Type = Ty> + TryInto<NodeByte, Error = CvtErr>,
        CvtErr: Into<MguError>,
    {
        if term.is_metavariable() {
            // Leaf case: extract the metavariable
            let var = term.get_metavariable().ok_or(MguError::UnknownError(701))?;
            let typ = var.get_type()?;
            if !typ.is_boolean() {
                return Err(MguError::from_found_and_expected_types(
                    false,
                    &typ,
                    &(Ty::try_boolean()?),
                ));
            }
            let index = vars
                .iter()
                .position(|v| *v == var)
                .ok_or(MguError::UnknownError(702))?;
            if index >= N {
                return Err(MguError::UnknownError(703));
            }

            if index >= 20 {
                // Reasonable limit?
                return Err(MguError::AllocationError(format!(
                    "Variable index {index} exceeds maximum 19 for 2^20 bits"
                )));
            }

            let num_bits = 1u64 << (N as u32);
            let period = 1_u64 << (index + 1);
            if num_bits < period {
                return Err(MguError::AllocationError(format!(
                    "num_bits ({num_bits}) must be at least 2^{} ({period}) for variable index {index}",
                    index + 1
                )));
            }

            // Create alternating pattern: period = `2^(var_index+1)`, on for `2^var_index` bits
            // Pattern repeats with period `2^(var_index+1)`, and is high for the second half of each period

            let on_length = 1_u64 << index;

            let mut result = Self::from_bool(false);
            for bit_pos in 0..num_bits {
                // Check if this bit position is in the "on" part of its period
                let pos_in_period = bit_pos % period;
                if pos_in_period >= on_length {
                    result.set_bit(bit_pos, true)?;
                }
            }

            Ok(result)
        } else {
            // Node case: evaluate the node with its children
            let node = term.get_node().ok_or(MguError::UnknownError(704))?;
            let node_converted: NodeByte = node.try_into().map_err(|e| e.into())?;
            use NodeByte::*;
            match node_converted {
                True | False | Not | Implies | Biimp | And | Or | NotAnd | ExclusiveOr
                | NotOr | And3 | Or3 | SumFromAdder | CarryFromAdder | LogicalIf => {
                    let child_values = term
                        .get_children()
                        .map(|t| Self::eval_boolean_term(t, vars))
                        .collect::<Vec<_>>();
                    if let Some(Err(err)) = child_values.iter().find(|x| (*x).is_err()) {
                        return Err(err.clone());
                    }
                    let child_values = child_values
                        .into_iter()
                        .map(|x| x.unwrap())
                        .collect::<Vec<_>>();
                    Self::eval_boolean_node::<V>(&node_converted, &child_values)
                }
                _ => Err(MguError::UnknownError(700)),
            }
        }
    }
}

impl UnsignedBits<bool, 0> for bool {
    fn mask() -> bool {
        true
    }
    fn is_mask_maximum(&self) -> bool {
        true
    }

    fn from_orig(orig: bool) -> Self {
        orig
    }

    fn set_bit(&mut self, bit_pos: u64, value: bool) -> Result<(), MguError> {
        if bit_pos != 0 {
            Err(MguError::UnknownError(120))
        } else {
            *self = value;
            Ok(())
        }
    }
}

ub_prim_impl!(UnsignedBits; u8, 0; 3);
ub_prim_impl!(UnsignedBits; u8, 1; 3);
ub_prim_impl!(UnsignedBits; u8, 2; 3);
ub_prim_impl!(UnsignedBits; u8, 3; 3);
ub_prim_impl!(UnsignedBits; u16, 0; 4);
ub_prim_impl!(UnsignedBits; u16, 1; 4);
ub_prim_impl!(UnsignedBits; u16, 2; 4);
ub_prim_impl!(UnsignedBits; u16, 3; 4);
ub_prim_impl!(UnsignedBits; u16, 4; 4);
ub_prim_impl!(UnsignedBits; u32, 0; 5);
ub_prim_impl!(UnsignedBits; u32, 1; 5);
ub_prim_impl!(UnsignedBits; u32, 2; 5);
ub_prim_impl!(UnsignedBits; u32, 3; 5);
ub_prim_impl!(UnsignedBits; u32, 4; 5);
ub_prim_impl!(UnsignedBits; u32, 5; 5);
ub_prim_impl!(UnsignedBits; u64, 0; 6);
ub_prim_impl!(UnsignedBits; u64, 1; 6);
ub_prim_impl!(UnsignedBits; u64, 2; 6);
ub_prim_impl!(UnsignedBits; u64, 3; 6);
ub_prim_impl!(UnsignedBits; u64, 4; 6);
ub_prim_impl!(UnsignedBits; u64, 5; 6);
ub_prim_impl!(UnsignedBits; u64, 6; 6);
ub_prim_impl!(UnsignedBits; u128, 0; 7);
ub_prim_impl!(UnsignedBits; u128, 1; 7);
ub_prim_impl!(UnsignedBits; u128, 2; 7);
ub_prim_impl!(UnsignedBits; u128, 3; 7);
ub_prim_impl!(UnsignedBits; u128, 4; 7);
ub_prim_impl!(UnsignedBits; u128, 5; 7);
ub_prim_impl!(UnsignedBits; u128, 6; 7);
ub_prim_impl!(UnsignedBits; u128, 7; 7);

/// A wrapper around `BigUint` to have it model truth tables on N Boolean variables.
#[cfg(feature = "bigint")]
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SomeBits<const N: usize>(BigUint);

#[cfg(feature = "bigint")]
impl<const N: usize> SomeBits<N> {
    /// A mask with `2^(2^N)` ones.
    pub fn all_ones_mask() -> Self {
        let one: BigUint = 1u32.into();
        Self((one.clone() << (1 << N)) - one)
    }
}

#[cfg(feature = "bigint")]
impl<const N: usize> UnsignedBits<SomeBits<N>, N> for SomeBits<N> {
    fn mask() -> SomeBits<N> {
        Self::all_ones_mask()
    }
    fn is_mask_maximum(&self) -> bool {
        false
    }
    fn n() -> usize {
        N
    }

    fn from_orig(orig: SomeBits<N>) -> Self {
        orig
    }

    fn set_bit(&mut self, bit_pos: u64, value: bool) -> Result<(), MguError> {
        let high_index = 1u64 << N;
        if bit_pos < high_index {
            self.0.set_bit(bit_pos, value);
            Ok(())
        } else {
            Err(MguError::UnknownError(119))
        }
    }
}

#[cfg(feature = "bigint")]
impl<const N: usize> BitAnd for SomeBits<N> {
    type Output = SomeBits<N>;

    fn bitand(self, rhs: Self) -> Self::Output {
        (SomeBits::<N>)(self.0 & rhs.0)
    }
}

#[cfg(feature = "bigint")]
impl<const N: usize> Not for SomeBits<N> {
    type Output = SomeBits<N>;

    fn not(self) -> Self::Output {
        (SomeBits::<N>)(self.0 ^ SomeBits::<N>::all_ones_mask().0)
    }
}

#[cfg(feature = "bigint")]
impl<const N: usize> BitOr for SomeBits<N> {
    type Output = SomeBits<N>;

    fn bitor(self, rhs: Self) -> Self::Output {
        (SomeBits::<N>)(self.0 | rhs.0)
    }
}

#[cfg(feature = "bigint")]
impl<const N: usize> BitXor for SomeBits<N> {
    type Output = SomeBits<N>;

    fn bitxor(self, rhs: Self) -> Self::Output {
        (SomeBits::<N>)(self.0 ^ rhs.0)
    }
}

#[cfg(feature = "bigint")]
impl<const N: usize> std::fmt::LowerHex for SomeBits<N> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        std::fmt::LowerHex::fmt(&(self.0), f) // delegate to `BigUint`'s implementation
    }
}

#[cfg(feature = "bigint")]
impl<const N: usize> std::fmt::UpperHex for SomeBits<N> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        std::fmt::UpperHex::fmt(&(self.0), f) // delegate to `BigUint`'s implementation
    }
}

#[cfg(feature = "bigint")]
impl<const N: usize> std::fmt::Display for SomeBits<N> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        std::fmt::Display::fmt(&(self.0), f) // delegate to `BigUint`'s implementation
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use strum::VariantArray;

    /// Test that all `BooleanSimpleOp` variants evaluate to their correct truth table codes.
    ///
    /// This test builds the truth table for each operation by evaluating it on all
    /// possible input combinations (using a, b, c from the standard test vectors),
    /// then verifies the result matches the operation's code.
    #[test]
    fn all_variants_make_truth_tables() {
        // Test all 278 operations
        for variant in BooleanSimpleOp::VARIANTS {
            let arity = variant.get_arity();
            let expected_code: u8 = variant.get_code3();

            let mut truth_table: u8 = 0;
            for c in [true, false] {
                for b in [true, false] {
                    for a in [true, false] {
                        let result = match arity {
                            0 => variant
                                .eval0::<bool, bool, 0>()
                                .unwrap_or_else(|| panic!("eval0 failed for {}", variant)),
                            1 => variant
                                .eval1::<bool, bool, 0>(&a)
                                .unwrap_or_else(|| panic!("eval1 failed for {}", variant)),
                            2 => variant
                                .eval2::<bool, bool, 0>(&a, &b)
                                .unwrap_or_else(|| panic!("eval2 failed for {}", variant)),
                            3 => variant
                                .eval3::<bool, bool, 0>(&a, &b, &c)
                                .unwrap_or_else(|| panic!("eval3 failed for {}", variant)),
                            _ => panic!("Unexpected arity {} for {}", arity, variant),
                        };
                        truth_table <<= 1;
                        truth_table |= if result { 1 } else { 0 };
                    }
                }
            }

            assert_eq!(
                truth_table, expected_code,
                "Truth table mismatch for {variant} (arity={arity}): \
                 got 0x{truth_table:02x}, expected 0x{expected_code:02x}",
            );
        }
    }

    /// Test that all `BooleanSimpleOp` variants evaluate to their correct truth table codes.
    ///
    /// This test builds the truth table for each operation by evaluating it on all
    /// possible input combinations (using a, b, c from the standard test vectors),
    /// then verifies the result matches the operation's code.
    #[test]
    fn all_variants_u8_truth_tables() {
        // Standard test vectors for 3 variables
        // a = 10101010 = 0xaa
        // b = 11001100 = 0xcc
        // c = 11110000 = 0xf0

        let a = <u8 as UnsignedBits<u8, 3>>::from_orig(0xaa);
        let b = <u8 as UnsignedBits<u8, 3>>::from_orig(0xcc);
        let c = <u8 as UnsignedBits<u8, 3>>::from_orig(0xf0);
        let mask = <u8 as UnsignedBits<u8, 3>>::mask();

        // Test all 278 operations
        for variant in BooleanSimpleOp::VARIANTS {
            let arity = variant.get_arity();
            let expected_code = variant.get_code3();

            let result = match arity {
                0 => variant
                    .eval0::<u8, u8, 3>()
                    .unwrap_or_else(|| panic!("eval0 failed for {}", variant)),
                1 => variant
                    .eval1::<u8, u8, 3>(&a)
                    .unwrap_or_else(|| panic!("eval1 failed for {}", variant)),
                2 => variant
                    .eval2::<u8, u8, 3>(&a, &b)
                    .unwrap_or_else(|| panic!("eval2 failed for {}", variant)),
                3 => variant
                    .eval3::<u8, u8, 3>(&a, &b, &c)
                    .unwrap_or_else(|| panic!("eval3 failed for {}", variant)),
                _ => panic!("Unexpected arity {} for {}", arity, variant),
            } & mask;

            assert_eq!(
                result, expected_code,
                "Truth table mismatch for {variant} (arity={arity}): \
                 got 0x{result:02x}, expected 0x{expected_code:02x}",
            );
        }
    }

    /// Test that all `BooleanSimpleOp` variants evaluate to their correct truth table codes.
    ///
    /// This test builds the truth table for each operation by evaluating it on all
    /// possible input combinations (using a, b, c from the standard test vectors),
    /// then verifies the result matches the operation's code.
    #[test]
    fn all_variants_u64_truth_tables() {
        // Standard test vectors for 3 variables
        // a = 10101010 = 0xaa
        // b = 11001100 = 0xcc
        // c = 11110000 = 0xf0

        let a = <u64 as UnsignedBits<u64, 3>>::from_orig(0xaaaa_aaaa_aaaa_aaaa);
        let b = <u64 as UnsignedBits<u64, 3>>::from_orig(0xcccc_cccc_cccc_cccc);
        let c = <u64 as UnsignedBits<u64, 3>>::from_orig(0xf0f0_f0f0_f0f0_f0f0);
        let mask = <u64 as UnsignedBits<u64, 3>>::mask();

        // Test all 278 operations
        for variant in BooleanSimpleOp::VARIANTS {
            let arity = variant.get_arity();
            let expected_code = <u64 as UnsignedBits<u64, 3>>::from_orig(
                0x0101_0101_0101_0101u64 * variant.get_code3() as u64,
            );

            let result = match arity {
                0 => variant
                    .eval0::<u64, u64, 3>()
                    .unwrap_or_else(|| panic!("eval0 failed for {}", variant)),
                1 => variant
                    .eval1::<u64, u64, 3>(&a)
                    .unwrap_or_else(|| panic!("eval1 failed for {}", variant)),
                2 => variant
                    .eval2::<u64, u64, 3>(&a, &b)
                    .unwrap_or_else(|| panic!("eval2 failed for {}", variant)),
                3 => variant
                    .eval3::<u64, u64, 3>(&a, &b, &c)
                    .unwrap_or_else(|| panic!("eval3 failed for {}", variant)),
                _ => panic!("Unexpected arity {} for {}", arity, variant),
            } & mask;

            assert_eq!(
                result, expected_code,
                "Truth table mismatch for {variant} (arity={arity}): \
                 got 0x{result:016x}, expected 0x{expected_code:016x}",
            );
        }
    }

    /// Test that all `BooleanSimpleOp` variants evaluate to their correct truth table codes.
    ///
    /// This test builds the truth table for each operation by evaluating it on all
    /// possible input combinations (using a, b, c from the standard test vectors),
    /// then verifies the result matches the operation's code.
    #[test]
    #[cfg(feature = "bigint")]
    fn all_variants_bigint_truth_tables() {
        // Standard test vectors for 3 variables
        // a = 10101010 = 0xaa
        // b = 11001100 = 0xcc
        // c = 11110000 = 0xf0
        let a = SomeBits::<3>(BigUint::from(0xaa_u32));
        let b = SomeBits::<3>(BigUint::from(0xcc_u32));
        let c = SomeBits::<3>(BigUint::from(0xf0_u32));

        // Test all 278 operations
        for variant in BooleanSimpleOp::VARIANTS {
            let arity = variant.get_arity();
            let expected_code = variant.get_code3();

            let result = match arity {
                0 => variant
                    .eval0::<SomeBits<3>, SomeBits<3>, 3>()
                    .unwrap_or_else(|| panic!("eval0 failed for {}", variant)),
                1 => variant
                    .eval1::<SomeBits<3>, SomeBits<3>, 3>(&a)
                    .unwrap_or_else(|| panic!("eval1 failed for {}", variant)),
                2 => variant
                    .eval2::<SomeBits<3>, SomeBits<3>, 3>(&a, &b)
                    .unwrap_or_else(|| panic!("eval2 failed for {}", variant)),
                3 => variant
                    .eval3::<SomeBits<3>, SomeBits<3>, 3>(&a, &b, &c)
                    .unwrap_or_else(|| panic!("eval3 failed for {}", variant)),
                _ => panic!("Unexpected arity {} for {}", arity, variant),
            };

            assert_eq!(
                result,
                SomeBits::<3>(BigUint::from(expected_code)),
                "Truth table mismatch for {variant} (arity={arity}): \
                 got 0x{result:02x}, expected 0x{expected_code:02x}",
            );
        }
    }

    /// Test a few specific operations to ensure correct behavior.
    #[test]
    fn specific_operations() {
        let a: u8 = 0xaa;
        let b: u8 = 0xcc;
        let c: u8 = 0xf0;

        // Test constants
        assert_eq!(BooleanSimpleOp::False0.eval0::<u8, u8, 3>().unwrap(), 0x00);
        assert_eq!(BooleanSimpleOp::True0.eval0::<u8, u8, 3>().unwrap(), 0xff);

        // Test basic binary operations
        assert_eq!(
            BooleanSimpleOp::AndAB2.eval2::<u8, u8, 3>(&a, &b).unwrap(),
            a & b
        );
        assert_eq!(
            BooleanSimpleOp::OrAB2.eval2::<u8, u8, 3>(&a, &b).unwrap(),
            a | b
        );
        assert_eq!(
            BooleanSimpleOp::XorAB2.eval2::<u8, u8, 3>(&a, &b).unwrap(),
            a ^ b
        );
        assert_eq!(
            BooleanSimpleOp::NotAndAB2
                .eval2::<u8, u8, 3>(&a, &b)
                .unwrap(),
            !(a & b)
        );

        // Test basic ternary operations
        assert_eq!(
            BooleanSimpleOp::Or3ABC3
                .eval3::<u8, u8, 3>(&a, &b, &c)
                .unwrap(),
            a | b | c
        );
        assert_eq!(
            BooleanSimpleOp::And3ABC3
                .eval3::<u8, u8, 3>(&a, &b, &c)
                .unwrap(),
            a & b & c
        );

        // Test `Xor3` (odd parity)
        assert_eq!(
            BooleanSimpleOp::Xor3ABC3
                .eval3::<u8, u8, 3>(&a, &b, &c)
                .unwrap(),
            a ^ b ^ c
        );

        // Test Majority (at least 2 of 3 true)
        let majority = (a & b) | (a & c) | (b & c);
        assert_eq!(
            BooleanSimpleOp::Majority3ABC3
                .eval3::<u8, u8, 3>(&a, &b, &c)
                .unwrap(),
            majority
        );
    }

    /// Test law of excluded middle: p ∨ ¬p is a tautology.
    #[test]
    fn tautology_simple() {
        use crate::{EnumTerm, MetaByte, SimpleType};

        // Create variable p
        let p_var = MetaByte::try_from_type_and_index(SimpleType::Boolean, 0).unwrap();
        let p_term = EnumTerm::<SimpleType, MetaByte, NodeByte>::Leaf(p_var);

        // Create ¬p
        let not_p = EnumTerm::NodeOrLeaf(NodeByte::Not, vec![p_term.clone()]);

        // Create p ∨ ¬p
        let law_of_excluded_middle = EnumTerm::NodeOrLeaf(NodeByte::Or, vec![p_term, not_p]);

        // Should be a tautology
        assert!(
            test_tautology(&law_of_excluded_middle).unwrap(),
            "Law of excluded middle (p ∨ ¬p) should be a tautology"
        );
    }

    /// Test that p ∧ ¬p is not a tautology (it's a contradiction).
    #[test]
    fn tautology_not_tautology() {
        use crate::{EnumTerm, MetaByte, SimpleType};

        // Create variable p
        let p_var = MetaByte::try_from_type_and_index(SimpleType::Boolean, 0).unwrap();
        let p_term = EnumTerm::<SimpleType, MetaByte, NodeByte>::Leaf(p_var);

        // Create ¬p
        let not_p = EnumTerm::NodeOrLeaf(NodeByte::Not, vec![p_term.clone()]);

        // Create p ∧ ¬p
        let contradiction = EnumTerm::NodeOrLeaf(NodeByte::And, vec![p_term, not_p]);

        // Should NOT be a tautology (it's a contradiction)
        assert!(
            !test_tautology(&contradiction).unwrap(),
            "Contradiction (p ∧ ¬p) should not be a tautology"
        );
    }

    /// Test <span style="white-space: nowrap">De Morgan's</span> law: ¬(p ∧ q) ↔ (¬p ∨ ¬q) is a tautology.
    #[test]
    fn tautology_de_morgan() {
        use crate::{EnumTerm, MetaByte, SimpleType};

        // Create variables p and q
        let p_var = MetaByte::try_from_type_and_index(SimpleType::Boolean, 0).unwrap();
        let q_var = MetaByte::try_from_type_and_index(SimpleType::Boolean, 1).unwrap();
        let p = EnumTerm::<SimpleType, MetaByte, NodeByte>::Leaf(p_var);
        let q = EnumTerm::Leaf(q_var);

        // Create p ∧ q
        let p_and_q = EnumTerm::NodeOrLeaf(NodeByte::And, vec![p.clone(), q.clone()]);

        // Create ¬(p ∧ q)
        let not_p_and_q = EnumTerm::NodeOrLeaf(NodeByte::Not, vec![p_and_q]);

        // Create ¬p and ¬q
        let not_p = EnumTerm::NodeOrLeaf(NodeByte::Not, vec![p]);
        let not_q = EnumTerm::NodeOrLeaf(NodeByte::Not, vec![q]);

        // Create ¬p ∨ ¬q
        let not_p_or_not_q = EnumTerm::NodeOrLeaf(NodeByte::Or, vec![not_p, not_q]);

        // Create ¬(p ∧ q) ↔ (¬p ∨ ¬q)
        let de_morgan = EnumTerm::NodeOrLeaf(NodeByte::Biimp, vec![not_p_and_q, not_p_or_not_q]);

        // Should be a tautology
        assert!(
            test_tautology(&de_morgan).unwrap(),
            "De Morgan's law should be a tautology"
        );
    }
}
