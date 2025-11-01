//! Next-gen Boolean evaluation.

pub(crate) mod generated_enum;

use crate::{BooleanSimpleOp, EnumTerm, Metavariable, MguError, Node, NodeByte, SimpleType, Type};
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
        if self.get_arity() > 0 {
            return None;
        }
        Self::eval1::<B, U, N>(self, &(B::from_bool(false))) // TODO: replace this with a 2-branch match.
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
        if self.get_arity() > 1 {
            return None;
        }
        Self::eval2::<B, U, N>(self, a, &(B::from_bool(false))) // TODO: replace this with a 4-branch match.
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
        if self.get_arity() > 2 {
            return None;
        }
        Self::eval3::<B, U, N>(self, a, b, &(B::from_bool(false))) // TODO: replace this with a 16-branch match.
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
            NotOr3ABC3 => todo!(),
            NotOr3NotABC3 => todo!(),
            NotOrBC3 => todo!(),
            NotOr3ANotBC3 => todo!(),
            NotOrAC3 => todo!(),
            AndNotCXorAB3 => todo!(),
            NotOrCAndAB3 => todo!(),
            And3ABNotC3 => todo!(),
            NotOrCXorAB3 => todo!(),
            NotImpliesAC3 => todo!(),
            AndNotCOrANotB3 => todo!(),
            NotImpliesBC3 => todo!(),
            AndNotCOrNotAB3 => todo!(),
            AndNotCOrAB3 => todo!(),
            NotC3 => !c.clone(),
            NotOr3ABNotC3 => todo!(),
            NotOrAB2 | NotOrAB3 => !(a.clone() | b.clone()),
            AndNotBXorAC3 => todo!(),
            NotOrBAndAC3 => todo!(),
            AndNotAXorBC3 => todo!(),
            NotOrAAndBC3 => todo!(),
            NotOrAndABNotXor3ABC3 => todo!(),
            NotMajority3ABC3 => todo!(),
            AndBiimpABXorAC3 => todo!(),
            NotOrXorABAndAC3 => todo!(),
            NotOrBiimpACAndBC3 => todo!(),
            NotIfACB3 => todo!(),
            NotOrBiimpBCAndAC3 => todo!(),
            NotIfBCA3 => todo!(),
            XorCOrAB3 => todo!(),
            ImpliesOrABNotC3 => todo!(),
            And3ANotBC3 => todo!(),
            NotOrBXorAC3 => todo!(),
            NotImpliesAB2 | NotImpliesAB3 => a.clone() & !b.clone(),
            AndNotBOrANotC3 => todo!(),
            AndXorABBiimpAC3 => todo!(),
            NotOrXorACAndAB3 => todo!(),
            NotOrBiimpABAndBC3 => todo!(),
            NotIfABC3 => todo!(),
            AndAXorBC3 => todo!(),
            NotOrAndBCXor3ABC3 => todo!(),
            NotOrNotAAndBC3 => todo!(),
            NotMajority3NotABC3 => todo!(),
            AndXorBCOrAB3 => todo!(),
            XorCOrNotAB3 => todo!(),
            IfBNotCA3 => todo!(),
            ImpliesImpliesABNotC3 => todo!(),
            NotImpliesCB3 => todo!(),
            AndNotBOrNotAC3 => todo!(),
            AndNotBOrAC3 => todo!(),
            NotB2 | NotB3 => !b.clone(),
            NotOrBiimpBCAndAB3 => todo!(),
            NotIfCBA3 => todo!(),
            XorBOrAC3 => todo!(),
            ImpliesOrACNotB3 => todo!(),
            AndXorBCOrAC3 => todo!(),
            XorBOrNotAC3 => todo!(),
            IfCNotBA3 => todo!(),
            ImpliesImpliesACNotB3 => todo!(),
            XorBC3 => todo!(),
            NotAndBiimpBCOrAB3 => todo!(),
            OrXorCBAndNotCA3 => todo!(),
            NotAndBC3 => todo!(),
            And3NotABC3 => todo!(),
            NotOrAXorBC3 => todo!(),
            AndXorABXorAC3 => todo!(),
            NotOrXorBCAndAB3 => todo!(),
            NotImpliesBA2 | NotImpliesBA3 => !a.clone() & b.clone(),
            AndNotAOrBNotC3 => todo!(),
            NotOrBiimpABAndAC3 => todo!(),
            NotIfBAC3 => todo!(),
            AndBXorAC3 => todo!(),
            NotOrAndACXor3ABC3 => todo!(),
            AndXorACOrAB3 => todo!(),
            BiimpCAndNotAB3 => todo!(),
            NotOrNotBAndAC3 => todo!(),
            NotMajority3ANotBC3 => todo!(),
            IfANotCB3 => todo!(),
            ImpliesImpliesBANotC3 => todo!(),
            NotImpliesCA3 => todo!(),
            AndNotAOrNotBC3 => todo!(),
            NotOrBiimpACAndAB3 => todo!(),
            NotIfCAB3 => todo!(),
            AndNotAOrBC3 => todo!(),
            NotA1 | NotA2 | NotA3 => !a.clone(),
            XorAOrBC3 => todo!(),
            ImpliesOrBCNotA3 => todo!(),
            AndXorACOrBC3 => todo!(),
            XorAOrNotBC3 => todo!(),
            XorAC3 => todo!(),
            NotAndBiimpACOrAB3 => todo!(),
            IfCNotAB3 => todo!(),
            ImpliesImpliesBCNotA3 => todo!(),
            OrXorACAndNotAB3 => todo!(),
            NotAndAC3 => todo!(),
            AndCXorAB3 => todo!(),
            NotOrAndABXor3ABC3 => todo!(),
            AndXorABOrAC3 => todo!(),
            BiimpBAndNotAC3 => todo!(),
            AndXorABOrBC3 => todo!(),
            BiimpAAndNotBC3 => todo!(),
            XorAB2 | XorAB3 => a.clone() ^ b.clone(),
            NotAndBiimpABOrAC3 => todo!(),
            NotOrNotOrABXor3ABC3 => todo!(),
            NotXor3ABC3 => todo!(),
            XorAAndBC3 => todo!(),
            OrNotXor3ABCAndANotB3 => todo!(),
            XorBAndAC3 => todo!(),
            OrNotXor3ABCAndNotAB3 => todo!(),
            OrXorABAndANotC3 => todo!(),
            ImpliesBiimpABNotC3 => todo!(),
            NotOrNotCAndAB3 => todo!(),
            NotMajority3ABNotC3 => todo!(),
            IfANotBC3 => todo!(),
            ImpliesImpliesCANotB3 => todo!(),
            IfBNotAC3 => todo!(),
            ImpliesImpliesCBNotA3 => todo!(),
            OrXorABAndNotAC3 => todo!(),
            NotAndAB2 | NotAndAB3 => !(a.clone() & b.clone()),
            XorCAndAB3 => todo!(),
            OrNotXor3ABCAndNotAC3 => todo!(),
            OrXorACAndANotB3 => todo!(),
            ImpliesBiimpACNotB3 => todo!(),
            OrXorCBAndCNotA3 => todo!(),
            ImpliesBiimpBCNotA3 => todo!(),
            OrXorABXorAC3 => todo!(),
            NotAnd3ABC3 => todo!(),
            And3ABC3 => todo!(),
            NotOrXorABXorAC3 => todo!(),
            AndABiimpBC3 => todo!(),
            AndBiimpBCOrANotB3 => todo!(),
            AndBBiimpAC3 => todo!(),
            AndBiimpACOrNotAB3 => todo!(),
            NotOrAndNotACNotXor3ABC3 => todo!(),
            BiimpCAndAB3 => todo!(),
            AndAB2 | AndAB3 => a.clone() & b.clone(),
            AndBiimpABOrANotC3 => todo!(),
            AndAOrBNotC3 => todo!(),
            IfBANotC3 => todo!(),
            AndBOrANotC3 => todo!(),
            IfABNotC3 => todo!(),
            Majority3ABNotC3 => todo!(),
            ImpliesNotAndABNotC3 => todo!(),
            AndCBiimpAB3 => todo!(),
            AndBiimpABOrNotAC3 => todo!(),
            NotOrAndNotABNotXor3ABC3 => todo!(),
            BiimpBAndAC3 => todo!(),
            NotOrAndANotBNotXor3ABC3 => todo!(),
            BiimpAAndBC3 => todo!(),
            Xor3ABC3 => todo!(),
            OrXor3ABCNotOrAB3 => todo!(),
            AndBiimpABOrAC3 => todo!(),
            BiimpAB2 | BiimpAB3 => !(a.clone() ^ b.clone()),
            XorAAndNotBC3 => todo!(),
            NotAndXorABOrBC3 => todo!(),
            XorBAndNotAC3 => todo!(),
            NotAndXorABOrAC3 => todo!(),
            OrXor3ABCAndAB3 => todo!(),
            ImpliesXorABNotC3 => todo!(),
            AndAC3 => todo!(),
            AndBiimpACOrANotB3 => todo!(),
            AndAOrNotBC3 => todo!(),
            IfCANotB3 => todo!(),
            AndBiimpACOrAB3 => todo!(),
            BiimpAC3 => todo!(),
            BiimpAOrNotBC3 => todo!(),
            NotAndXorACOrBC3 => todo!(),
            AndAOrBC3 => todo!(),
            BiimpAOrBC3 => todo!(),
            IdA1 | IdA2 | IdA3 => a.clone(),
            ImpliesOrBCA3 => todo!(),
            IfCAB3 => todo!(),
            OrBiimpACAndAB3 => todo!(),
            ImpliesImpliesBCA3 => todo!(),
            ImpliesCA3 => todo!(),
            AndCOrANotB3 => todo!(),
            IfACNotB3 => todo!(),
            Majority3ANotBC3 => todo!(),
            ImpliesNotAndACNotB3 => todo!(),
            XorCAndNotAB3 => todo!(),
            NotAndXorACOrAB3 => todo!(),
            OrXor3ABCAndAC3 => todo!(),
            ImpliesXorACNotB3 => todo!(),
            IfBAC3 => todo!(),
            OrBiimpABAndAC3 => todo!(),
            ImpliesImpliesCBA3 => todo!(),
            ImpliesBA2 | ImpliesBA3 => a.clone() | !b.clone(),
            OrXorBCAndAB3 => todo!(),
            NotAndXorABXorAC3 => todo!(),
            ImpliesBiimpBCA3 => todo!(),
            NotAnd3NotABC3 => todo!(),
            AndBC3 => todo!(),
            AndBiimpBCOrNotAB3 => todo!(),
            AndBiimpBCOrAB3 => todo!(),
            BiimpBC3 => todo!(),
            AndBOrNotAC3 => todo!(),
            IfCBNotA3 => todo!(),
            BiimpBOrNotAC3 => todo!(),
            NotAndXorBCOrAC3 => todo!(),
            AndBOrAC3 => todo!(),
            BiimpBOrAC3 => todo!(),
            IfCBA3 => todo!(),
            OrBiimpBCAndAB3 => todo!(),
            IdB2 | IdB3 => b.clone(),
            ImpliesOrACB3 => todo!(),
            ImpliesImpliesACB3 => todo!(),
            ImpliesCB3 => todo!(),
            AndCOrNotAB3 => todo!(),
            IfBCNotA3 => todo!(),
            BiimpCOrNotAB3 => todo!(),
            NotAndXorBCOrAB3 => todo!(),
            Majority3NotABC3 => todo!(),
            ImpliesNotAndBCNotA3 => todo!(),
            OrXor3ABCAndBC3 => todo!(),
            ImpliesXorBCNotA3 => todo!(),
            IfABC3 => todo!(),
            OrBiimpABAndBC3 => todo!(),
            OrXorACAndAB3 => todo!(),
            OrBiimpABXorAC3 => todo!(),
            ImpliesImpliesCAB3 => todo!(),
            ImpliesAB2 | ImpliesAB3 => !a.clone() | b.clone(),
            ImpliesBiimpACB3 => todo!(),
            NotAnd3ANotBC3 => todo!(),
            AndCOrAB3 => todo!(),
            BiimpCOrAB3 => todo!(),
            IfBCA3 => todo!(),
            OrBiimpBCAndAC3 => todo!(),
            IfACB3 => todo!(),
            OrBiimpACAndBC3 => todo!(),
            OrXorABAndAC3 => todo!(),
            OrXorABBiimpAC3 => todo!(),
            Majority3ABC3 => todo!(),
            OrNotXor3ABCAndAB3 => todo!(),
            ImpliesNotAndBCA3 => todo!(),
            ImpliesXorBCA3 => todo!(),
            ImpliesNotAndACB3 => todo!(),
            ImpliesXorACB3 => todo!(),
            OrAB2 | OrAB3 => a.clone() | b.clone(),
            Or3ABNotC3 => todo!(),
            IdC3 => c.clone(),
            ImpliesOrABC3 => todo!(),
            ImpliesImpliesABC3 => todo!(),
            ImpliesBC3 => todo!(),
            ImpliesImpliesBAC3 => todo!(),
            ImpliesAC3 => todo!(),
            ImpliesBiimpABC3 => todo!(),
            NotAnd3ABNotC3 => todo!(),
            ImpliesNotAndABC3 => todo!(),
            ImpliesXorABC3 => todo!(),
            OrAC3 => todo!(),
            Or3ANotBC3 => todo!(),
            OrBC3 => todo!(),
            Or3NotABC3 => todo!(),
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

    /// Evaluate Boolean term in N variables.
    ///
    /// # Errors
    ///
    /// TODO.
    fn eval_boolean_term<Ty, V, No, CvtErr>(
        term: &EnumTerm<Ty, V, No>,
        vars: &[V],
    ) -> Result<Self, MguError>
    where
        Ty: Type,
        V: Metavariable<Type = Ty>,
        No: Node<Type = Ty> + TryInto<NodeByte, Error = CvtErr>,
        CvtErr: Into<MguError>,
    {
        match term {
            EnumTerm::Leaf(var) => {
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
                    .position(|v| *v == *var)
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
            }

            EnumTerm::NodeOrLeaf(node, children) => {
                let node_converted: NodeByte = (node.clone()).try_into().map_err(|e| e.into())?;
                use NodeByte::*;
                match node_converted {
                    True | False | Not | Implies | Biimp | And | Or | NotAnd | ExclusiveOr
                    | NotOr | And3 | Or3 | SumFromAdder | CarryFromAdder | LogicalIf => {
                        let child_values = children
                            .iter()
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

impl<const N: usize> UnsignedBits<u8, N> for u8 {
    fn mask() -> u8 {
        assert!(N <= 3);
        if N == 3 {
            return u8::MAX;
        }
        (1u8 << (1 << N)) - 1
    }
    fn is_mask_maximum(&self) -> bool {
        assert!(N <= 3);
        N == 3
    }

    fn n() -> usize {
        assert!(N <= 3);
        N
    }

    fn from_orig(orig: u8) -> Self {
        assert!(N <= 3);

        if N == 3 {
            return orig;
        }
        let mask = (1u8 << (1 << N)) - 1;
        mask & orig
    }

    fn set_bit(&mut self, bit_pos: u64, value: bool) -> Result<(), MguError> {
        assert!(N <= 3);
        let high_index = 1u64 << N;
        if bit_pos < high_index {
            if value {
                *self |= 1 << (bit_pos as u32);
            } else {
                let bit = 1u8 << (bit_pos as u32);
                let mask = if N == 3 {
                    u8::MAX
                } else {
                    (1u8 << (1 << N)) - 1
                };
                let bit = (bit & mask) ^ mask;
                *self &= bit;
            }
            Ok(())
        } else {
            Err(MguError::UnknownError(121))
        }
    }
}

/// A wrapper around `BigUint` to have it model truth tables on N Boolean variables.
#[cfg(feature = "bigint")]
#[derive(Clone, Debug)]
pub struct SomeBits<const N: usize>(BigUint);

#[cfg(feature = "bigint")]
impl<const N: usize> SomeBits<N> {
    /// A mask with `2^(2^N)` ones.
    pub fn all_ones_mask() -> Self {
        let one: BigUint = 1u32.into();
        Self(one.clone().pow(1 << N) - one)
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
