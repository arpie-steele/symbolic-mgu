//! Next-gen Boolean evaluation.

use crate::{EnumTerm, Metavariable, MguError, NodeBytes, SimpleType};
use std::fmt::Debug as DebugTrait;
use std::ops::{BitAnd, BitOr, BitXor, Not};

#[cfg(feature = "bigint")]
use num_bigint::BigUint;

/// Checks if a Boolean `NodeBytes` node is supported by this module.
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
/// [`True`]: `crate::NodeBytes::True`
/// [`False`]: `crate::NodeBytes::False`
/// [`Not`]: `crate::NodeBytes::Not`
/// [`Implies`]: `crate::NodeBytes::Implies`
/// [`Biimp`]: `crate::NodeBytes::Biimp`
/// [`And`]: `crate::NodeBytes::And`
/// [`Or`]: `crate::NodeBytes::Or`
/// [`NotAnd`]: `crate::NodeBytes::NotAnd`
/// [`ExclusiveOr`]: `crate::NodeBytes::ExclusiveOr`
/// [`NotOr`]: `crate::NodeBytes::NotOr`
/// [`And3`]: `crate::NodeBytes::And3`
/// [`Or3`]: `crate::NodeBytes::Or3`
/// [`SumFromAdder`]: `crate::NodeBytes::SumFromAdder`
/// [`CarryFromAdder`]: `crate::NodeBytes::CarryFromAdder`
/// [`LogicalIf`]: `crate::NodeBytes::LogicalIf`
pub fn is_supported_op(node: &NodeBytes) -> bool {
    use NodeBytes::*;
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
            | SumFromAdder
            | CarryFromAdder
            | LogicalIf
    )
}

/// Isolate the differences between various unsigned representations.
pub trait UnsignedBits<T, const N: usize>:
    Clone
    + DebugTrait
    + BitXor<Output = Self>
    + BitAnd<Output = Self>
    + BitOr<Output = Self>
    + Not<Output = Self>
where
    T: Clone + BitAnd<Output = T> + BitOr<Output = T> + BitXor<Output = T>,
{
    /// Mask for one's complement.
    fn mask() -> T;

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
    fn from_orig(orig: T) -> Self;

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
    fn eval_boolean_nullary(node: &NodeBytes) -> Result<Self, MguError> {
        use NodeBytes::*;
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
    fn eval_boolean_unary<V>(&node: &NodeBytes, a: &Self) -> Result<Self, MguError>
    where
        V: Metavariable,
    {
        use NodeBytes::*;
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
    fn eval_boolean_binary<V>(node: &NodeBytes, a: &Self, b: &Self) -> Result<Self, MguError>
    where
        V: Metavariable,
    {
        use NodeBytes::*;
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
        node: &NodeBytes,
        a: &Self,
        b: &Self,
        c: &Self,
    ) -> Result<Self, MguError>
    where
        V: Metavariable,
    {
        use NodeBytes::*;
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
    fn eval_boolean_node<V>(node: &NodeBytes, children: &[Self]) -> Result<Self, MguError>
    where
        V: Metavariable,
    {
        use NodeBytes::*;
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
    fn eval_boolean_term<V>(term: &EnumTerm<V, NodeBytes>, vars: &[V]) -> Result<Self, MguError>
    where
        V: Metavariable,
    {
        match term {
            EnumTerm::MetaLeaf(var) => {
                let typ = var.get_type()?;
                if typ != SimpleType::Boolean {
                    return Err(MguError::TypeMismatch(typ, SimpleType::Boolean));
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

                // Create alternating pattern: period = 2^(`var_index`+1), on for `2^var_index` bits
                // Pattern repeats with period 2^(`var_index`+1), and is high for the second half of each period

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

            EnumTerm::NodeHead(node, children) => {
                use NodeBytes::*;
                match node {
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
                        Self::eval_boolean_node::<V>(node, &child_values)
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
#[derive(Clone, Debug)]
pub struct SomeBits<const N: usize>(BigUint);

impl<const N: usize> SomeBits<N> {
    /// A mask with 2^(`2^N`) ones.
    pub fn all_ones_mask() -> Self {
        let one: BigUint = 1u32.into();
        Self(one.clone().pow(1 << N) - one)
    }
}

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

impl<const N: usize> BitAnd for SomeBits<N> {
    type Output = SomeBits<N>;

    fn bitand(self, rhs: Self) -> Self::Output {
        (SomeBits::<N>)(self.0 & rhs.0)
    }
}

impl<const N: usize> Not for SomeBits<N> {
    type Output = SomeBits<N>;

    fn not(self) -> Self::Output {
        (SomeBits::<N>)(self.0 ^ SomeBits::<N>::all_ones_mask().0)
    }
}

impl<const N: usize> BitOr for SomeBits<N> {
    type Output = SomeBits<N>;

    fn bitor(self, rhs: Self) -> Self::Output {
        (SomeBits::<N>)(self.0 | rhs.0)
    }
}

impl<const N: usize> BitXor for SomeBits<N> {
    type Output = SomeBits<N>;

    fn bitxor(self, rhs: Self) -> Self::Output {
        (SomeBits::<N>)(self.0 ^ rhs.0)
    }
}
