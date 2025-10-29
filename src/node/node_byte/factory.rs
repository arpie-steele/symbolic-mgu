//! A simple factory for `NodeByte`.

use crate::{MguError, Node, NodeByte, NodeFactory, Type};
#[cfg(feature = "bigint")]
use num_bigint::BigUint;
#[cfg(feature = "bigint")]
use std::convert::TryInto;
use std::marker::PhantomData;
use std::str::FromStr;

/// TODO.
#[derive(Debug)]
pub struct NodeByteFactory<Ty> {
    /// Literally not used.
    _not_used: PhantomData<Ty>,

    /// Map `u8` to `NodeByte`
    by_order: Vec<NodeByte>,

    /// Map `u8` to `NodeByte`
    by_u8_discriminant: Vec<Option<NodeByte>>,
}

impl<Ty> NodeByteFactory<Ty>
where
    Ty: Type,
{
    /// Create a factory for stateless `NodeByte` objects.
    pub fn new() -> Self {
        let mut by_index = Vec::with_capacity(222);
        let mut by_u8 = vec![None; 256];
        for n in NodeByte::ALL_NODES.iter() {
            by_index.push(*n);
            let index_u8 = (*n) as u8;
            by_u8[index_u8 as usize] = Some(*n);
        }

        Self {
            _not_used: PhantomData,
            by_order: by_index,
            by_u8_discriminant: by_u8,
        }
    }

    /// Lookup a `NodeByte` by its `u8` content, designed for toy examples to
    /// coexist with the use of the remaining `u8` values for ASCII variables.
    ///
    /// # Errors
    /// - The index may not refer to a valid `NodeByte`.
    pub fn lookup_by_discriminant(&self, index: u8) -> Result<NodeByte, MguError> {
        self.by_u8_discriminant[index as usize].ok_or_else(|| {
            MguError::from_unsuported_value_for_type_unsigned(index as u128, "NodeByte")
        })
    }

    /// Loop over all possible `NodeByte` values.
    pub fn all_nodes_iter(&self) -> std::vec::IntoIter<NodeByte> {
        self.by_order.clone().into_iter()
    }
}

impl<Ty> Default for NodeByteFactory<Ty>
where
    Ty: Type,
{
    fn default() -> Self {
        Self::new()
    }
}

impl<Ty> NodeFactory for NodeByteFactory<Ty>
where
    Ty: Type,
{
    type NodeType = <NodeByte as Node>::Type;

    type Node = NodeByte;

    type NodeIterator<'a>
        = std::vec::IntoIter<NodeByte>
    where
        Self: 'a;

    fn create_by_name(&self, name: &str, arity: usize) -> Result<Self::Node, crate::MguError> {
        let node = NodeByte::from_str(name).map_err(|_| MguError::from_error_code::<u16>(4321))?;
        let found_arity = node.get_arity()?;
        if found_arity == arity {
            Ok(node)
        } else {
            Err(MguError::from_found_and_expected_unsigned(
                found_arity,
                arity,
            ))
        }
    }

    fn create_by_boolean_function_code(
        &self,
        code: u128,
        arity: usize,
    ) -> Result<Self::Node, crate::MguError> {
        match arity {
            0 => match (code & 1) as u8 {
                0 => Ok(NodeByte::False),
                1 => Ok(NodeByte::True),
                _ => Err(MguError::from_error_code::<u16>(4322)),
            },
            1 => match (code & 3) as u8 {
                0b01 => Ok(NodeByte::Not),
                _ => Err(MguError::from_error_code::<u16>(4323)),
            },
            2 => match (code & 15) as u8 {
                0b0001 => Ok(NodeByte::NotOr),
                0b0110 => Ok(NodeByte::ExclusiveOr),
                0b0111 => Ok(NodeByte::NotAnd),
                0b1000 => Ok(NodeByte::And),
                0b1001 => Ok(NodeByte::Biimp),
                0b1101 => Ok(NodeByte::Implies),
                0b1110 => Ok(NodeByte::Or),
                _ => Err(MguError::from_error_code::<u16>(4324)),
            },
            3 => match (code & 255) as u8 {
                0b1000_0000 => Ok(NodeByte::And3),
                0b1001_0110 => Ok(NodeByte::SumFromAdder),
                0b1101_1000 => Ok(NodeByte::LogicalIf),
                0b1110_1000 => Ok(NodeByte::CarryFromAdder),
                0b1111_1110 => Ok(NodeByte::Or3),
                _ => Err(MguError::from_error_code::<u16>(4325)),
            },
            _ => Err(MguError::from_error_code::<u16>(4326)),
        }
    }

    #[cfg_attr(nightly, doc(cfg(feature = "bigint")))]
    #[cfg(feature = "bigint")]
    fn create_by_boolean_function_long_code(
        &self,
        code: BigUint,
        arity: usize,
    ) -> Result<Self::Node, MguError> {
        let mask: BigUint = 0xffu32.into();
        if code > mask {
            return Err(MguError::from_error_code::<u16>(4328));
        }
        let value = code.clone() & mask;
        let value: u128 = value
            .try_into()
            .map_err(|_| MguError::from_error_code::<u16>(4329))?;
        self.create_by_boolean_function_code(value, arity)
    }

    fn create_by_type_and_index(
        &self,
        the_type: Self::NodeType,
        index: usize,
    ) -> Result<Self::Node, crate::MguError> {
        let node = self
            .by_order
            .get(index)
            .ok_or_else(|| MguError::from_error_code::<u16>(4330))?;
        if node.to_type() == the_type {
            Ok(*node)
        } else {
            Err(MguError::from_error_code::<u16>(4331))
        }
    }

    fn list_nodes_by_type(&self, the_type: &Self::NodeType) -> Self::NodeIterator<'_> {
        self.all_nodes_iter()
            .filter(|n| n.to_type() == *the_type)
            .collect::<Vec<NodeByte>>()
            .into_iter()
    }
}
