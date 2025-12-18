//! A simple factory for `NodeByte`.

use crate::{MguError, Node, NodeByte, NodeFactory, Type};
#[cfg(feature = "bigint")]
use num_bigint::BigUint;
#[cfg(feature = "bigint")]
use std::convert::TryInto;
use std::marker::PhantomData;
use std::str::FromStr;

/// Factory for creating `NodeByte` instances.
///
/// This factory leverages strum's derived traits to avoid redundant storage.
#[derive(Debug)]
pub struct NodeByteFactory<Ty> {
    /// Literally not used.
    _not_used: PhantomData<Ty>,
}

impl<Ty> NodeByteFactory<Ty>
where
    Ty: Type,
{
    /// Create a factory for stateless `NodeByte` objects.
    #[must_use]
    pub fn new() -> Self {
        Self {
            _not_used: PhantomData,
        }
    }

    /// Lookup a `NodeByte` by its `u8` content, designed for toy examples to
    /// coexist with the use of the remaining `u8` values for ASCII variables.
    ///
    /// # Errors
    /// - The index may not refer to a valid `NodeByte`.
    pub fn lookup_by_discriminant(&self, index: u8) -> Result<NodeByte, MguError> {
        NodeByte::from_repr(index).ok_or_else(|| {
            MguError::from_unsuported_value_for_type_unsigned(index as u128, "NodeByte")
        })
    }

    /// Loop over all possible `NodeByte` values.
    #[must_use]
    pub fn all_nodes_iter(&self) -> std::vec::IntoIter<NodeByte> {
        // We use `to_vec().into_iter()` to agree with our declared `Self::NodeIterator`
        #[allow(clippy::unnecessary_to_owned)]
        NodeByte::ALL_NODES.to_vec().into_iter()
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

    fn create_by_name(&self, name: &str, arity: usize) -> Result<Self::Node, MguError> {
        let node = NodeByte::from_str(name).map_err(|_| MguError::UnknownNodeName {
            name: name.to_string(),
        })?;
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
    ) -> Result<Self::Node, MguError> {
        match arity {
            0 => match (code & 1) as u8 {
                0 => Ok(NodeByte::False),
                1 => Ok(NodeByte::True),
                _ => Err(MguError::InvalidBooleanCode { code, arity: 0 }),
            },
            1 => match (code & 3) as u8 {
                0b01 => Ok(NodeByte::Not),
                _ => Err(MguError::InvalidBooleanCode { code, arity: 1 }),
            },
            2 => match (code & 15) as u8 {
                0b0001 => Ok(NodeByte::NotOr),
                0b0110 => Ok(NodeByte::ExclusiveOr),
                0b0111 => Ok(NodeByte::NotAnd),
                0b1000 => Ok(NodeByte::And),
                0b1001 => Ok(NodeByte::Biimp),
                0b1101 => Ok(NodeByte::Implies),
                0b1110 => Ok(NodeByte::Or),
                _ => Err(MguError::InvalidBooleanCode { code, arity: 2 }),
            },
            3 => match (code & 255) as u8 {
                0b1000_0000 => Ok(NodeByte::And3),
                0b1001_0110 => Ok(NodeByte::SumFromAdder),
                0b1101_1000 => Ok(NodeByte::LogicalIf),
                0b1110_1000 => Ok(NodeByte::CarryFromAdder),
                0b1111_1110 => Ok(NodeByte::Or3),
                _ => Err(MguError::InvalidBooleanCode { code, arity: 3 }),
            },
            _ => Err(MguError::UnsupportedBooleanArity { arity }),
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
            return Err(MguError::FeatureRequired {
                feature: "bigint",
                reason: format!(
                    "Boolean codes > 0xFF require bigint feature (got {:#x})",
                    code
                ),
            });
        }
        let value = code.clone() & mask;
        let value_clone = value.clone();
        let value: u128 = value.try_into().map_err(|_| {
            MguError::NumericConversionError(format!(
                "Failed to convert BigUint to u128: {:?}",
                value_clone
            ))
        })?;
        self.create_by_boolean_function_code(value, arity)
    }

    fn create_by_type_and_index(
        &self,
        the_type: Self::NodeType,
        index: usize,
    ) -> Result<Self::Node, MguError> {
        let node = NodeByte::ALL_NODES
            .get(index)
            .ok_or_else(|| MguError::ChildIndexOutOfRange(index, NodeByte::ALL_NODES.len()))?;
        if node.to_type() == the_type {
            Ok(*node)
        } else {
            Err(MguError::NodeTypeMismatch {
                found: format!("{:?}", node.to_type()),
                expected: format!("{:?}", the_type),
            })
        }
    }

    fn list_nodes_by_type(&self, the_type: &Self::NodeType) -> Self::NodeIterator<'_> {
        self.all_nodes_iter()
            .filter(|n| n.to_type() == *the_type)
            .collect::<Vec<NodeByte>>()
            .into_iter()
    }
}
