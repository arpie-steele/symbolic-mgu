//! Introduce an implementation of [`Node`] that can fit in a [`u8`] and not collide with a legal value for [`AsciiMetaVar`].
//!
//! [`Node`]: `crate::Node`
//! [`AsciiMetaVar`]: `crate::AsciiMetaVar`

pub(crate) mod base;
pub(crate) mod factory;
