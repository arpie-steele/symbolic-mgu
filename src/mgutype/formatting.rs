//! Formatting routines for [`Type`].
//!
//! [`Type`]: `crate::Type`

use crate::SimpleType;
use std::fmt::{Debug, Display, Formatter, Result};

impl Debug for SimpleType {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result {
        write!(f, "{}", self.as_short_str())
    }
}

impl Display for SimpleType {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result {
        write!(f, "{}", self.as_long_str())
    }
}
