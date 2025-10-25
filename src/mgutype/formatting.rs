//! Formatting routines for [`Type`].
//!
//! [`Type`]: `crate::Type`

use super::base::Type;
use std::fmt::{Debug, Display, Formatter, Result};

impl Debug for Type {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result {
        write!(f, "{}", self.as_short_str())
    }
}

impl Display for Type {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result {
        write!(f, "{}", self.as_long_str())
    }
}
