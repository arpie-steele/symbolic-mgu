//! Wide metavariable implementation with unlimited index space.
//!
//! This module provides [`WideMetavariable`], an implementation of the [`Metavariable`]
//! trait that supports an effectively unlimited number of variables per type using
//! a (Type, usize) tuple.
//!
//! # Display Format
//!
//! [`WideMetavariable`]s use a single italic UTF-8 character (from Unicode Mathematical
//! Alphanumeric Symbols blocks) with an optional numeric subscript:
//!
//! - **Booleans**: Greek letters (φ, ψ, χ, θ, τ, η, ζ, σ, ρ, μ, λ, κ)
//! - **Setvars**: Italic Latin lowercase (𝑥, 𝑦, 𝑧, 𝑤, 𝑣, 𝑢, 𝑡, ...)
//! - **Classes**: Italic Latin uppercase (𝐴, 𝐵, 𝐶, 𝐷, 𝑃, 𝑄, 𝑅, ...)
//!
//! Subscripts use Unicode subscript digits (₀₁₂₃₄₅₆₇₈₉):
//! - Index 0 → φ (first Boolean)
//! - Index 12 → φ₁ (first Boolean, subscript 1)
//! - Index 153 → κ₁₂ (last Boolean κ, subscript 12)
//!
//! # Design Note
//!
//! Following Metamath conventions:
//! - Greek letters for Boolean-valued metavariables
//! - Lowercase Latin for set-valued variables (Setvars)
//! - Uppercase Latin for class-valued variables (Classes)
//!
//! # Examples
//!
//! ```
//! use symbolic_mgu::{WideMetavariable, Metavariable, SimpleType};
//!
//! // Create first Boolean metavariable
//! let phi = WideMetavariable::try_from_type_and_index(SimpleType::Boolean, 0).unwrap();
//! assert_eq!(phi.to_string(), "𝜑");
//!
//! // Create with subscript
//! let phi_1 = WideMetavariable::try_from_type_and_index(SimpleType::Boolean, 12).unwrap();
//! assert_eq!(phi_1.to_string(), "𝜑₁");
//!
//! // Enumerate variables
//! let mut bools = WideMetavariable::enumerate(SimpleType::Boolean);
//! assert_eq!(bools.next().unwrap().to_string(), "𝜑");
//! assert_eq!(bools.next().unwrap().to_string(), "𝜓");
//! ```

use crate::{Metavariable, MguError, SimpleType as Type};
use std::fmt::Display;

/// Lowercase Greek letters used for Boolean metavariables.
///
/// Following Metamath conventions for propositional variables.
/// Total: 12 characters.
pub const OUR_BOOLEANS: &str = "𝜑𝜓𝜒𝜃𝜏𝜂𝜁𝜎𝜌𝜇𝜆𝜅";

/// Italic Latin lowercase letters used for Setvar metavariables.
///
/// Following Metamath conventions for set variables.
/// Total: 24 characters.
pub const OUR_SETVARS: &str = "𝑥𝑦𝑧𝑤𝑣𝑢𝑡𝑓𝑔𝑠𝑒ℎ𝑖𝑗𝑘𝑚𝑛𝑜𝑟𝑞𝑝𝑎𝑏𝑐𝑑𝑙";

/// Italic Latin uppercase letters used for Class metavariables.
///
/// Following Metamath conventions for class variables.
/// Total: 24 characters.
pub const OUR_CLASSES: &str = "𝐴𝐵𝐶𝐷𝑃𝑄𝑅𝑆𝑇𝑈𝐸𝐹𝐺𝐻𝐼𝐽𝐾𝐿𝑀𝑁𝑉𝑊𝑋𝑌𝑍𝑂";

/// A metavariable implementation with unlimited index space.
///
/// [`WideMetavariable`] stores a Type and a usize index, allowing for an
/// effectively unlimited number of variables per type.
///
/// # Display Format
///
/// Variables display as a main character (from the appropriate constant)
/// with an optional subscript when the index exceeds the base character count:
///
/// - Index 0-11 (Booleans): φ, ψ, χ, θ, τ, η, ζ, σ, ρ, μ, λ, κ
/// - Index 12-23 (Booleans): φ₁, ψ₁, χ₁, θ₁, τ₁, η₁, ζ₁, σ₁, ρ₁, μ₁, λ₁, κ₁
/// - Index 24-35 (Booleans): φ₂, ψ₂, χ₂, ...
///
/// Subscripts are computed as `index / character_count`.
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug, PartialOrd, Ord)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct WideMetavariable(pub Type, pub usize);

impl Default for WideMetavariable {
    /// Default is the first Boolean metavariable (φ, index 0).
    fn default() -> Self {
        WideMetavariable(Type::Boolean, 0)
    }
}

impl Metavariable for WideMetavariable {
    type Type = Type;

    fn max_index_by_type(_typ: Type) -> usize {
        usize::MAX
    }

    fn try_from_type_and_index(my_type: Type, my_index: usize) -> Result<Self, MguError> {
        Ok(WideMetavariable(my_type, my_index))
    }

    fn get_type_and_index(&self) -> Result<(Type, usize), MguError> {
        Ok((self.0, self.1))
    }

    fn enumerate(for_type: Type) -> impl Iterator<Item = Self> {
        (0usize..).map(move |x| WideMetavariable(for_type, x))
    }
}

impl Display for WideMetavariable {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        use Type::*;

        let data = match self.0 {
            Boolean => OUR_BOOLEANS,
            Setvar => OUR_SETVARS,
            Class => OUR_CLASSES,
        };

        let n_chars = data.chars().count();
        let subscript = self.1 / n_chars;
        let index = self.1 % n_chars;

        // Get the main character
        let main: String = data.chars().nth(index).iter().collect();

        if subscript != 0 {
            // Convert subscript number to Unicode subscript digits
            let tiny: String = format!("{subscript}")
                .chars()
                .map(|ch| {
                    // Map ASCII digit to Unicode subscript
                    // '0' (0x30) -> '₀' (0x2080)
                    // '1' (0x31) -> '₁' (0x2081)
                    // etc.
                    char::from_u32(0x2080 + (ch as u32 - '0' as u32)).unwrap()
                })
                .collect();
            write!(f, "{main}{tiny}")
        } else {
            write!(f, "{main}")
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::collections::HashSet;

    #[test]
    fn wide_metavariable_display() {
        use Type::*;

        for (t, data, final_girl) in [
            (Boolean, OUR_BOOLEANS, "𝜃₁₅₃₇₂₂₈₆₇₂₈₀₉₁₂₉₃₀₁"),
            (Setvar, OUR_SETVARS, "𝑚₇₀₉₄₉₀₁₅₆₆₈₁₁₃₆₆₀₀"),
            (Class, OUR_CLASSES, "𝐽₇₀₉₄₉₀₁₅₆₆₈₁₁₃₆₆₀₀"),
        ] {
            let short_t = format!("{t:?}");
            let first_char = data.chars().next().unwrap().to_string();
            let last_char = data.chars().next_back().unwrap().to_string();
            let n = data.chars().count();

            assert_eq!(
                format!("{:?}", WideMetavariable(t, 0)),
                format!("WideMetavariable({short_t}, 0)")
            );
            assert_eq!(format!("{}", WideMetavariable(t, 0)), first_char);
            assert_eq!(format!("{}", WideMetavariable(t, n - 1)), last_char);
            assert_eq!(format!("{}", WideMetavariable(t, n)), first_char + "₁");
            assert_eq!(format!("{}", WideMetavariable(t, usize::MAX)), final_girl);
        }
    }

    #[test]
    fn metavariable_wide() {
        assert!(!OUR_BOOLEANS.is_ascii());
        assert!(!OUR_SETVARS.is_ascii());
        assert!(!OUR_CLASSES.is_ascii());

        let n = OUR_BOOLEANS.chars().count();
        for (i, ch) in OUR_BOOLEANS.chars().enumerate() {
            let x = WideMetavariable::try_from_type_and_index(Type::Boolean, i).unwrap();
            assert_eq!(x.to_string(), ch.to_string());
            assert_eq!(x.get_type_and_index(), Ok((Type::Boolean, i)));
            let y = WideMetavariable::try_from_type_and_index(Type::Boolean, i);
            assert_eq!(y, Ok(x));

            let x = WideMetavariable::try_from_type_and_index(Type::Boolean, i + n).unwrap();
            assert_eq!(x.to_string(), ch.to_string() + "₁");
            assert_eq!(x.get_type_and_index(), Ok((Type::Boolean, i + n)));
            let y = WideMetavariable::try_from_type_and_index(Type::Boolean, i + n);
            assert_eq!(y, Ok(x));
        }

        let n = OUR_SETVARS.chars().count();
        for (i, ch) in OUR_SETVARS.chars().enumerate() {
            let x = WideMetavariable::try_from_type_and_index(Type::Setvar, i).unwrap();
            assert_eq!(x.to_string(), ch.to_string());
            assert_eq!(x.get_type_and_index(), Ok((Type::Setvar, i)));
            let y = WideMetavariable::try_from_type_and_index(Type::Setvar, i);
            assert_eq!(y, Ok(x));

            let x = WideMetavariable::try_from_type_and_index(Type::Setvar, i + n).unwrap();
            assert_eq!(x.to_string(), ch.to_string() + "₁");
            assert_eq!(x.get_type_and_index(), Ok((Type::Setvar, i + n)));
            let y = WideMetavariable::try_from_type_and_index(Type::Setvar, i + n);
            assert_eq!(y, Ok(x));
        }

        let n = OUR_CLASSES.chars().count();
        for (i, ch) in OUR_CLASSES.chars().enumerate() {
            let x = WideMetavariable::try_from_type_and_index(Type::Class, i).unwrap();
            assert_eq!(x.to_string(), ch.to_string());
            assert_eq!(x.get_type_and_index(), Ok((Type::Class, i)));
            let y = WideMetavariable::try_from_type_and_index(Type::Class, i);
            assert_eq!(y, Ok(x));

            let x = WideMetavariable::try_from_type_and_index(Type::Class, i + n).unwrap();
            assert_eq!(x.to_string(), ch.to_string() + "₁");
            assert_eq!(x.get_type_and_index(), Ok((Type::Class, i + n)));
            let y = WideMetavariable::try_from_type_and_index(Type::Class, i + n);
            assert_eq!(y, Ok(x));
        }

        let mut uniques = HashSet::new();
        for t in [Type::Boolean, Type::Setvar, Type::Class] {
            for i in WideMetavariable::enumerate(t).take(100) {
                assert_eq!(i.get_type(), Ok(t));
                assert!(uniques.insert(i));
            }
        }
    }

    #[test]
    fn default_is_valid_boolean_metavariable() {
        let default_var = WideMetavariable::default();

        // Default should be a valid metavariable
        let (typ, index) = default_var
            .get_type_and_index()
            .expect("Default WideMetavariable should be valid");

        // Default should be a Boolean metavariable
        assert_eq!(
            typ,
            Type::Boolean,
            "Default WideMetavariable should be Boolean type"
        );

        // Default should be the first Boolean metavariable (index 0)
        assert_eq!(index, 0, "Default WideMetavariable should be at index 0");

        // Verify it displays as the first Boolean character
        let first_bool_char = OUR_BOOLEANS.chars().next().unwrap().to_string();
        assert_eq!(default_var.to_string(), first_bool_char);
    }

    #[test]
    fn enumerate_produces_unique_variables() {
        // Test that enumeration produces unique variables
        let vars: Vec<_> = WideMetavariable::enumerate(Type::Boolean).take(100).collect();
        let unique_vars: HashSet<_> = vars.iter().cloned().collect();

        assert_eq!(vars.len(), unique_vars.len(), "All enumerated variables should be unique");
    }

    #[test]
    fn subscript_formatting() {
        // Test various subscript numbers
        // Note: Uses Mathematical Italic characters from OUR_BOOLEANS constant
        let first_bool = OUR_BOOLEANS.chars().next().unwrap().to_string();
        let test_cases = vec![
            (0, first_bool.clone()),                    // No subscript
            (12, first_bool.clone() + "₁"),            // First subscript
            (24, first_bool.clone() + "₂"),            // Second subscript
            (120, first_bool.clone() + "₁₀"),          // Two-digit subscript
            (1200, first_bool.clone() + "₁₀₀"),        // Three-digit subscript
        ];

        for (index, expected) in test_cases {
            let var = WideMetavariable(Type::Boolean, index);
            assert_eq!(var.to_string(), expected, "Index {} should format as {}", index, expected);
        }
    }
}
