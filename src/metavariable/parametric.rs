//! Generic parametric metavariable implementation.
//!
//! This module provides [`ParametricMetavariable`], a generic metavariable
//! implementation that decouples type systems, decoration schemes, and output formats.
//!
//! # Type Parameters
//!
//! - **`Ty: Type`**: The type system (`SimpleType`, or custom implementations)
//! - **`U: Decorator`**: Controls decoration (subscripts, primes, etc.)
//! - **`CharSet`**: Provides character tables for different output formats
//!
//! # Examples
//!
//! ```
//! use symbolic_mgu::{ParametricMetavariable, WideCharSet, SimpleType, Metavariable};
//!
//! // Create with numeric subscripts (usize decorator)
//! type MyVar = ParametricMetavariable<SimpleType, usize, WideCharSet>;
//!
//! let phi = MyVar::try_from_type_and_index(SimpleType::Boolean, 0).unwrap();
//! assert_eq!(phi.to_string(), "𝜑");
//!
//! let phi_1 = MyVar::try_from_type_and_index(SimpleType::Boolean, 12).unwrap();
//! assert_eq!(phi_1.to_string(), "𝜑₁");
//! ```

use crate::{Decorator, Metavariable, MguError, SimpleType, Type, WideCharSet};
use std::fmt::{Debug, Display};
use std::hash::Hash;
use std::marker::PhantomData;

/// Generic metavariable with pluggable types, decorators, and character sets.
///
/// This type provides maximum flexibility while maintaining zero-cost abstractions
/// through compile-time parameterization.
///
/// # Type Parameters
///
/// - `Ty`: Type system implementation
/// - `U`: Decorator style ((), usize, Prime, etc.)
/// - `CharSet`: Character mapping provider (`WideCharSet`, etc.)
///
/// # Enumeration Order
///
/// Variables enumerate by cycling through base characters first, then incrementing
/// the decorator. For example with 12 Boolean characters:
///
/// - Index 0-11: φ, ψ, χ, θ, τ, η, ζ, σ, ρ, μ, λ, κ (decorator = 0)
/// - Index 12-23: φ₁, ψ₁, χ₁, θ₁, τ₁, η₁, ζ₁, σ₁, ρ₁, μ₁, λ₁, κ₁ (decorator = 1)
/// - Index 24-35: φ₂, ψ₂, χ₂, ... (decorator = 2)
///
/// Formula: `base_index = global_index % (max_base + 1)`,
///          `decorator_count = global_index / (max_base + 1)`
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug, PartialOrd, Ord)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct ParametricMetavariable<Ty, U, CharSet> {
    /// Type of this metavariable (Boolean, Setvar, Class, etc.)
    ty: Ty,
    /// Index within character set for this type (0..`max_index`)
    base_index: usize,
    /// Decoration (subscript, prime, etc.)
    decorator: U,
    /// Zero-sized marker for character set
    _charset: PhantomData<CharSet>,
}

impl<Ty> ParametricMetavariable<Ty, usize, WideCharSet>
where
    Ty: Type + Clone + Debug + Display + Hash + Eq,
{
    /// Format as ASCII (Metamath-compatible).
    ///
    /// # Examples
    ///
    /// ```
    /// use symbolic_mgu::{ParametricMetavariable, WideCharSet, SimpleType, Metavariable};
    ///
    /// type MyVar = ParametricMetavariable<SimpleType, usize, WideCharSet>;
    /// let phi = MyVar::try_from_type_and_index(SimpleType::Boolean, 0).unwrap();
    /// assert_eq!(phi.format_as_ascii(), "ph");
    ///
    /// let phi_1 = MyVar::try_from_type_and_index(SimpleType::Boolean, 12).unwrap();
    /// assert_eq!(phi_1.format_as_ascii(), "ph_1");
    /// ```
    pub fn format_as_ascii(&self) -> String
    where
        Ty: Into<SimpleType>,
    {
        let base = WideCharSet::ascii_char(&self.ty.clone().into(), self.base_index).unwrap_or("?");
        let dec = self.decorator.format_ascii();
        if dec.is_empty() {
            base.to_string()
        } else {
            format!("{}_{}", base, dec)
        }
    }

    /// Format as UTF-8 (Unicode mathematical symbols).
    pub fn format_as_utf8(&self) -> String
    where
        Ty: Into<SimpleType>,
    {
        let base = WideCharSet::utf8_char(&self.ty.clone().into(), self.base_index).unwrap_or("?");
        format!("{}{}", base, self.decorator.format_utf8())
    }

    /// Format as LaTeX.
    pub fn format_as_latex(&self) -> String
    where
        Ty: Into<SimpleType>,
    {
        let base = WideCharSet::latex_char(&self.ty.clone().into(), self.base_index).unwrap_or("?");
        format!("{}{}", base, self.decorator.format_latex())
    }

    /// Format as HTML with optional coloring.
    pub fn format_as_html(&self, formatter: &dyn crate::formatter::OutputFormatter) -> String
    where
        Ty: Into<SimpleType>,
    {
        let base = WideCharSet::utf8_char(&self.ty.clone().into(), self.base_index).unwrap_or("?");

        let color_opt = match self.ty.clone().into() {
            SimpleType::Boolean => formatter.get_boolean_color(),
            SimpleType::Setvar => formatter.get_setvar_color(),
            SimpleType::Class => formatter.get_class_color(),
        };

        let main_html = if let Some(color) = color_opt {
            format!("<i style='color:{}'>{}</i>", color.to_html(), base)
        } else {
            format!("<i>{}</i>", base)
        };

        if self.decorator == 0 {
            main_html
        } else {
            // Use proper HTML <sub> tag with normal digits
            if let Some(color) = color_opt {
                format!(
                    "{}<sub style='color:{}'>{}</sub>",
                    main_html,
                    color.to_html(),
                    self.decorator
                )
            } else {
                format!("{}<sub>{}</sub>", main_html, self.decorator)
            }
        }
    }

    /// Format as UTF-8 with ANSI color codes.
    pub fn format_as_utf8_color(&self, formatter: &dyn crate::formatter::OutputFormatter) -> String
    where
        Ty: Into<SimpleType>,
    {
        let base = WideCharSet::utf8_char(&self.ty.clone().into(), self.base_index).unwrap_or("?");

        let color_opt = match self.ty.clone().into() {
            SimpleType::Boolean => formatter.get_boolean_color(),
            SimpleType::Setvar => formatter.get_setvar_color(),
            SimpleType::Class => formatter.get_class_color(),
        };

        let dec_str = self.decorator.format_utf8();

        if let Some(color) = color_opt {
            format!(
                "\x1b[38;5;{}m{}{}\x1b[0m",
                color.to_xterm256(),
                base,
                dec_str
            )
        } else {
            format!("{}{}", base, dec_str)
        }
    }
}

// Default Display uses UTF-8
impl<Ty> Display for ParametricMetavariable<Ty, usize, WideCharSet>
where
    Ty: Type + Clone + Into<SimpleType>,
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.format_as_utf8())
    }
}

impl<Ty> Metavariable for ParametricMetavariable<Ty, usize, WideCharSet>
where
    Ty: Type + Clone + Debug + Display + Hash + Eq + Into<SimpleType>,
{
    type Type = Ty;

    fn try_from_type_and_index(ty: Ty, index: usize) -> Result<Self, MguError> {
        let max_base = WideCharSet::max_index(&ty.clone().into());
        let base_index = index % (max_base + 1);
        let decorator_count = index / (max_base + 1);

        Ok(ParametricMetavariable {
            ty,
            base_index,
            decorator: decorator_count,
            _charset: PhantomData,
        })
    }

    fn get_type_and_index(&self) -> Result<(Ty, usize), MguError> {
        let max_base = WideCharSet::max_index(&self.ty.clone().into());
        let index = self.base_index + self.decorator * (max_base + 1);
        Ok((self.ty.clone(), index))
    }

    fn max_index_by_type(_typ: Ty) -> usize {
        usize::MAX
    }

    fn format_with(&self, formatter: &dyn crate::formatter::OutputFormatter) -> String {
        match formatter.name() {
            "ascii" => self.format_as_ascii(),
            "latex" => self.format_as_latex(),
            "html" | "html-color" => self.format_as_html(formatter),
            "utf8-color" => self.format_as_utf8_color(formatter),
            _ => self.format_as_utf8(), // Default: UTF-8
        }
    }

    fn to_ascii(&self) -> String {
        self.format_as_ascii()
    }

    fn to_utf8(&self) -> String {
        self.format_as_utf8()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    type TestVar = ParametricMetavariable<SimpleType, usize, WideCharSet>;

    #[test]
    fn parametric_metavariable_basic() {
        let phi = TestVar::try_from_type_and_index(SimpleType::Boolean, 0).unwrap();
        assert_eq!(phi.to_string(), "𝜑");
        assert_eq!(phi.format_as_ascii(), "ph");

        let psi = TestVar::try_from_type_and_index(SimpleType::Boolean, 1).unwrap();
        assert_eq!(psi.to_string(), "𝜓");
        assert_eq!(psi.format_as_ascii(), "ps");
    }

    #[test]
    fn parametric_metavariable_with_subscripts() {
        // Index 12 = first Boolean with subscript 1
        let phi_1 = TestVar::try_from_type_and_index(SimpleType::Boolean, 12).unwrap();
        assert_eq!(phi_1.to_string(), "𝜑₁");
        assert_eq!(phi_1.format_as_ascii(), "ph_1");
        assert_eq!(phi_1.format_as_latex(), r"\varphi_{1}");

        // Index 24 = first Boolean with subscript 2
        let phi_2 = TestVar::try_from_type_and_index(SimpleType::Boolean, 24).unwrap();
        assert_eq!(phi_2.to_string(), "𝜑₂");
        assert_eq!(phi_2.format_as_ascii(), "ph_2");
    }

    #[test]
    fn parametric_metavariable_round_trip() {
        for index in 0..50 {
            let var = TestVar::try_from_type_and_index(SimpleType::Boolean, index).unwrap();
            let (ty, idx) = var.get_type_and_index().unwrap();
            assert_eq!(ty, SimpleType::Boolean);
            assert_eq!(idx, index);
        }
    }

    #[test]
    fn parametric_metavariable_sequence() {
        let vars: Vec<_> = (0..15)
            .map(|i| TestVar::try_from_type_and_index(SimpleType::Boolean, i).unwrap())
            .collect();

        // First 12 should be base characters
        assert_eq!(vars[0].to_string(), "𝜑");
        assert_eq!(vars[1].to_string(), "𝜓");
        assert_eq!(vars[11].to_string(), "𝜅");

        // Next 3 should have subscript 1
        assert_eq!(vars[12].to_string(), "𝜑₁");
        assert_eq!(vars[13].to_string(), "𝜓₁");
        assert_eq!(vars[14].to_string(), "𝜒₁");
    }

    #[test]
    fn parametric_metavariable_setvars() {
        let x = TestVar::try_from_type_and_index(SimpleType::Setvar, 0).unwrap();
        assert_eq!(x.to_string(), "𝑥");
        assert_eq!(x.format_as_ascii(), "x");

        let y = TestVar::try_from_type_and_index(SimpleType::Setvar, 1).unwrap();
        assert_eq!(y.to_string(), "𝑦");
        assert_eq!(y.format_as_ascii(), "y");
    }

    #[test]
    fn parametric_metavariable_classes() {
        let a = TestVar::try_from_type_and_index(SimpleType::Class, 0).unwrap();
        assert_eq!(a.to_string(), "𝐴");
        assert_eq!(a.format_as_ascii(), "A");

        let b = TestVar::try_from_type_and_index(SimpleType::Class, 1).unwrap();
        assert_eq!(b.to_string(), "𝐵");
        assert_eq!(b.format_as_ascii(), "B");
    }

    #[test]
    fn latex_formatting() {
        let phi = TestVar::try_from_type_and_index(SimpleType::Boolean, 0).unwrap();
        assert_eq!(phi.format_as_latex(), r"\varphi");

        let phi_1 = TestVar::try_from_type_and_index(SimpleType::Boolean, 12).unwrap();
        assert_eq!(phi_1.format_as_latex(), r"\varphi_{1}");

        let x = TestVar::try_from_type_and_index(SimpleType::Setvar, 0).unwrap();
        assert_eq!(x.format_as_latex(), "x");

        let x_1 = TestVar::try_from_type_and_index(SimpleType::Setvar, 26).unwrap();
        assert_eq!(x_1.format_as_latex(), "x_{1}");
    }
}
