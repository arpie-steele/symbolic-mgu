//! Decorator trait for parametric metavariable subscripts and notation.
//!
//! This module provides the [`Decorator`] trait which controls how decorations
//! (subscripts, primes, etc.) are formatted after the base metavariable character.
//!
//! # Built-in Implementations
//!
//! - `()` - No decoration (φ, ψ, χ, ...)
//! - `usize` - Numeric subscripts (φ, φ₁, φ₂, ...)
//! - [`Prime`] - Prime notation (φ, φ′, φ″, φ‴)

use std::fmt::Debug;
use std::hash::Hash;

/// Trait for decoration styles that can be applied to metavariables.
///
/// Decorators control what appears after the base character in different
/// output formats (ASCII, UTF-8, LaTeX, HTML).
///
/// # Examples
///
/// ```
/// use symbolic_mgu::Decorator;
///
/// // No decoration
/// let none = ();
/// assert_eq!(none.format_utf8(), "");
///
/// // Numeric subscript
/// let sub1 = 1usize;
/// assert_eq!(sub1.format_utf8(), "₁");
///
/// let sub12 = 12usize;
/// assert_eq!(sub12.format_utf8(), "₁₂");
/// ```
pub trait Decorator: Copy + Eq + Hash + Debug + Default {
    /// Format for ASCII output (Metamath-compatible).
    ///
    /// # Examples
    ///
    /// - `()` → `""`
    /// - `1usize` → `"1"`
    /// - `Prime::Single` → `"'"`
    #[must_use]
    fn format_ascii(&self) -> String;

    /// Format for UTF-8 output (Unicode subscripts, primes, etc.).
    ///
    /// # Examples
    ///
    /// - `()` → `""`
    /// - `1usize` → `"₁"`
    /// - `Prime::Single` → `"′"` (U+2032)
    #[must_use]
    fn format_utf8(&self) -> String;

    /// Format for LaTeX output.
    ///
    /// # Examples
    ///
    /// - `()` → `""`
    /// - `1usize` → `"_{1}"`
    /// - `Prime::Single` → `"'"`
    #[must_use]
    fn format_latex(&self) -> String;

    /// Next decorator in sequence (for enumeration).
    ///
    /// Returns `None` when the decorator space is exhausted.
    #[must_use]
    fn next(&self) -> Option<Self>;
}

/// No decoration - base characters only.
///
/// This implementation produces no decoration, allowing only base characters
/// like φ, ψ, χ without subscripts or primes.
///
/// The decorator space is exhausted after the first cycle through base characters,
/// meaning enumeration is limited to the number of base characters available
/// (12 for Boolean, 26 for Setvar/Class).
impl Decorator for () {
    fn format_ascii(&self) -> String {
        String::new()
    }

    fn format_utf8(&self) -> String {
        String::new()
    }

    fn format_latex(&self) -> String {
        String::new()
    }

    fn next(&self) -> Option<Self> {
        None // Exhausted - no decorators beyond the base characters
    }
}

/// Numeric subscript decoration using usize.
///
/// Provides unlimited subscripts: φ, φ₁, φ₂, φ₃, ...
///
/// The zero value produces no subscript (decorator 0 = base character only).
impl Decorator for usize {
    fn format_ascii(&self) -> String {
        if *self == 0 {
            String::new()
        } else {
            format!("{}", self)
        }
    }

    fn format_utf8(&self) -> String {
        if *self == 0 {
            return String::new();
        }

        // Map digits to Unicode subscripts (U+2080..U+2089)
        format!("{}", self)
            .chars()
            .map(|ch| char::from_u32(0x2080 + (ch as u32 - '0' as u32)).unwrap())
            .collect()
    }

    fn format_latex(&self) -> String {
        if *self == 0 {
            String::new()
        } else {
            format!("_{{{}}}", self)
        }
    }

    fn next(&self) -> Option<Self> {
        self.checked_add(1)
    }
}

/// Prime notation decoration (φ, φ′, φ″, φ‴).
///
/// Limited to None, Single, Double, and Triple primes.
/// Often used in mathematical notation as an alternative to subscripts.
#[derive(Copy, Clone, Debug, Default, Eq, PartialEq, Hash)]
pub enum Prime {
    /// No prime (φ)
    #[default]
    None,
    /// Single prime (φ′)
    Single,
    /// Double prime (φ″)
    Double,
    /// Triple prime (φ‴)
    Triple,
}

impl Decorator for Prime {
    fn format_ascii(&self) -> String {
        match self {
            Prime::None => String::new(),
            Prime::Single => "'".to_string(),
            Prime::Double => "''".to_string(),
            Prime::Triple => "'''".to_string(),
        }
    }

    fn format_utf8(&self) -> String {
        match self {
            Prime::None => String::new(),
            Prime::Single => "′".to_string(), // U+2032 PRIME
            Prime::Double => "″".to_string(), // U+2033 DOUBLE PRIME
            Prime::Triple => "‴".to_string(), // U+2034 TRIPLE PRIME
        }
    }

    fn format_latex(&self) -> String {
        // LaTeX uses ASCII apostrophes for primes
        self.format_ascii()
    }

    fn next(&self) -> Option<Self> {
        match self {
            Prime::None => Some(Prime::Single),
            Prime::Single => Some(Prime::Double),
            Prime::Double => Some(Prime::Triple),
            Prime::Triple => None, // Exhausted
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn unit_decorator_produces_empty_strings() {
        let d = ();
        assert_eq!(d.format_ascii(), "");
        assert_eq!(d.format_utf8(), "");
        assert_eq!(d.format_latex(), "");
        assert_eq!(d.next(), None); // Exhausted after first cycle
    }

    #[test]
    fn usize_decorator_zero_is_empty() {
        let d = 0usize;
        assert_eq!(d.format_ascii(), "");
        assert_eq!(d.format_utf8(), "");
        assert_eq!(d.format_latex(), "");
    }

    #[test]
    fn usize_decorator_formats_subscripts() {
        let d = 1usize;
        assert_eq!(d.format_ascii(), "1");
        assert_eq!(d.format_utf8(), "₁");
        assert_eq!(d.format_latex(), "_{1}");

        let d = 12usize;
        assert_eq!(d.format_ascii(), "12");
        assert_eq!(d.format_utf8(), "₁₂");
        assert_eq!(d.format_latex(), "_{12}");

        let d = 153usize;
        assert_eq!(d.format_ascii(), "153");
        assert_eq!(d.format_utf8(), "₁₅₃");
        assert_eq!(d.format_latex(), "_{153}");
    }

    #[test]
    fn usize_decorator_can_increment() {
        let d = 0usize;
        assert_eq!(d.next(), Some(1));

        let d = 1usize;
        assert_eq!(d.next(), Some(2));

        let d = 999usize;
        assert_eq!(d.next(), Some(1000));
    }

    #[test]
    fn prime_decorator_formats_correctly() {
        assert_eq!(Prime::None.format_ascii(), "");
        assert_eq!(Prime::None.format_utf8(), "");
        assert_eq!(Prime::None.format_latex(), "");

        assert_eq!(Prime::Single.format_ascii(), "'");
        assert_eq!(Prime::Single.format_utf8(), "′");
        assert_eq!(Prime::Single.format_latex(), "'");

        assert_eq!(Prime::Double.format_ascii(), "''");
        assert_eq!(Prime::Double.format_utf8(), "″");
        assert_eq!(Prime::Double.format_latex(), "''");

        assert_eq!(Prime::Triple.format_ascii(), "'''");
        assert_eq!(Prime::Triple.format_utf8(), "‴");
        assert_eq!(Prime::Triple.format_latex(), "'''");
    }

    #[test]
    fn prime_decorator_sequence() {
        assert_eq!(Prime::None.next(), Some(Prime::Single));
        assert_eq!(Prime::Single.next(), Some(Prime::Double));
        assert_eq!(Prime::Double.next(), Some(Prime::Triple));
        assert_eq!(Prime::Triple.next(), None); // Exhausted
    }

    #[test]
    fn prime_default_is_none() {
        assert_eq!(Prime::default(), Prime::None);
    }

    #[test]
    fn unit_decorator_is_bounded() {
        // The unit decorator provides NO additional decorations
        // So the space is exhausted immediately (only base characters available)
        let decorator = ();

        // Calling next() on the default (and only) value returns None
        assert_eq!(decorator.next(), None);

        // This means a `ParametricMetavariable`<_, (), _> can only have
        // as many variables as there are base characters (12 Boolean, 26 Setvar/Class)
    }

    #[test]
    fn usize_decorator_is_effectively_unbounded() {
        // The usize decorator provides subscripts 0, 1, 2, 3, ...
        let mut decorator = 0usize;

        // Can advance many times
        for i in 1..=1000 {
            decorator = decorator.next().expect("should not exhaust at 1000");
            assert_eq!(decorator, i);
        }
    }

    #[test]
    fn prime_decorator_is_bounded_at_four() {
        // The Prime decorator provides exactly 4 values
        let mut decorator = Prime::None;

        decorator = decorator.next().unwrap();
        assert_eq!(decorator, Prime::Single);

        decorator = decorator.next().unwrap();
        assert_eq!(decorator, Prime::Double);

        decorator = decorator.next().unwrap();
        assert_eq!(decorator, Prime::Triple);

        // Exhausted after 4 values
        assert_eq!(decorator.next(), None);
    }
}
