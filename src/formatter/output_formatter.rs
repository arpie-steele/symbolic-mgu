//! Core `OutputFormatter` trait for formatting logical objects.

use super::color::Color;

/// Trait for formatting logical objects to various output representations.
///
/// Formatters delegate to the `format_with()` methods on [`Metavariable`] and [`Node`]
/// implementations, providing a clean separation between formatting logic and
/// the objects being formatted.
///
/// # Design Pattern
///
/// The `OutputFormatter` uses a delegation pattern:
/// 1. Formatter provides its name via `name()`
/// 2. Metavariable/Node/Term implementations check the name and format accordingly
/// 3. Each type knows how to format itself for different formatters
///
/// This enables:
/// - Each type knows how to format itself
/// - Easy extension with new formatters
/// - Fallback to Display trait for unknown formatters
/// - Object-safe trait (can be used as `dyn OutputFormatter`)
///
/// # Object Safety
///
/// This trait is object-safe to allow dynamic formatter dispatch via trait objects.
/// Type-specific formatting is handled by the `format_with()` methods on
/// [`Metavariable`], [`Node`], and [`Term`] implementations.
///
/// # Examples
///
/// ```rust
/// use symbolic_mgu::{OutputFormatter, get_formatter, Metavariable, MetavariableFactory, MetaByte, MetaByteFactory, SimpleType};
///
/// let formatter = get_formatter("utf8");
/// // Formatting is done via Metavariable/Node/Term format_with() methods
/// let vars = MetaByteFactory();
/// let var = vars.list_metavariables_by_type(&SimpleType::Boolean).next().unwrap();
/// let output = var.format_with(&*formatter);
/// println!("{}", output);
/// ```
///
/// [`Metavariable`]: `crate::Metavariable`
/// [`Node`]: `crate::Node`
/// [`Term`]: `crate::Term`
pub trait OutputFormatter: Send + Sync {
    /// Returns the name of this formatter.
    ///
    /// This name is used by [`Metavariable`], [`Node`], and [`Term`] implementations
    /// to determine how to format themselves.
    ///
    /// Standard formatter names:
    /// - `"ascii"` - ASCII operators, Metamath-style names (ph, ps, ch)
    /// - `"utf8"` - Unicode operators and symbols (→, ∧, φ, ψ)
    /// - `"utf8-color"` - UTF-8 with ANSI 256-color codes
    /// - `"html"` - HTML with Unicode symbols
    /// - `"html-color"` - HTML with inline color styles
    /// - `"latex"` - LaTeX math mode (\to, \land, \varphi)
    /// - `"display"` - Fallback using Display trait
    ///
    /// [`Metavariable`]: `crate::Metavariable`
    /// [`Node`]: `crate::Node`
    /// [`Term`]: `crate::Term`
    fn name(&self) -> &str;

    /// Get color code for Boolean type (if this formatter supports colors).
    ///
    /// Returns `None` for color-agnostic formatters (ASCII, LaTeX).
    ///
    /// # Returns
    ///
    /// Color for Boolean metavariables, or None if coloring not supported.
    fn get_boolean_color(&self) -> Option<Color> {
        None
    }

    /// Get color code for Setvar type (if this formatter supports colors).
    ///
    /// Returns `None` for color-agnostic formatters (ASCII, LaTeX).
    ///
    /// # Returns
    ///
    /// Color for Setvar metavariables, or None if coloring not supported.
    fn get_setvar_color(&self) -> Option<Color> {
        None
    }

    /// Get color code for Class type (if this formatter supports colors).
    ///
    /// Returns `None` for color-agnostic formatters (ASCII, LaTeX).
    ///
    /// # Returns
    ///
    /// Color for Class metavariables, or None if coloring not supported.
    fn get_class_color(&self) -> Option<Color> {
        None
    }

    /// Whether this formatter uses infix notation.
    ///
    /// Most formatters use infix notation (e.g., "p ∧ q").
    /// Polish notation formatter would return `false`.
    fn is_infix(&self) -> bool {
        true // Most formatters use infix
    }
}
