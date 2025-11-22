//! Output formatters for logical objects.
//!
//! This module provides a flexible formatting system for terms, nodes, and metavariables.
//! Different formatters support various output formats:
//!
//! - **ASCII**: Metamath-style operators (`->`, `/\`, `ph`, `ps`)
//! - **UTF-8**: Unicode symbols (`→`, `∧`, `φ`, `ψ`)
//! - **UTF-8 Color**: UTF-8 with ANSI 256-color codes
//! - **HTML**: HTML with Unicode symbols
//! - **HTML Color**: HTML with inline color styles
//! - **LaTeX**: LaTeX math mode (`\to`, `\land`, `\varphi`)
//!
//! # Design Pattern
//!
//! The formatter system uses a delegation pattern:
//! 1. Formatters implement the [`OutputFormatter`] trait
//! 2. [`Metavariable`] and [`Node`] implementations have `format_with()` methods
//! 3. Each type knows how to format itself for different formatters
//! 4. Formatters orchestrate recursive formatting for terms
//!
//! # Type-Based Coloring
//!
//! Color-aware formatters use the type-color registry to color metavariables:
//! - Boolean → Blue
//! - Setvar → Green
//! - Class → Red
//! - Custom types can register their own colors
//!
//! # Usage
//!
//! ```rust,compile_fail
//! use symbolic_mgu::{get_formatter, register_type_color, Color};
//!
//! // Get a built-in formatter
//! let formatter = get_formatter("utf8-color");
//! let output = formatter.format_term(&my_term);
//! println!("{}", output);
//!
//! // Register a custom color
//! register_type_color("RealNumber", Color::new(220, "#ffaa00"));
//! ```
//!
//! [`Metavariable`]: crate::Metavariable
//! [`Node`]: crate::Node

pub(crate) mod color;
pub(crate) mod formatters;
pub(crate) mod output_formatter;
pub(crate) mod registry;
#[cfg(test)]
mod tests;
pub(crate) mod type_colors;

// Re-export public API
pub use color::Color;
pub use output_formatter::OutputFormatter;
pub use registry::{get_formatter, register_formatter};
pub use type_colors::{get_type_color, get_type_color_from_trait, register_type_color};
