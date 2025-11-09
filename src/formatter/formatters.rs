//! Concrete formatter implementations.

use super::color::Color;
use super::output_formatter::OutputFormatter;

/// ASCII formatter - Metamath baseline format.
///
/// Uses ASCII operators and Metamath-style variable names:
/// - Operators: `->`, `/\`, `\/`, `-.` etc.
/// - Variables: `ph`, `ps`, `ch` for Booleans; `x`, `y`, `z` for setvars
pub struct AsciiFormatter;

impl OutputFormatter for AsciiFormatter {
    fn name(&self) -> &str {
        "ascii"
    }
}

/// UTF-8 formatter - Unicode symbols without colors.
///
/// Uses Unicode mathematical operators:
/// - Operators: `→`, `∧`, `∨`, `¬` etc.
/// - Variables: `φ`, `ψ`, `χ` for Booleans; `𝑥`, `𝑦`, `𝑧` for setvars
pub struct Utf8Formatter;

impl OutputFormatter for Utf8Formatter {
    fn name(&self) -> &str {
        "utf8"
    }
}

/// UTF-8 formatter with ANSI 256-color codes.
///
/// Like [`Utf8Formatter`] but adds terminal colors:
/// - Boolean variables → Blue
/// - Setvar variables → Green
/// - Class variables → Red
/// - Operators → Orange
pub struct Utf8ColorFormatter;

impl OutputFormatter for Utf8ColorFormatter {
    fn name(&self) -> &str {
        "utf8-color"
    }

    fn get_boolean_color(&self) -> Option<Color> {
        Some(Color::BLUE)
    }

    fn get_setvar_color(&self) -> Option<Color> {
        Some(Color::GREEN)
    }

    fn get_class_color(&self) -> Option<Color> {
        Some(Color::RED)
    }
}

/// HTML formatter - Unicode symbols without colors.
///
/// Uses Unicode mathematical operators wrapped in HTML:
/// - Variables in `<i>` tags
/// - Operators in `<span class='op'>` tags
pub struct HtmlFormatter;

impl OutputFormatter for HtmlFormatter {
    fn name(&self) -> &str {
        "html"
    }
}

/// HTML formatter with inline color styles.
///
/// Like [`HtmlFormatter`] but adds inline color styles:
/// - Boolean variables → Blue (`style="color:#0088ff"`)
/// - Setvar variables → Green (`style="color:#00aa00"`)
/// - Class variables → Red (`style="color:#cc0000"`)
pub struct HtmlColorFormatter;

impl OutputFormatter for HtmlColorFormatter {
    fn name(&self) -> &str {
        "html-color"
    }

    fn get_boolean_color(&self) -> Option<Color> {
        Some(Color::BLUE)
    }

    fn get_setvar_color(&self) -> Option<Color> {
        Some(Color::GREEN)
    }

    fn get_class_color(&self) -> Option<Color> {
        Some(Color::RED)
    }
}

/// LaTeX formatter - LaTeX math mode commands.
///
/// Uses LaTeX commands:
/// - Operators: `\to`, `\land`, `\lor`, `\neg` etc.
/// - Variables: `\varphi`, `\psi`, `\chi` for Booleans; `x`, `y`, `z` for setvars
pub struct LatexFormatter;

impl OutputFormatter for LatexFormatter {
    fn name(&self) -> &str {
        "latex"
    }
}
