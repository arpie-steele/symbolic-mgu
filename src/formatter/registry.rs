//! Global formatter registry for managing `OutputFormatter` implementations.

use super::output_formatter::OutputFormatter;
use std::collections::HashMap;
use std::sync::{Arc, OnceLock, RwLock};

/// Type alias for boxed formatter trait objects.
type FormatterBox = Arc<dyn OutputFormatter>;

/// Global formatter registry.
///
/// Initialized with built-in formatters on first access.
/// Applications can register custom formatters at run-time.
static GLOBAL_FORMATTER_REGISTRY: OnceLock<RwLock<HashMap<String, FormatterBox>>> = OnceLock::new();

/// Get or initialize the global formatter registry.
///
/// Initializes the registry with built-in formatters on first access:
/// - `"ascii"` - ASCII operators, Metamath-style names
/// - `"utf8"` - Unicode operators and symbols
/// - `"utf8-color"` - UTF-8 with ANSI 256-color codes
/// - `"html"` - HTML with Unicode symbols
/// - `"html-color"` - HTML with inline color styles
/// - `"latex"` - LaTeX math mode
/// - `"display"` - Fallback using Display trait
fn formatter_registry() -> &'static RwLock<HashMap<String, FormatterBox>> {
    GLOBAL_FORMATTER_REGISTRY.get_or_init(|| {
        use super::formatters::*;

        let mut map = HashMap::new();

        // Register built-in formatters
        map.insert(
            "ascii".to_string(),
            Arc::new(AsciiFormatter) as FormatterBox,
        );
        map.insert("utf8".to_string(), Arc::new(Utf8Formatter) as FormatterBox);
        map.insert(
            "utf8-color".to_string(),
            Arc::new(Utf8ColorFormatter) as FormatterBox,
        );
        map.insert("html".to_string(), Arc::new(HtmlFormatter) as FormatterBox);
        map.insert(
            "html-color".to_string(),
            Arc::new(HtmlColorFormatter) as FormatterBox,
        );
        map.insert(
            "latex".to_string(),
            Arc::new(LatexFormatter) as FormatterBox,
        );
        map.insert(
            "display".to_string(),
            Arc::new(DisplayFormatter) as FormatterBox,
        );

        RwLock::new(map)
    })
}

/// Register a custom formatter.
///
/// # Arguments
///
/// * `name` - Name to register the formatter under
/// * `formatter` - Formatter implementation
///
/// # Examples
///
/// ```rust,ignore
/// use symbolic_mgu::{register_formatter, OutputFormatter};
///
/// struct MyFormatter;
/// impl OutputFormatter for MyFormatter {
///     fn name(&self) -> &str { "my-format" }
///     // ... implement other methods ...
/// }
///
/// register_formatter("my-format", MyFormatter);
/// ```
///
/// # Panics
///
/// Can panic
/// - if `RwLock` is poisoned because a writer panics while holding an exclusive lock, or
/// - if the lock is already held by the current thread.
pub fn register_formatter(name: impl Into<String>, formatter: impl OutputFormatter + 'static) {
    formatter_registry()
        .write()
        .unwrap()
        .insert(name.into(), Arc::new(formatter));
}

/// Get a formatter by name.
///
/// Returns a fallback formatter if the requested name is not found.
///
/// # Arguments
///
/// * `name` - Name of the formatter to retrieve
///
/// # Examples
///
/// ```rust,ignore
/// use symbolic_mgu::get_formatter;
///
/// let formatter = get_formatter("utf8-color");
/// let output = formatter.format_term(&my_term);
/// ```
///
/// # Panics
///
/// Can panic
/// - if `RwLock` is poisoned because a writer panics while holding an exclusive lock, or
/// - if the lock is already held by the current thread.
pub fn get_formatter(name: &str) -> FormatterBox {
    formatter_registry()
        .read()
        .unwrap()
        .get(name)
        .cloned()
        .unwrap_or_else(|| {
            // Fallback to display formatter
            // Will be replaced with actual `DisplayFormatter` implementation
            Arc::new(DisplayFormatter)
        })
}

/// Fallback formatter that uses Display trait.
///
/// This is used when a requested formatter is not found.
struct DisplayFormatter;

impl OutputFormatter for DisplayFormatter {
    fn name(&self) -> &str {
        "display"
    }
}
