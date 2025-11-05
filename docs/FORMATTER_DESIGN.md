# Output Formatter Design Document

## Design Goals

1. **Familiar Rust syntax**: `"{0:latex}"`, `"{term:html}"` format specifiers
2. **Type-based coloring**: Metavariables colored by their Type (Boolean/Setvar/Class)
3. **Extensible type-color registry**: Support new types without code changes
4. **Color-agnostic formatters**: ASCII/LaTeX formatters ignore colors
5. **Application-controlled statement layout**: Library doesn't dictate 2D layouts
6. **Avoid color theory complexity**: Simple, pragmatic color handling
7. **Node/Metavariable support**: Built-in formatter methods with ASCII/UTF-8 fallbacks

## Architecture Overview

### Three-Layer System

```
User Code:
    format!("{:utf8-color}", term)
        ↓
std::fmt::Display wrapper:
    FormattedTerm<T> { term: T, format_name: &str }
        ↓
Formatter trait:
    OutputFormatter::format_term(term) → String
        ↓
Type-Color registry (if needed):
    TYPE_COLOR_REGISTRY.get(Type::Boolean) → Color(33)
```

### Core Components

#### 1. Formatter Trait (src/formatter/mod.rs)

```rust
/// Trait for formatting logical objects to various output representations.
pub trait OutputFormatter: Send + Sync {
    /// Returns the name of this formatter
    fn name(&self) -> &str;

    /// Format a metavariable using its built-in formatter support
    fn format_metavar<Ty, V>(&self, var: &V) -> String
    where
        Ty: Type,
        V: Metavariable<Type = Ty>,
    {
        // Delegate to metavariable's format_with method
        var.format_with(self)
    }

    /// Format a node using its built-in formatter support
    fn format_node<Ty, N>(&self, node: &N) -> String
    where
        Ty: Type,
        N: Node<Type = Ty>,
    {
        // Delegate to node's format_with method
        node.format_with(self)
    }

    /// Format a term (recursively)
    fn format_term<Ty, V, N, T>(&self, term: &T) -> String
    where
        Ty: Type,
        V: Metavariable<Type = Ty>,
        N: Node<Type = Ty>,
        T: Term<Ty, V, N>;

    /// Get color for a type (if this formatter supports colors)
    /// Returns None for color-agnostic formatters
    fn get_type_color(&self, ty: &impl Type) -> Option<Color> {
        None  // Default: no coloring
    }

    /// Whether this formatter uses infix notation
    fn is_infix(&self) -> bool {
        true  // Most formatters use infix
    }
}
```

#### 2. Enhanced Metavariable Trait

```rust
pub trait Metavariable: Clone + Eq + Hash + Debug {
    type Type: Type;

    // ... existing methods ...

    /// Format this metavariable with the given formatter.
    /// Default: uses Display trait
    fn format_with(&self, formatter: &dyn OutputFormatter) -> String {
        format!("{}", self)
    }

    /// Get ASCII representation (e.g., "ph" for φ)
    fn to_ascii(&self) -> String {
        format!("{}", self)  // Default: use Display
    }

    /// Get UTF-8 representation (e.g., "φ" for Boolean metavar 0)
    fn to_utf8(&self) -> String {
        format!("{}", self)  // Default: use Display
    }
}
```

**WideMetavariable Implementation Pattern**:
```rust
impl Metavariable for WideMetavariable {
    fn format_with(&self, formatter: &dyn OutputFormatter) -> String {
        let (main_char, subscript_opt) = self.get_display_parts();

        match formatter.name() {
            "ascii" => self.to_ascii(),  // "ph", "ph_1", etc.
            "latex" => {
                let latex_symbol = map_unicode_to_latex(main_char);  // φ→\varphi
                if let Some(sub) = subscript_opt {
                    format!("{latex_symbol}_{{{sub}}}")
                } else {
                    latex_symbol
                }
            }
            "html" | "html-color" => {
                let colored = if let Some(color) = formatter.get_type_color(&self.0) {
                    format!("<i style='color:{}'>{main_char}</i>", color.to_html())
                } else {
                    format!("<i>{main_char}</i>")
                };

                if let Some(sub) = subscript_opt {
                    format!("{colored}<sub>{sub}</sub>")
                } else {
                    colored
                }
            }
            "utf8-color" => {
                let colored = if let Some(color) = formatter.get_type_color(&self.0) {
                    format!("\x1b[38;5;{}m{}\x1b[0m", color.to_xterm256(), main_char)
                } else {
                    main_char.to_string()
                };

                if let Some(sub) = subscript_opt {
                    // Subscript already in UTF-8 from WideMetavariable Display
                    format!("{colored}{}", format_subscript_digits(sub))
                } else {
                    colored
                }
            }
            _ => format!("{}", self),  // Fallback to Display
        }
    }

    /// Helper: breaks down into main char + optional subscript number
    fn get_display_parts(&self) -> (char, Option<usize>) {
        let data = match self.0 {
            Type::Boolean => OUR_BOOLEANS,
            Type::Setvar => OUR_SETVARS,
            Type::Class => OUR_CLASSES,
        };
        let n_chars = data.chars().count();
        let subscript_num = self.1 / n_chars;
        let index = self.1 % n_chars;
        let main_char = data.chars().nth(index).unwrap();

        if subscript_num == 0 {
            (main_char, None)
        } else {
            (main_char, Some(subscript_num))
        }
    }
}
```

#### 3. Enhanced Node Trait

```rust
pub trait Node: Clone + PartialEq + Eq + Debug {
    type Type: Type;

    // ... existing methods ...

    /// Format this node with the given formatter
    fn format_with(&self, formatter: &dyn OutputFormatter) -> String {
        format!("{}", self)  // Default: use Display
    }

    /// Get ASCII operator symbol
    fn to_ascii_symbol(&self) -> &str;

    /// Get UTF-8 operator symbol
    fn to_utf8_symbol(&self) -> &str;
}
```

**NodeByte Implementation Pattern**:
```rust
impl Node for NodeByte {
    fn format_with(&self, formatter: &dyn OutputFormatter) -> String {
        match formatter.name() {
            "ascii" => self.to_ascii_symbol().to_string(),
            "latex" => self.to_latex_symbol().to_string(),
            "html" | "html-color" => {
                let sym = self.to_utf8_symbol();
                format!("<span class='op'>{sym}</span>")
            }
            "utf8-color" => {
                let sym = self.to_utf8_symbol();
                // Operators get fixed color (e.g., orange)
                format!("\x1b[38;5;208m{}\x1b[0m", sym)
            }
            _ => self.to_utf8_symbol().to_string(),
        }
    }

    fn to_ascii_symbol(&self) -> &str {
        match self {
            NodeByte::Implies => "->",
            NodeByte::Not => "-",
            NodeByte::And => "/\\",
            NodeByte::Or => "\\/",
            NodeByte::Biimplication => "<->",
            NodeByte::Xor => "(+)",
            _ => "?",
        }
    }

    fn to_utf8_symbol(&self) -> &str {
        match self {
            NodeByte::Implies => "→",
            NodeByte::Not => "¬",
            NodeByte::And => "∧",
            NodeByte::Or => "∨",
            NodeByte::Biimplication => "↔",
            NodeByte::Xor => "⊕",
            _ => "?",
        }
    }

    fn to_latex_symbol(&self) -> &str {
        match self {
            NodeByte::Implies => r"\to",
            NodeByte::Not => r"\neg",
            NodeByte::And => r"\land",
            NodeByte::Or => r"\lor",
            NodeByte::Biimplication => r"\leftrightarrow",
            NodeByte::Xor => r"\oplus",
            _ => "?",
        }
    }
}
```

#### 4. Type-Color Registry (src/formatter/type_colors.rs)

```rust
use std::collections::HashMap;
use std::sync::{OnceLock, RwLock};

/// Simple color representation
#[derive(Clone, Copy, Debug)]
pub struct Color {
    /// xterm256 color code (0-255)
    xterm256: u8,
    /// HTML hex color
    html_hex: &'static str,
}

impl Color {
    pub fn to_xterm256(&self) -> u8 {
        self.xterm256
    }

    pub fn to_html(&self) -> &str {
        self.html_hex
    }
}

/// Global registry mapping Type to Color
static TYPE_COLOR_REGISTRY: OnceLock<RwLock<HashMap<String, Color>>> = OnceLock::new();

/// Get or initialize the type-color registry
fn type_color_registry() -> &'static RwLock<HashMap<String, Color>> {
    TYPE_COLOR_REGISTRY.get_or_init(|| {
        let mut map = HashMap::new();

        // Default colors for standard types
        map.insert("Boolean".to_string(), Color {
            xterm256: 33,  // Blue
            html_hex: "#0088ff",
        });
        map.insert("Setvar".to_string(), Color {
            xterm256: 34,  // Green
            html_hex: "#00aa00",
        });
        map.insert("Class".to_string(), Color {
            xterm256: 160,  // Red
            html_hex: "#cc0000",
        });

        RwLock::new(map)
    })
}

/// Register a color for a type
pub fn register_type_color(type_name: impl Into<String>, color: Color) {
    type_color_registry()
        .write()
        .unwrap()
        .insert(type_name.into(), color);
}

/// Get color for a type (returns None if not registered)
pub fn get_type_color(type_name: &str) -> Option<Color> {
    type_color_registry()
        .read()
        .unwrap()
        .get(type_name)
        .copied()
}
```

#### 5. Formatter Implementations

**AsciiFormatter** (Metamath baseline):
```rust
pub struct AsciiFormatter;

impl OutputFormatter for AsciiFormatter {
    fn name(&self) -> &str { "ascii" }

    fn format_term<Ty, V, N, T>(&self, term: &T) -> String {
        // Infix with ASCII operators
        // ( ph -> ( ps -> ph ) )
    }

    // No coloring
    fn get_type_color(&self, _ty: &impl Type) -> Option<Color> {
        None
    }
}
```

**Utf8Formatter** (plain Unicode):
```rust
pub struct Utf8Formatter;

impl OutputFormatter for Utf8Formatter {
    fn name(&self) -> &str { "utf8" }

    fn format_term<Ty, V, N, T>(&self, term: &T) -> String {
        // Infix with Unicode operators
        // (φ → (ψ → φ))
    }
}
```

**Utf8ColorFormatter** (ANSI 256-color):
```rust
pub struct Utf8ColorFormatter;

impl OutputFormatter for Utf8ColorFormatter {
    fn name(&self) -> &str { "utf8-color" }

    fn get_type_color(&self, ty: &impl Type) -> Option<Color> {
        get_type_color(&format!("{:?}", ty))
    }
}
```

**HtmlColorFormatter**:
```rust
pub struct HtmlColorFormatter;

impl OutputFormatter for HtmlColorFormatter {
    fn name(&self) -> &str { "html-color" }

    fn get_type_color(&self, ty: &impl Type) -> Option<Color> {
        get_type_color(&format!("{:?}", ty))
    }

    fn format_term<Ty, V, N, T>(&self, term: &T) -> String {
        // Use inline styles: <i style="color:#0088ff">φ</i>
    }
}
```

**LatexFormatter**:
```rust
pub struct LatexFormatter;

impl OutputFormatter for LatexFormatter {
    fn name(&self) -> &str { "latex" }

    // No coloring (LaTeX uses semantic markup)
    fn get_type_color(&self, _ty: &impl Type) -> Option<Color> {
        None
    }
}
```

#### 6. Global Formatter Registry (src/formatter/registry.rs)

```rust
use std::collections::HashMap;
use std::sync::{Arc, OnceLock, RwLock};

type FormatterBox = Arc<dyn OutputFormatter>;

/// Global formatter registry
static GLOBAL_FORMATTER_REGISTRY: OnceLock<RwLock<HashMap<String, FormatterBox>>> = OnceLock::new();

/// Get or initialize the global formatter registry
fn formatter_registry() -> &'static RwLock<HashMap<String, FormatterBox>> {
    GLOBAL_FORMATTER_REGISTRY.get_or_init(|| {
        let mut map = HashMap::new();

        // Register built-in formatters
        map.insert("ascii".to_string(), Arc::new(AsciiFormatter));
        map.insert("utf8".to_string(), Arc::new(Utf8Formatter));
        map.insert("utf8-color".to_string(), Arc::new(Utf8ColorFormatter));
        map.insert("html".to_string(), Arc::new(HtmlFormatter));
        map.insert("html-color".to_string(), Arc::new(HtmlColorFormatter));
        map.insert("latex".to_string(), Arc::new(LatexFormatter));
        map.insert("display".to_string(), Arc::new(DisplayFormatter));

        RwLock::new(map)
    })
}

pub fn register_formatter(name: impl Into<String>, formatter: impl OutputFormatter + 'static) {
    formatter_registry()
        .write()
        .unwrap()
        .insert(name.into(), Arc::new(formatter));
}

pub fn get_formatter(name: &str) -> FormatterBox {
    formatter_registry()
        .read()
        .unwrap()
        .get(name)
        .cloned()
        .unwrap_or_else(|| Arc::new(DisplayFormatter))
}
```

#### 7. std::fmt Integration (src/formatter/display_wrapper.rs)

```rust
/// Wrapper type to enable "{:formatter_name}" syntax
pub struct Formatted<'a, T> {
    value: &'a T,
    formatter_name: &'a str,
}

impl<'a, Ty, V, N, T> std::fmt::Display for Formatted<'a, T>
where
    Ty: Type,
    V: Metavariable<Type = Ty>,
    N: Node<Type = Ty>,
    T: Term<Ty, V, N>,
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let formatter = get_formatter(self.formatter_name);
        write!(f, "{}", formatter.format_term(self.value))
    }
}

/// Extension trait to enable .formatted("name") method
pub trait Formattable: Sized {
    fn formatted<'a>(&'a self, formatter_name: &'a str) -> Formatted<'a, Self> {
        Formatted {
            value: self,
            formatter_name,
        }
    }
}

// Implement for all Terms
impl<Ty, V, N, T> Formattable for T
where
    Ty: Type,
    V: Metavariable<Type = Ty>,
    N: Node<Type = Ty>,
    T: Term<Ty, V, N>,
{}
```

**Usage**:
```rust
// Method 1: .formatted() method
println!("{}", term.formatted("utf8-color"));

// Method 2: Custom format specifier (requires proc macro)
println!("{:utf8-color}", term);  // Future work

// Method 3: format_math! macro
format_math!("utf8-color", "{}", term);
```

## Statement Formatting (Out of Scope)

Statement layout is **intentionally left to application developers** because:
- Different textbook conventions exist
- Some layouts are inherently 2-dimensional (proof trees, sequent calculus)
- No single format satisfies all use cases

**Application developers** can use the formatter API:
```rust
let formatter = get_formatter("utf8-color");
let assertion = formatter.format_term(stmt.get_assertion());
let hyps: Vec<_> = stmt.get_hypotheses()
    .iter()
    .map(|h| formatter.format_term(h))
    .collect();

// Custom layout logic here
println!("⊢ {}", assertion);  // Sequent style
// or
println!("({assertion}; {:?}; ∅)", hyps);  // Tuple style
```

## Design Decisions

### 1. Type-Based Coloring Only

**Only metavariables are colored**, based on their Type:
- Boolean → Blue (#0088ff / xterm256:33)
- Setvar → Green (#00aa00 / xterm256:34)
- Class → Red (#cc0000 / xterm256:160)

**Operators use fixed colors** (if colored):
- All operators → Orange (xterm256:208)

**Rationale**: Helps distinguish variable types at a glance, avoids color theory complexity.

### 2. No Color Module

Avoid building elaborate color manipulation code. Simple palette:
- Store xterm256 code + HTML hex
- No RGB→XYZ→Lab conversions
- No dynamic palette generation

### 3. HTML Inline Styles

Use `style="color:#0088ff"` instead of CSS classes:
- No document context assumptions
- Self-contained output
- Copy-paste friendly

### 4. Formatter Name as Discriminator

Metavariables/Nodes use `formatter.name()` to dispatch:
- Clean separation of concerns
- Easy to extend
- Fallback to Display trait

### 5. Delegation Pattern

Formatters delegate to `Metavariable::format_with()` and `Node::format_with()`:
- Each type knows how to format itself
- Formatters orchestrate, don't micromanage
- Extensible for new Node/Metavariable implementations

## Implementation Plan

### Phase 1: Core Infrastructure
1. Define `OutputFormatter` trait
2. Implement `Color` and type-color registry
3. Implement global formatter registry
4. Add `Formatted<T>` wrapper for std::fmt integration

### Phase 2: Enhance Existing Types
5. Add `format_with()`, `to_ascii()`, `to_utf8()` to Metavariable trait
6. Add `format_with()`, symbol methods to Node trait
7. Implement for MetaByte (ASCII names: ph, ps, ch...)
8. Implement for NodeByte (operators)

### Phase 3: Formatters
9. Implement AsciiFormatter
10. Implement Utf8Formatter
11. Implement Utf8ColorFormatter
12. Implement HtmlColorFormatter
13. Implement LatexFormatter

### Phase 4: Integration
14. Update compact binary with `--format` flag
15. Add formatter examples to documentation
16. Export formatter API from lib.rs

### Phase 5: WideMetavariable (concurrent)
17. Backport WideMetavariable from rustmgu
18. Implement WideMetavariableFactory
19. Implement `format_with()` for WideMetavariable
20. Add tests for long proofs requiring >256 variables

## Technical Notes

### Global Registry Implementation: `OnceLock` vs `lazy_static`

**Decision**: Use `std::sync::OnceLock` (Rust 1.70+) instead of `lazy_static` crate.

**Rationale**:
- ✅ **Zero dependencies**: OnceLock is in the standard library (Rust 1.70+)
- ✅ **MSRV compatible**: Works with our minimum Rust version (1.77)
- ✅ **Future-proof**: Won't be deprecated like external crates
- ✅ **Same performance**: Identical to lazy_static under the hood
- ✅ **Project philosophy**: Avoid external dependencies when stdlib provides equivalent

**Implementation Pattern**:
```rust
// Static cell (never reinitialized)
static REGISTRY: OnceLock<RwLock<HashMap<K, V>>> = OnceLock::new();

// Private accessor function
fn registry() -> &'static RwLock<HashMap<K, V>> {
    REGISTRY.get_or_init(|| {
        let mut map = HashMap::new();
        // ... populate defaults ...
        RwLock::new(map)
    })
}

// Public API uses accessor
pub fn register(key: K, value: V) {
    registry().write().unwrap().insert(key, value);
}
```

**Migration Path to Rust 1.80+**:
When we eventually bump MSRV to Rust 1.80+, we can migrate to `std::sync::LazyLock` for slightly cleaner syntax:
```rust
// Rust 1.80+ version (future)
static REGISTRY: LazyLock<RwLock<HashMap<K, V>>> = LazyLock::new(|| {
    let mut map = HashMap::new();
    // ... populate defaults ...
    RwLock::new(map)
});

// Can access REGISTRY directly, no accessor function needed
pub fn register(key: K, value: V) {
    REGISTRY.write().unwrap().insert(key, value);
}
```

This is a one-line change per registry, fully backward compatible.

## Open Questions

1. **Operator precedence**: Always parenthesize, or use precedence rules?
   - Suggestion: Always parenthesize for 0.1.0 (safest, clearest)
   - Future: Add minimal-parens mode

2. **MetaByte ASCII mapping**: Should ph, ps, ch be in:
   - MetaByte implementation (tied to type)
   - AsciiFormatter (formatter-specific)
   - Suggestion: MetaByte owns it (mirrors WideMetavariable UTF-8)

3. **Polish notation**: Need prefix notation for testing vs Megill's reference?
   - Suggestion: Add PolishFormatter if needed for regression tests

4. **LaTeX packages**: Assume `\varphi`, `\to`, etc. are available?
   - Suggestion: Yes, assume standard LaTeX math mode

## Testing Strategy

### Unit Tests
- Each formatter produces expected output for known terms
- Type-color registry works for standard and custom types
- Formatted wrapper integrates with std::fmt

### Regression Tests
- DDD111D23 → `>P>>>~Q~RR>>~Q~RQ` (Polish notation comparison)
- DDD1D221D2D2D11 → `>>>>>PQRQ>>PQR>>>>PQRQR`
- Both tests verify disjointness bug is fixed

### Integration Tests
- compact binary with different `--format` flags
- Long proofs requiring WideMetavariable (>256 variables)

## Future Enhancements (Post-0.1.0)

- MathML formatter
- S-expression formatter (for Lisp-style output)
- Proof tree formatters (ASCII art, GraphViz)
- Custom format specifier proc macro: `println!("{:latex}", term)`
- Configurable color schemes
- Minimal parenthesis mode with precedence
