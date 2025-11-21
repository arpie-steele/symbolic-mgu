# Parametric Metavariable Design

## Overview

Design document for `ParametricMetavariable<Ty, U, CharSet>`, a generic metavariable implementation that decouples type systems, decoration schemes, and output formats.

**Status**: Design phase (planned for v0.1.1+)
**Author**: Design discussion 2025-01-04
**Replaces**: `WideMetavariable` (after testing)
**Prerequisites**: Phase 7.10 (Output Formatters) - **COMPLETE** (v0.1.0-alpha.10)

## Motivation

Current `WideMetavariable` limitations:
- Hardcoded to `SimpleType`
- Fixed UTF-8 display format (no ASCII/LaTeX alternatives)
- Subscript-only decoration (no primes, other notations)
- Character tables embedded in implementation

## Design Goals

1. **Type independence**: Work with any `Type` trait implementation
2. **Format flexibility**: Support ASCII, UTF-8, LaTeX, HTML, etc.
3. **Decoration control**: Subscripts, primes, or custom decorators via type parameter `U`
4. **Zero-cost abstractions**: `U=()` compiles to no decorator overhead
5. **Extensibility**: Allow third-party character sets (v0.1.1+)

## Core Design

### Type Signature

```rust
pub struct ParametricMetavariable<Ty, U, CharSet> {
    ty: Ty,              // Type (Boolean, Setvar, Class, or custom)
    base_index: usize,   // Which character within type (0..max_index)
    decorator: U,        // () | usize | u8 | Prime | custom
    _charset: PhantomData<CharSet>,
}
```

### Type Parameters

- **`Ty: Type`**: The type system (SimpleType, or custom implementations)
- **`U: Decorator`**: Controls what appears after base character
  - `()` → no decoration (φ, ψ, χ)
  - `usize` → numeric subscripts (φ, φ₁, φ₂, ...)
  - `u8` → compact subscripts (limited to 0-255)
  - `Prime` → prime notation (φ, φ′, φ″, φ‴)
  - Custom enums → domain-specific notation
- **`CharSet`**: Provides character tables for different output formats

### Enumeration Order

**Design Decision**: Cycle through base characters first, then increment decorator.

**Rationale**: Even with `U=u8` (256 decorators), humans won't exhaust subscripts for base characters. Repeating the same base character with different meanings (e.g., φ as Boolean and φ as Setvar) would cause confusion.

**Enumeration Sequence**:
```
index 0:  φ   (base 0, decorator 0)
index 1:  ψ   (base 1, decorator 0)
index 2:  χ   (base 2, decorator 0)
...
index 11: κ   (base 11, decorator 0)
index 12: φ₁  (base 0, decorator 1)
index 13: ψ₁  (base 1, decorator 1)
...
```

**Formula**:
```rust
let max_base = CharSet::max_index(&ty);
let base_index = global_index % (max_base + 1);
let decorator_count = global_index / (max_base + 1);
```

## Component 1: Decorator Trait

```rust
/// Controls decoration after base character
pub trait Decorator: Copy + Eq + Hash + Debug + Default {
    /// Format for ASCII output
    fn format_ascii(&self) -> String;

    /// Format for UTF-8 output (Unicode subscripts, primes, etc.)
    fn format_utf8(&self) -> String;

    /// Format for LaTeX output
    fn format_latex(&self) -> String;

    /// Next decorator in sequence (for enumeration)
    fn next(&self) -> Option<Self>;
}
```

### Built-in Decorator Implementations

#### No Decoration: `()`
```rust
impl Decorator for () {
    fn format_ascii(&self) -> String { String::new() }
    fn format_utf8(&self) -> String { String::new() }
    fn format_latex(&self) -> String { String::new() }
    fn next(&self) -> Option<Self> { Some(()) }
}
```

#### Numeric Subscripts: `usize`
```rust
impl Decorator for usize {
    fn format_ascii(&self) -> String {
        if *self == 0 { String::new() } else { format!("{}", self) }
    }

    fn format_utf8(&self) -> String {
        if *self == 0 { return String::new(); }
        // Map digits to Unicode subscripts (U+2080..U+2089)
        format!("{}", self).chars()
            .map(|ch| char::from_u32(0x2080 + (ch as u32 - '0' as u32)).unwrap())
            .collect()
    }

    fn format_latex(&self) -> String {
        if *self == 0 { String::new() } else { format!("_{{{}}}", self) }
    }

    fn next(&self) -> Option<Self> { self.checked_add(1) }
}
```

#### Prime Notation: `Prime`
```rust
#[derive(Copy, Clone, Debug, Eq, PartialEq, Hash)]
pub enum Prime {
    None,    // φ
    Single,  // φ′ (U+2032) or φ'
    Double,  // φ″ (U+2033) or φ''
    Triple,  // φ‴ (U+2034) or φ'''
}

impl Default for Prime {
    fn default() -> Self { Prime::None }
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
            Prime::Single => "′".to_string(),  // U+2032
            Prime::Double => "″".to_string(),  // U+2033
            Prime::Triple => "‴".to_string(),  // U+2034
        }
    }

    fn format_latex(&self) -> String { self.format_ascii() }

    fn next(&self) -> Option<Self> {
        match self {
            Prime::None => Some(Prime::Single),
            Prime::Single => Some(Prime::Double),
            Prime::Double => Some(Prime::Triple),
            Prime::Triple => None,  // Exhausted
        }
    }
}
```

## Component 2: Character Set

### v0.1.0 Approach: Compile-Time Constants (Option B)

**Design**: Direct const arrays with dispatcher functions. Zero runtime cost, no trait overhead.

```rust
/// Character set for WideMetavariable-style display
pub struct WideCharSet;

impl WideCharSet {
    // Boolean characters
    pub const fn ascii_boolean(index: usize) -> Option<&'static str> {
        const CHARS: &[&str] = &[
            "ph", "ps", "ch", "th", "ta", "et",
            "ze", "si", "rh", "mu", "la", "ka"
        ];
        if index < CHARS.len() { Some(CHARS[index]) } else { None }
    }

    pub const fn utf8_boolean(index: usize) -> Option<&'static str> {
        const CHARS: &[&str] = &[
            "𝜑", "𝜓", "𝜒", "𝜃", "𝜏", "𝜂",
            "𝜁", "𝜎", "𝜌", "𝜇", "𝜆", "𝜅"
        ];
        if index < CHARS.len() { Some(CHARS[index]) } else { None }
    }

    pub const fn latex_boolean(index: usize) -> Option<&'static str> {
        const CHARS: &[&str] = &[
            "\\varphi", "\\psi", "\\chi", "\\theta", "\\tau", "\\eta",
            "\\zeta", "\\sigma", "\\rho", "\\mu", "\\lambda", "\\kappa"
        ];
        if index < CHARS.len() { Some(CHARS[index]) } else { None }
    }

    // Setvar characters (24 chars)
    pub const fn ascii_setvar(index: usize) -> Option<&'static str> {
        const CHARS: &[&str] = &[
            "x", "y", "z", "w", "v", "u", "t", "f", "g", "s", "e", "h",
            "i", "j", "k", "m", "n", "o", "r", "q", "p", "a", "b", "c", "d", "l"
        ];
        if index < CHARS.len() { Some(CHARS[index]) } else { None }
    }

    pub const fn utf8_setvar(index: usize) -> Option<&'static str> {
        const CHARS: &[&str] = &[
            "𝑥", "𝑦", "𝑧", "𝑤", "𝑣", "𝑢", "𝑡", "𝑓", "𝑔", "𝑠", "𝑒", "ℎ",
            "𝑖", "𝑗", "𝑘", "𝑚", "𝑛", "𝑜", "𝑟", "𝑞", "𝑝", "𝑎", "𝑏", "𝑐", "𝑑", "𝑙"
        ];
        if index < CHARS.len() { Some(CHARS[index]) } else { None }
    }

    pub const fn latex_setvar(index: usize) -> Option<&'static str> {
        const CHARS: &[&str] = &[
            "x", "y", "z", "w", "v", "u", "t", "f", "g", "s", "e", "h",
            "i", "j", "k", "m", "n", "o", "r", "q", "p", "a", "b", "c", "d", "l"
        ];
        if index < CHARS.len() { Some(CHARS[index]) } else { None }
    }

    // Class characters (24 chars)
    pub const fn ascii_class(index: usize) -> Option<&'static str> {
        const CHARS: &[&str] = &[
            "A", "B", "C", "D", "P", "Q", "R", "S", "T", "U", "E", "F",
            "G", "H", "I", "J", "K", "L", "M", "N", "V", "W", "X", "Y", "Z", "O"
        ];
        if index < CHARS.len() { Some(CHARS[index]) } else { None }
    }

    pub const fn utf8_class(index: usize) -> Option<&'static str> {
        const CHARS: &[&str] = &[
            "𝐴", "𝐵", "𝐶", "𝐷", "𝑃", "𝑄", "𝑅", "𝑆", "𝑇", "𝑈", "𝐸", "𝐹",
            "𝐺", "𝐻", "𝐼", "𝐽", "𝐾", "𝐿", "𝑀", "𝑁", "𝑉", "𝑊", "𝑋", "𝑌", "𝑍", "𝑂"
        ];
        if index < CHARS.len() { Some(CHARS[index]) } else { None }
    }

    pub const fn latex_class(index: usize) -> Option<&'static str> {
        const CHARS: &[&str] = &[
            "A", "B", "C", "D", "P", "Q", "R", "S", "T", "U", "E", "F",
            "G", "H", "I", "J", "K", "L", "M", "N", "V", "W", "X", "Y", "Z", "O"
        ];
        if index < CHARS.len() { Some(CHARS[index]) } else { None }
    }

    // Type dispatcher (non-const until Rust supports const match on traits)
    pub fn ascii_char(ty: &SimpleType, index: usize) -> Option<&'static str> {
        match ty {
            SimpleType::Boolean => Self::ascii_boolean(index),
            SimpleType::Setvar => Self::ascii_setvar(index),
            SimpleType::Class => Self::ascii_class(index),
        }
    }

    pub fn utf8_char(ty: &SimpleType, index: usize) -> Option<&'static str> {
        match ty {
            SimpleType::Boolean => Self::utf8_boolean(index),
            SimpleType::Setvar => Self::utf8_setvar(index),
            SimpleType::Class => Self::utf8_class(index),
        }
    }

    pub fn latex_char(ty: &SimpleType, index: usize) -> Option<&'static str> {
        match ty {
            SimpleType::Boolean => Self::latex_boolean(index),
            SimpleType::Setvar => Self::latex_setvar(index),
            SimpleType::Class => Self::latex_class(index),
        }
    }

    pub const fn max_index(ty: &SimpleType) -> usize {
        match ty {
            SimpleType::Boolean => 11,  // 12 chars (0..11)
            SimpleType::Setvar => 23,   // 24 chars (0..23)
            SimpleType::Class => 23,    // 24 chars (0..23)
        }
    }
}
```

**Pros**:
- Zero runtime cost (direct array indexing)
- Aggressive inlining
- Works in `const fn` contexts (mostly)
- Simple to understand and maintain
- Excellent cache locality

**Cons**:
- Not extensible by third parties
- Must modify source to add character sets
- Type dispatcher can't be `const fn` in Rust 1.77

### v0.1.1+ Approach: Hybrid Trait + Constants (Option C)

**Design**: Define trait for uniform interface, but implement built-ins using const arrays.

```rust
/// Trait for character set extensibility
pub trait MetavariableCharSet<Ty: Type> {
    /// ASCII representation (Metamath-compatible)
    fn ascii_char(ty: &Ty, index: usize) -> Option<&'static str>;

    /// UTF-8 representation (Unicode mathematical symbols)
    fn utf8_char(ty: &Ty, index: usize) -> Option<&'static str>;

    /// LaTeX representation
    fn latex_char(ty: &Ty, index: usize) -> Option<&'static str>;

    /// Maximum base index for this type (before decorators)
    fn max_index(ty: &Ty) -> usize;
}

// Built-in implementation using const arrays (zero cost)
impl MetavariableCharSet<SimpleType> for WideCharSet {
    fn ascii_char(ty: &SimpleType, index: usize) -> Option<&'static str> {
        // Delegate to const functions
        match ty {
            SimpleType::Boolean => Self::ascii_boolean(index),
            SimpleType::Setvar => Self::ascii_setvar(index),
            SimpleType::Class => Self::ascii_class(index),
        }
    }

    // ... similar for utf8_char, latex_char, max_index
}

// Third-party implementations (small cost for flexibility)
pub struct CustomCharSet;

impl MetavariableCharSet<SimpleType> for CustomCharSet {
    fn ascii_char(ty: &SimpleType, index: usize) -> Option<&'static str> {
        // Could load from config, database, etc.
        todo!()
    }
    // ...
}
```

**Upgrade Path**:
1. v0.1.0: Ship with Option B (const arrays, no trait)
2. v0.1.1: Add trait definition, implement for `WideCharSet`
3. No breaking changes (semver-compatible)

**Pros**:
- Zero cost for built-in character sets
- Extensible by third parties
- Uniform interface via trait
- Opt-in flexibility cost

**Cons**:
- Two mechanisms to document
- Slightly more complex implementation

## Component 3: ParametricMetavariable Implementation

```rust
/// Generic metavariable with pluggable types, decorators, and character sets
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug, PartialOrd, Ord)]
pub struct ParametricMetavariable<Ty, U, CharSet> {
    /// Type of this metavariable
    ty: Ty,
    /// Index within character set for this type (0..max_index)
    base_index: usize,
    /// Decoration (subscript, prime, etc.)
    decorator: U,
    /// Zero-sized marker for character set
    _charset: PhantomData<CharSet>,
}

impl<Ty, U, CharSet> ParametricMetavariable<Ty, U, CharSet>
where
    Ty: Type + Clone,
    U: Decorator,
{
    /// Format as ASCII (Metamath-compatible)
    pub fn format_as_ascii(&self) -> String {
        let base = CharSet::ascii_char(&self.ty, self.base_index)
            .unwrap_or("?");
        format!("{}{}", base, self.decorator.format_ascii())
    }

    /// Format as UTF-8 (Unicode mathematical symbols)
    pub fn format_as_utf8(&self) -> String {
        let base = CharSet::utf8_char(&self.ty, self.base_index)
            .unwrap_or("?");
        format!("{}{}", base, self.decorator.format_utf8())
    }

    /// Format as LaTeX
    pub fn format_as_latex(&self) -> String {
        let base = CharSet::latex_char(&self.ty, self.base_index)
            .unwrap_or("?");
        format!("{}{}", base, self.decorator.format_latex())
    }
}

// Default Display uses UTF-8
impl<Ty, U, CharSet> Display for ParametricMetavariable<Ty, U, CharSet>
where
    Ty: Type + Clone,
    U: Decorator,
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.format_as_utf8())
    }
}
```

### Metavariable Trait Implementation

```rust
impl<Ty, U, CharSet> Metavariable for ParametricMetavariable<Ty, U, CharSet>
where
    Ty: Type + Clone + Debug + Display + Hash + Eq,
    U: Decorator,
{
    type Type = Ty;

    fn try_from_type_and_index(ty: Ty, index: usize) -> Result<Self, MguError> {
        let max_base = CharSet::max_index(&ty);
        let base_index = index % (max_base + 1);
        let decorator_count = index / (max_base + 1);

        // Build decorator by iterating next()
        let mut decorator = U::default();
        for _ in 0..decorator_count {
            decorator = decorator.next().ok_or_else(||
                MguError::from_index_and_len(Some(ty.clone()), index, usize::MAX))?;
        }

        Ok(ParametricMetavariable {
            ty,
            base_index,
            decorator,
            _charset: PhantomData,
        })
    }

    fn get_type_and_index(&self) -> Result<(Ty, usize), MguError> {
        let max_base = CharSet::max_index(&self.ty);

        // Reconstruct decorator count by iterating next()
        let mut count = 0usize;
        let mut d = U::default();
        while d != self.decorator {
            d = d.next().ok_or_else(||
                MguError::UnknownMetavariable("ParametricMetavariable", format!("{:?}", self)))?;
            count += 1;
        }

        let index = self.base_index + count * (max_base + 1);
        Ok((self.ty.clone(), index))
    }

    fn max_index_by_type(typ: Ty) -> usize {
        // If decorator is bounded (e.g., u8), compute actual max
        // Otherwise return usize::MAX
        usize::MAX
    }

    fn enumerate(for_type: Ty) -> impl Iterator<Item = Self> {
        ParametricMetavariableIterator::new(for_type)
    }
}

// Iterator implementation
struct ParametricMetavariableIterator<Ty, U, CharSet> {
    ty: Ty,
    base_index: usize,
    decorator: U,
    _charset: PhantomData<CharSet>,
}

impl<Ty, U, CharSet> Iterator for ParametricMetavariableIterator<Ty, U, CharSet>
where
    Ty: Type + Clone,
    U: Decorator,
{
    type Item = ParametricMetavariable<Ty, U, CharSet>;

    fn next(&mut self) -> Option<Self::Item> {
        let result = ParametricMetavariable {
            ty: self.ty.clone(),
            base_index: self.base_index,
            decorator: self.decorator,
            _charset: PhantomData,
        };

        // Increment: cycle base_index first, then decorator
        let max_base = CharSet::max_index(&self.ty);
        self.base_index += 1;
        if self.base_index > max_base {
            self.base_index = 0;
            self.decorator = self.decorator.next()?;
        }

        Some(result)
    }
}
```

## Type Aliases for Common Patterns

```rust
// Current WideMetavariable equivalent
pub type WideMetavariable2 = ParametricMetavariable<SimpleType, usize, WideCharSet>;

// No subscripts, just base characters (φ, ψ, χ, ...)
pub type SimpleMetavariable = ParametricMetavariable<SimpleType, (), WideCharSet>;

// Prime notation (φ, φ′, φ″, φ‴)
pub type PrimeMetavariable = ParametricMetavariable<SimpleType, Prime, WideCharSet>;

// Compact u8 subscripts (φ, φ₁, ..., φ₂₅₅)
pub type CompactMetavariable = ParametricMetavariable<SimpleType, u8, WideCharSet>;
```

## Integration with Phase 7.10 (Output Formatters) - COMPLETE

Phase 7.10 has been fully implemented in v0.1.0-alpha.10. The `Metavariable` trait now includes:

```rust
// Already implemented in Metavariable trait (v0.1.0-alpha.10)
pub trait Metavariable: Display + Debug + Clone + Hash + PartialEq + Eq {
    type Type: Type;

    // ... existing methods ...

    /// Format this metavariable using the specified output formatter
    fn format_with(&self, formatter: &dyn OutputFormatter) -> String {
        // Default: delegate to Display
        format!("{}", self)
    }

    fn to_ascii(&self) -> String { format!("{}", self) }
    fn to_utf8(&self) -> String { format!("{}", self) }
}

// WideMetavariable already implements format_with() (v0.1.0-alpha.10)
impl Metavariable for WideMetavariable {
    fn format_with(&self, formatter: &dyn OutputFormatter) -> String {
        match formatter.name() {
            "ascii" => self.to_ascii(),
            "latex" => self.to_latex(),
            "html" | "html-color" => self.to_html(formatter),
            "utf8-color" => self.to_utf8_color(formatter),
            _ => self.to_utf8(),
        }
    }
}

// ParametricMetavariable will follow the same pattern
impl<Ty, U, CharSet> Metavariable for ParametricMetavariable<Ty, U, CharSet>
where
    Ty: Type + Clone + Debug + Display + Hash + Eq,
    U: Decorator,
{
    fn format_with(&self, formatter: &dyn OutputFormatter) -> String {
        match formatter.name() {
            "ascii" => self.format_as_ascii(),
            "utf8" | "utf8-color" => self.format_as_utf8(),
            "latex" => self.format_as_latex(),
            _ => format!("{}", self),  // Fallback to Display
        }
    }
}
```

### OutputFormatter Trait (Implemented)

The `OutputFormatter` trait is object-safe and uses delegation:

```rust
pub trait OutputFormatter: Send + Sync {
    fn name(&self) -> &str;
    fn get_boolean_color(&self) -> Option<Color> { None }
    fn get_setvar_color(&self) -> Option<Color> { None }
    fn get_class_color(&self) -> Option<Color> { None }
    fn is_infix(&self) -> bool { true }
}
```

ParametricMetavariable can integrate seamlessly with this existing infrastructure.

## Migration Path

**Updated Timeline**: Based on Phase 7.10 completion (v0.1.0-alpha.10)

### Phase 1: v0.1.1 - Implement ParametricMetavariable

1. Create `src/metavariable/parametric.rs`
2. Implement `Decorator` trait with `()`, `usize`, `Prime`
3. Implement `WideCharSet` using const arrays (Option B)
4. Implement `ParametricMetavariable<Ty, U, CharSet>`
5. Implement `format_with()` using existing `OutputFormatter` infrastructure
6. Add type alias: `pub type WideMetavariable2 = ParametricMetavariable<SimpleType, usize, WideCharSet>`
7. Export from `lib.rs`
8. **Do not deprecate `WideMetavariable` yet**

### Phase 2: v0.1.2 - Testing

1. Add comprehensive unit tests
2. Test with compact binary on long proofs
3. Benchmark against `WideMetavariable`
4. Verify formatting matches current output (all 6 formatters)
5. Test integration with existing formatter system

### Phase 3: v0.2.0 - Replace WideMetavariable (Breaking Change)

1. Deprecate `WideMetavariable` (mark with `#[deprecated]`)
2. Update `WideMetavariableFactory` to create `WideMetavariable2`
3. Update all examples and docs
4. Migration guide in CHANGELOG
5. Announce breaking change with clear upgrade path

### Phase 4: v0.2.1+ - Add Trait Extensibility

1. Define `MetavariableCharSet<Ty>` trait (Option C)
2. Implement trait for `WideCharSet` (wraps const arrays)
3. Document third-party character set creation
4. Example: Metamath legacy character set
5. Example: Custom domain-specific character sets

## Open Questions

1. **Decorator bounds**: Should `Decorator` require `Default`? Or pass initial value to `try_from_type_and_index`?
2. **CharSet as type param vs trait object**: Current design uses ZST type parameter. Alternative: `CharSet: &'static dyn MetavariableCharSet<Ty>`?
3. **HTML/Polish formatters**: Should these be first-class alongside ASCII/UTF-8/LaTeX, or extensions?
4. **Serialization**: How should `serde` support work with generic `CharSet`?

## References

- Phase 7.9: WideMetavariable Backport (completed)
- Phase 7.10: Output Formatter System (planned)
- `docs/FORMATTER_DESIGN.md`: Output formatter architecture
