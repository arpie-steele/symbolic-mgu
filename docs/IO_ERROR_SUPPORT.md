# I/O Error Support Addition

**Date**: 2025-11-19
**Status**: ✅ Complete
**Version**: v0.1.0-alpha.13

## Summary

Added I/O and parsing error support to `MguError` in preparation for Metamath database integration (v0.2.0). This enables seamless error handling for file I/O, network operations, and database parsing.

## Motivation

Future Metamath database integration will require:
1. **File I/O**: Reading `.mm` files and includes (`$[ filename $]`)
2. **Network I/O** (optional): Fetching remote databases via HTTP/HTTPS
3. **Parse errors**: Syntax errors in database files

Current `MguError` had comprehensive logic errors but **zero I/O support**. Adding these variants now:
- ✅ Non-breaking addition (existing code unaffected)
- ✅ Future-proof for v0.2.0 Metamath integration
- ✅ Follows existing patterns (string-based, Clone-able)
- ✅ Standard Rust library pattern

## Changes Made

### 1. New Error Variants

**File**: `src/error/base.rs`

```rust
pub enum MguError {
    // ... existing variants ...

    /// I/O error from file or network operations.
    #[error("I/O error: {0}")]
    IoError(String),

    /// Parse error in database file or data stream.
    #[error("Parse error at {location}: {message}")]
    ParseError {
        location: String,
        message: String,
    },
}
```

### 2. Automatic Conversion from `std::io::Error`

**File**: `src/error/base.rs`

```rust
impl From<std::io::Error> for MguError {
    fn from(err: std::io::Error) -> Self {
        MguError::IoError(err.to_string())
    }
}
```

**Benefits**:
- Enables `?` operator in I/O functions returning `Result<T, MguError>`
- Seamless integration with stdlib file/network operations
- Follows Rust error handling conventions

### 3. Updated `MguErrorType` Enum

**File**: `src/error/err_type.rs`

```rust
pub enum MguErrorType {
    // ... existing types ...
    IoError,
    ParseError,
}
```

### 4. Updated Trait Implementations

- **PartialEq**: Uses discriminant comparison (automatic for new variants) ✅
- **Hash**: Added match arms for `IoError` and `ParseError` ✅
- **get_error_type()**: Added cases returning new error types ✅

### 5. Documentation Examples

Added comprehensive examples in module documentation:

```rust
use symbolic_mgu::MguError;
use std::fs::File;
use std::io::Read;

// Automatic conversion from std::io::Error
fn read_database(path: &str) -> Result<String, MguError> {
    let mut file = File::open(path)?;  // ? operator works!
    let mut contents = String::new();
    file.read_to_string(&mut contents)?;
    Ok(contents)
}

// Parse errors with location info
let err = MguError::ParseError {
    location: "set.mm:42:15".to_string(),
    message: "Expected $a, found $p".to_string(),
};
```

## Design Decisions

### Low Granularity

**Choice**: Two variants (`IoError`, `ParseError`) instead of many specific variants
**Rationale**:
- User-facing errors (not programmatic recovery)
- Simpler API
- Can add specific variants later if needed (non-breaking)
- Matches existing error pattern (string-based for flexibility)

### Clone-able String Storage

**Choice**: Store `.to_string()` instead of `Arc<std::io::Error>`
**Rationale**:
- `std::io::Error` is NOT `Clone`
- Matches existing `MguError` pattern (all variants Clone-able)
- Simpler implementation
- User-facing messages don't need full error object

### Parse Error Location Format

**Format**: Flexible string (e.g., `"file.mm:line:col"` or byte offset)
**Rationale**:
- Different parsers may have different location info
- String flexibility allows: "set.mm:42:15", "byte 1234", "line 42"
- Can include context (e.g., "set.mm:42:15 in theorem ax-mp")

## Usage Examples

### File I/O with `?` Operator

```rust
use symbolic_mgu::MguError;
use std::fs::File;
use std::io::Read;

fn load_database(path: &str) -> Result<String, MguError> {
    let mut file = File::open(path)?;  // Automatic conversion!
    let mut contents = String::new();
    file.read_to_string(&mut contents)?;  // Works here too!
    Ok(contents)
}

match load_database("set.mm") {
    Ok(contents) => println!("Loaded {} bytes", contents.len()),
    Err(e) => eprintln!("Error: {}", e),  // "I/O error: ..."
}
```

### Parse Errors with Context

```rust
use symbolic_mgu::MguError;

fn parse_metamath_statement(line_num: usize, text: &str) -> Result<(), MguError> {
    if !text.starts_with("$a ") && !text.starts_with("$p ") {
        return Err(MguError::ParseError {
            location: format!("set.mm:{}:1", line_num),
            message: format!("Expected $a or $p, found '{}'",
                           text.chars().take(3).collect::<String>()),
        });
    }
    Ok(())
}
```

### Network I/O (Future)

```rust
use symbolic_mgu::MguError;

// If using HTTP library that returns std::io::Error
fn fetch_database(url: &str) -> Result<String, MguError> {
    // HTTP client that returns io::Error
    let response = http_get(url)?;  // Automatic conversion!
    Ok(response.text())
}
```

## Testing

### All Quality Gates Pass ✅

```bash
cargo +1.77 test --all-features              # ✅ 142 unit + 96 doc = 238 tests
cargo +1.77 clippy --all-features --all-targets  # ✅ 0 warnings
cargo +1.77 doc --all-features               # ✅ Clean build (9 doc tests)
cargo +1.77 fmt --check                      # ✅ Formatted
```

### Doc Examples Tested

All documentation examples compile and run:
- ✅ `From<std::io::Error>` conversion example
- ✅ `?` operator in I/O functions example
- ✅ `ParseError` creation example

## Files Modified

1. `src/error/base.rs` - Added 2 variants, `From` impl, Hash impl, doc examples
2. `src/error/err_type.rs` - Added 2 error type enum variants

## Future Use

### Metamath Database Integration (v0.2.0)

```rust
// Tokenizer
fn tokenize_file(path: &str) -> Result<Vec<Token>, MguError> {
    let contents = std::fs::read_to_string(path)?;  // IoError
    parse_tokens(&contents)  // ParseError
}

fn parse_tokens(text: &str) -> Result<Vec<Token>, MguError> {
    let mut tokens = Vec::new();
    let mut line = 1;
    let mut col = 1;

    for ch in text.chars() {
        if !is_valid_token_char(ch) {
            return Err(MguError::ParseError {
                location: format!("{}:{}", line, col),
                message: format!("Invalid character '{}'", ch),
            });
        }
        // ... tokenization logic
    }
    Ok(tokens)
}
```

### Database Parser

```rust
fn parse_database(path: &str) -> Result<Database, MguError> {
    let tokens = tokenize_file(path)?;

    for (i, token) in tokens.iter().enumerate() {
        match token {
            Token::Include(file) => {
                // Recursive include - IoError possible
                parse_database(file)?;
            }
            Token::Axiom { .. } => { /* ... */ }
            Token::Proof { .. } => { /* ... */ }
            _ => {
                return Err(MguError::ParseError {
                    location: format!("{}:token#{}", path, i),
                    message: format!("Unexpected token: {:?}", token),
                });
            }
        }
    }
    Ok(database)
}
```

## API Stability

✅ **Non-Breaking Addition**:
- Adds new variants (doesn't modify existing ones)
- Doesn't change function signatures
- Existing code continues to work unchanged
- Can add more specific variants later if needed

✅ **Compatible with v0.1.0 Release**:
- No dependencies on unreleased features
- No MSRV impact (uses stdlib only)
- Follows existing error patterns
- Well-documented and tested

## Conclusion

I/O error support successfully added to `MguError`. Ready for v0.1.0 release and future Metamath database integration in v0.2.0.

**Impact**: Zero breaking changes, enables future database I/O, follows Rust best practices.
