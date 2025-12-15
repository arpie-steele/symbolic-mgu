//! Label validation and punycode encoding for Metamath identifiers.
//!
//! Metamath strictly requires ASCII-only labels, but this implementation relaxes
//! that requirement by supporting UTF-8 labels encoded as punycode (RFC 3492).
//!
//! # Label Rules
//!
//! Valid labels consist of:
//! - ASCII alphanumeric characters (a-z, A-Z, 0-9)
//! - Hyphens (`-`), underscores (`_`), and periods (`.`)
//! - No whitespace or dollar signs (`$`)
//!
//! # Punycode Encoding
//!
//! Non-ASCII labels are automatically encoded using punycode with the `xn--` prefix.
//! This allows UTF-8 labels (e.g., "теорема") to be represented as ASCII
//! (e.g., "xn--80aja2aiml") for interchange with standard Metamath tools.
//!
//! # Interchange Format
//!
//! For file interchange with standard Metamath tools, use the **encoded** form:
//!
//! ```text
//! $c wff $.
//! $v ph ps $.
//! xn--80aja2aiml $a wff ph $.  $( "теорема" in punycode $)
//! ```
//!
//! When reading files, use `Label::from_encoded()` to handle both ASCII and
//! punycode labels transparently.
//!
//! # Examples
//!
//! ```
//! use symbolic_mgu::metamath::Label;
//!
//! // ASCII label - no encoding needed
//! let label = Label::new("ax-mp").unwrap();
//! assert_eq!(label.as_str(), "ax-mp");
//! assert_eq!(label.encoded(), "ax-mp");
//!
//! // UTF-8 label - automatically encoded
//! let label = Label::new("теорема").unwrap();
//! assert_eq!(label.as_str(), "теорема");
//! assert!(label.encoded().starts_with("xn--"));
//!
//! // Reading encoded labels
//! let label = Label::from_encoded("xn--80aja2aiml").unwrap();
//! assert_eq!(label.as_str(), "теорема");
//! ```

use std::fmt;
use std::sync::Arc;
use thiserror::Error;

/// Errors that can occur during label validation or encoding.
#[derive(Debug, Error, Clone, PartialEq, Eq)]
pub enum LabelError {
    /// Label is empty.
    #[error("Label cannot be empty")]
    Empty,

    /// Label contains invalid characters.
    #[error("Label contains invalid characters: {0}")]
    InvalidCharacters(String),

    /// Label contains whitespace.
    #[error("Label cannot contain whitespace")]
    Whitespace,

    /// Label contains a dollar sign.
    #[error("Label cannot contain '$'")]
    DollarSign,

    /// Punycode encoding failed.
    #[error("Punycode encoding failed: {0}")]
    EncodingError(String),

    /// Punycode decoding failed.
    #[error("Punycode decoding failed: {0}")]
    DecodingError(String),
}

/// A validated Metamath label with optional punycode encoding.
///
/// Labels are the primary identifiers in Metamath for axioms, theorems, and
/// hypotheses. This type ensures labels are valid and handles UTF-8 via punycode.
///
/// # Memory Efficiency
///
/// Labels use `Arc<str>` internally to allow cheap cloning and sharing.
#[derive(Debug, Clone, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct Label {
    /// The original (possibly UTF-8) label.
    original: Arc<str>,
    /// The ASCII-encoded form (punycode if needed).
    encoded: Arc<str>,
}

impl Label {
    /// Create a new label, validating and encoding as needed.
    ///
    /// # Arguments
    /// * `label` - The label text (ASCII or UTF-8)
    ///
    /// # Returns
    /// A validated `Label`, or an error if validation fails.
    ///
    /// # Errors
    ///
    /// Returns an error if the label is empty, contains whitespace or dollar signs,
    /// or contains invalid characters.
    ///
    /// # Examples
    ///
    /// ```
    /// use symbolic_mgu::metamath::Label;
    ///
    /// let label = Label::new("ax-1").unwrap();
    /// assert_eq!(label.as_str(), "ax-1");
    ///
    /// let label = Label::new("теорема").unwrap();
    /// assert_eq!(label.as_str(), "теорема");
    /// assert!(label.encoded().starts_with("xn--"));
    /// ```
    pub fn new(label: impl AsRef<str>) -> Result<Self, LabelError> {
        let label = label.as_ref();

        // Validate not empty
        if label.is_empty() {
            return Err(LabelError::Empty);
        }

        // Check for whitespace
        if label.chars().any(|c| c.is_whitespace()) {
            return Err(LabelError::Whitespace);
        }

        // Check for dollar sign
        if label.contains('$') {
            return Err(LabelError::DollarSign);
        }

        // Check if encoding is needed (contains non-ASCII)
        let encoded = if label.is_ascii() {
            // Validate ASCII characters
            Self::validate_ascii(label)?;
            Arc::from(label)
        } else {
            // Encode as punycode
            Arc::from(encode_punycode(label)?)
        };

        Ok(Self {
            original: Arc::from(label),
            encoded,
        })
    }

    /// Validate ASCII label characters.
    fn validate_ascii(label: &str) -> Result<(), LabelError> {
        for ch in label.chars() {
            if !ch.is_ascii_alphanumeric() && ch != '-' && ch != '_' && ch != '.' {
                return Err(LabelError::InvalidCharacters(format!(
                    "character '{}' (U+{:04X})",
                    ch, ch as u32
                )));
            }
        }
        Ok(())
    }

    /// Get the original (possibly UTF-8) label.
    pub fn as_str(&self) -> &str {
        &self.original
    }

    /// Get the ASCII-encoded form (punycode if original was UTF-8).
    ///
    /// This is the form used for file interchange with standard Metamath tools.
    pub fn encoded(&self) -> &str {
        &self.encoded
    }

    /// Check if this label required encoding (contains non-ASCII).
    pub fn is_encoded(&self) -> bool {
        !self.original.is_ascii()
    }

    /// Parse a label from its encoded (punycode) form.
    ///
    /// # Arguments
    /// * `encoded` - The ASCII-encoded label (possibly with `xn--` prefix)
    ///
    /// # Returns
    /// A `Label` with the decoded original form.
    ///
    /// # Errors
    ///
    /// Returns an error if the encoded label is empty or if punycode decoding fails.
    pub fn from_encoded(encoded: impl AsRef<str>) -> Result<Self, LabelError> {
        let encoded = encoded.as_ref();

        if encoded.is_empty() {
            return Err(LabelError::Empty);
        }

        // Check if it's punycode-encoded
        let original = if encoded.starts_with("xn--") {
            Arc::from(decode_punycode(encoded)?)
        } else {
            // Plain ASCII label
            Self::validate_ascii(encoded)?;
            Arc::from(encoded)
        };

        Ok(Self {
            original,
            encoded: Arc::from(encoded),
        })
    }
}

impl fmt::Display for Label {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.original)
    }
}

impl AsRef<str> for Label {
    fn as_ref(&self) -> &str {
        &self.original
    }
}

// Punycode parameters (RFC 3492)
/// Base for variable-length encoding (36 = digits + letters)
const BASE: u32 = 36;
/// Minimum threshold value
const TMIN: u32 = 1;
/// Maximum threshold value
const TMAX: u32 = 26;
/// Skew parameter for bias adaptation
const SKEW: u32 = 38;
/// Damping factor for bias adaptation
const DAMP: u32 = 700;
/// Initial bias value
const INITIAL_BIAS: u32 = 72;
/// Initial code point (first non-ASCII Unicode value)
const INITIAL_N: u32 = 0x80;
/// Delimiter between basic and extended characters
const DELIMITER: char = '-';

/// Encode a UTF-8 string as punycode with `xn--` prefix.
///
/// Implements RFC 3492 (Punycode) encoding.
fn encode_punycode(input: &str) -> Result<String, LabelError> {
    let mut output = String::from("xn--");

    // Extract basic code points (ASCII)
    let basic: Vec<char> = input.chars().filter(|&c| c.is_ascii()).collect();
    let basic_len = basic.len();

    // Append basic code points
    for &c in &basic {
        output.push(c);
    }

    // If there were basic code points, add delimiter
    if basic_len > 0 && basic_len < input.chars().count() {
        output.push(DELIMITER);
    }

    // If all ASCII, we're done
    if basic_len == input.chars().count() {
        return Ok(output);
    }

    let input_chars: Vec<char> = input.chars().collect();
    let input_len = input_chars.len();
    let mut n = INITIAL_N;
    let mut delta = 0u32;
    let mut bias = INITIAL_BIAS;
    let mut h = basic_len;

    while h < input_len {
        // Find next code point to encode
        let m = input_chars
            .iter()
            .filter(|&&c| (c as u32) >= n)
            .map(|&c| c as u32)
            .min()
            .ok_or_else(|| LabelError::EncodingError("No more code points".to_string()))?;

        delta = delta
            .checked_add(
                (m - n)
                    .checked_mul((h + 1) as u32)
                    .ok_or_else(|| LabelError::EncodingError("Overflow in delta".to_string()))?,
            )
            .ok_or_else(|| LabelError::EncodingError("Overflow in delta add".to_string()))?;

        n = m;

        for &c in &input_chars {
            let c_val = c as u32;

            match c_val.cmp(&n) {
                std::cmp::Ordering::Less => {
                    delta = delta
                        .checked_add(1)
                        .ok_or_else(|| LabelError::EncodingError("Delta overflow".to_string()))?;
                }
                std::cmp::Ordering::Equal => {
                    let mut q = delta;
                    let mut k = BASE;

                    loop {
                        let t = if k <= bias {
                            TMIN
                        } else if k >= bias + TMAX {
                            TMAX
                        } else {
                            k - bias
                        };

                        if q < t {
                            break;
                        }

                        let digit = t + ((q - t) % (BASE - t));
                        output.push(encode_digit(digit));

                        q = (q - t) / (BASE - t);
                        k += BASE;
                    }

                    output.push(encode_digit(q));
                    bias = adapt(delta, h + 1, h == basic_len);
                    delta = 0;
                    h += 1;
                }
                std::cmp::Ordering::Greater => {
                    // `c_val` > n, skip
                }
            }
        }

        delta += 1;
        n += 1;
    }

    Ok(output)
}

/// Decode a punycode string (with `xn--` prefix) to UTF-8.
///
/// Implements RFC 3492 (Punycode) decoding.
fn decode_punycode(encoded: &str) -> Result<String, LabelError> {
    // Remove xn-- prefix
    let encoded = encoded
        .strip_prefix("xn--")
        .ok_or_else(|| LabelError::DecodingError("Missing xn-- prefix".to_string()))?;

    // Find last delimiter
    let (basic, extended) = if let Some(pos) = encoded.rfind(DELIMITER) {
        (&encoded[..pos], &encoded[pos + 1..])
    } else {
        ("", encoded)
    };

    let mut output: Vec<char> = basic.chars().collect();
    let mut n = INITIAL_N;
    let mut i = 0u32;
    let mut bias = INITIAL_BIAS;

    let mut iter = extended.chars();
    while iter.clone().next().is_some() {
        let oldi = i;
        let mut w = 1u32;
        let mut k = BASE;

        loop {
            let digit = decode_digit(
                iter.next()
                    .ok_or_else(|| LabelError::DecodingError("Unexpected end".to_string()))?,
            )?;

            i = i
                .checked_add(
                    digit
                        .checked_mul(w)
                        .ok_or_else(|| LabelError::DecodingError("Overflow".to_string()))?,
                )
                .ok_or_else(|| LabelError::DecodingError("Overflow in i".to_string()))?;

            let t = if k <= bias {
                TMIN
            } else if k >= bias + TMAX {
                TMAX
            } else {
                k - bias
            };

            if digit < t {
                break;
            }

            w = w
                .checked_mul(BASE - t)
                .ok_or_else(|| LabelError::DecodingError("Overflow in w".to_string()))?;

            k += BASE;
        }

        bias = adapt(i - oldi, output.len() + 1, oldi == 0);
        n = n
            .checked_add(i / (output.len() as u32 + 1))
            .ok_or_else(|| LabelError::DecodingError("Overflow in n".to_string()))?;
        i %= output.len() as u32 + 1;

        let c = char::from_u32(n)
            .ok_or_else(|| LabelError::DecodingError(format!("Invalid code point: {}", n)))?;

        output.insert(i as usize, c);
        i += 1;
    }

    Ok(output.into_iter().collect())
}

/// Encode a digit (0-35) as a base-36 character.
fn encode_digit(digit: u32) -> char {
    match digit {
        0..=25 => (b'a' + digit as u8) as char,
        26..=35 => (b'0' + (digit - 26) as u8) as char,
        _ => panic!("Invalid digit: {}", digit),
    }
}

/// Decode a base-36 character to a digit (0-35).
fn decode_digit(c: char) -> Result<u32, LabelError> {
    match c {
        'a'..='z' => Ok((c as u8 - b'a') as u32),
        '0'..='9' => Ok((c as u8 - b'0') as u32 + 26),
        _ => Err(LabelError::DecodingError(format!(
            "Invalid punycode character: '{}'",
            c
        ))),
    }
}

/// Adapt the bias after each delta encoding.
fn adapt(delta: u32, numpoints: usize, firsttime: bool) -> u32 {
    let mut delta = if firsttime { delta / DAMP } else { delta / 2 };

    delta += delta / numpoints as u32;

    let mut k = 0;
    while delta > ((BASE - TMIN) * TMAX) / 2 {
        delta /= BASE - TMIN;
        k += BASE;
    }

    k + (((BASE - TMIN + 1) * delta) / (delta + SKEW))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn ascii_label() {
        let label = Label::new("ax-1").unwrap();
        assert_eq!(label.as_str(), "ax-1");
        assert_eq!(label.encoded(), "ax-1");
        assert!(!label.is_encoded());
    }

    #[test]
    fn label_with_underscore() {
        let label = Label::new("my_label").unwrap();
        assert_eq!(label.as_str(), "my_label");
        assert!(!label.is_encoded());
    }

    #[test]
    fn label_with_period() {
        let label = Label::new("label.2").unwrap();
        assert_eq!(label.as_str(), "label.2");
        assert!(!label.is_encoded());
    }

    #[test]
    fn empty_label() {
        let result = Label::new("");
        assert!(matches!(result, Err(LabelError::Empty)));
    }

    #[test]
    fn label_with_whitespace() {
        let result = Label::new("ax 1");
        assert!(matches!(result, Err(LabelError::Whitespace)));
    }

    #[test]
    fn label_with_dollar_sign() {
        let result = Label::new("ax$1");
        assert!(matches!(result, Err(LabelError::DollarSign)));
    }

    #[test]
    fn label_with_invalid_chars() {
        let result = Label::new("ax@1");
        assert!(matches!(result, Err(LabelError::InvalidCharacters(_))));
    }

    #[test]
    fn utf8_label_encoding() {
        let label = Label::new("теорема").unwrap();
        assert_eq!(label.as_str(), "теорема");
        assert_eq!(label.encoded(), "xn--80aja2aiml");
        assert!(label.is_encoded());
    }

    #[test]
    fn punycode_roundtrip() {
        let original = "定理";
        let label = Label::new(original).unwrap();
        let encoded_form = label.encoded();

        let decoded = Label::from_encoded(encoded_form).unwrap();
        assert_eq!(decoded.as_str(), original);
    }

    #[test]
    fn punycode_examples() {
        // Test known punycode examples from RFC 3492
        let test_cases = vec![
            ("München", "xn--Mnchen-3ya"),
            ("日本", "xn--wgv71a"),
            ("한국", "xn--3e0b707e"),
        ];

        for (original, expected_encoded) in test_cases {
            let label = Label::new(original).unwrap();
            // Note: our implementation is case-insensitive in encoding
            assert_eq!(
                label.encoded().to_lowercase(),
                expected_encoded.to_lowercase()
            );

            // Test round-trip
            let decoded = Label::from_encoded(label.encoded()).unwrap();
            assert_eq!(decoded.as_str(), original);
        }
    }

    #[test]
    fn mixed_ascii_unicode() {
        let label = Label::new("test日本").unwrap();
        assert_eq!(label.as_str(), "test日本");
        assert!(label.encoded().starts_with("xn--"));
        assert!(label.is_encoded());

        // Verify round-trip
        let decoded = Label::from_encoded(label.encoded()).unwrap();
        assert_eq!(decoded.as_str(), "test日本");
    }
}
