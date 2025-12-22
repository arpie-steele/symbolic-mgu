//! Proof representation and parsing for Metamath databases.
//!
//! Supports both expanded and compressed proof formats:
//! - **Expanded**: Direct sequence of labels (theorem/axiom/hypothesis references)
//! - **Compressed**: Parenthesized label list + encoded proof string using A-Z notation
//!
//! Compressed proof encoding (per Metamath specification):
//! - Codes have the format: `[U-Y]*[A-T]` (zero or more U-Y, then exactly one A-T)
//! - A-T terminates the code and contributes 0-19
//! - Each U-Y contributes (1-5) × (place value), where place values are 20, 100, 500, ...
//! - Z alone is the "save to stack" operation (not part of a number)
//! - Examples: `A` =0, `T` = 19, `UA` = 20, `UT` = 39, `VA` = 40, `YA` = 100, `UUA` = 120, `UYA` = 200, `VUA` = 220
//!
//! # Example
//!
//! ```
//! # use symbolic_mgu::metamath::Proof;
//! # use std::sync::Arc;
//! // Expanded proof
//! let expanded = Proof::Expanded(vec![
//!     Arc::from("ax-mp"),
//!     Arc::from("ax-1"),
//! ]);
//!
//! // Compressed proof: ( ax-mp ax-1 ) ABC $.
//! let compressed = Proof::Compressed {
//!     labels: vec![Arc::from("ax-mp"), Arc::from("ax-1")],
//!     proof_string: "ABC".to_string(),
//! };
//!
//! // Both can be iterated
//! for label in expanded.iter(&[]) {
//!     println!("Step: {}", label.as_ref());
//! }
//! ```

use crate::metamath::label::Label;
use std::sync::Arc;
use thiserror::Error;

/// Errors that can occur during proof parsing or iteration.
#[derive(Debug, Error, Clone, PartialEq, Eq)]
pub enum ProofError {
    /// Empty proof when one was expected.
    #[error("empty proof at line {line}")]
    EmptyProof {
        /// Line number
        line: usize,
    },

    /// Invalid compressed proof encoding.
    #[error("invalid compressed proof encoding '{code}' at position {position}")]
    InvalidEncoding {
        /// The invalid encoding character
        code: String,
        /// Position in the proof string
        position: usize,
    },

    /// Reference to non-existent label.
    #[error("proof references non-existent label '{label}' at line {line}")]
    UndefinedLabel {
        /// The undefined label
        label: String,
        /// Line number
        line: usize,
    },

    /// Self-referential proof (theorem references itself).
    #[error("proof contains self-reference to '{label}' at line {line}")]
    SelfReference {
        /// The self-referencing label
        label: String,
        /// Line number
        line: usize,
    },

    /// Malformed compressed proof (missing parentheses, etc.).
    #[error("malformed compressed proof at line {line}: {details}")]
    MalformedCompressed {
        /// Line number
        line: usize,
        /// Details about the error
        details: String,
    },

    /// Proof step index out of bounds.
    #[error("proof step index {index} out of bounds (max {max})")]
    IndexOutOfBounds {
        /// The invalid index
        index: usize,
        /// Maximum valid index
        max: usize,
    },
}

/// Represents a Metamath proof in either expanded or compressed format.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Proof {
    /// Expanded proof: sequence of labels (theorem/axiom/hypothesis references).
    Expanded(Vec<Arc<str>>),

    /// Compressed proof: label list + encoded proof string.
    ///
    /// The proof string uses A-Z encoding where:
    /// - A-T: Mandatory hypotheses (first 20)
    /// - U-Y: Special markers
    /// - AA-ZZ: References to the label list
    Compressed {
        /// Labels referenced in the proof (from parenthesized list).
        labels: Vec<Arc<str>>,
        /// The compressed proof string (A-Z, AA-ZZ encoding).
        proof_string: String,
    },
}

impl Proof {
    /// Returns an iterator over proof steps (labels).
    ///
    /// For compressed proofs, the iterator decodes the proof string on-the-fly.
    ///
    /// # Arguments
    ///
    /// * `mandatory_hyps` - Mandatory hypotheses for this theorem (for A-T decoding)
    ///
    /// # TODO
    ///
    /// Complete mandatory hypothesis handling. Currently this is a stub
    /// that provides the infrastructure. Full hypothesis collection and ordering
    /// according to Metamath specification needs to be implemented during
    /// proof verification (Architecture Phase 7).
    pub fn iter<'a>(&'a self, mandatory_hyps: &'a [Arc<str>]) -> ProofIterator<'a> {
        match self {
            Proof::Expanded(labels) => ProofIterator::Expanded(labels.iter()),
            Proof::Compressed {
                labels,
                proof_string,
            } => ProofIterator::Compressed(CompressedProofIterator {
                labels,
                proof_string,
                position: 0,
                mandatory_hyps,
            }),
        }
    }

    /// Parse a proof from a sequence of tokens (between `$=` and `$.`).
    ///
    /// Automatically detects expanded vs compressed format:
    /// - Compressed: Starts with '(' and contains ')'
    /// - Expanded: All other cases
    ///
    /// # Arguments
    ///
    /// * `tokens` - Token strings from the proof section
    /// * `theorem_label` - Label of the theorem being proven (for self-reference check)
    /// * `label_validator` - Function to check if a label exists in the database
    /// * `line` - Line number for error reporting
    ///
    /// # Errors
    ///
    /// Returns an error if the proof is empty, malformed, references undefined labels,
    /// or contains a self-reference.
    pub fn parse<F>(
        tokens: &[String],
        theorem_label: &Label,
        label_validator: F,
        line: usize,
    ) -> Result<Self, ProofError>
    where
        F: Fn(&str) -> bool,
    {
        if tokens.is_empty() {
            return Err(ProofError::EmptyProof { line });
        }

        // Check if this is a compressed proof (starts with '(')
        if tokens[0] == "(" {
            Self::parse_compressed(tokens, theorem_label, label_validator, line)
        } else {
            Self::parse_expanded(tokens, theorem_label, label_validator, line)
        }
    }

    /// Parse an expanded proof (sequence of labels).
    fn parse_expanded<F>(
        tokens: &[String],
        theorem_label: &Label,
        label_validator: F,
        line: usize,
    ) -> Result<Self, ProofError>
    where
        F: Fn(&str) -> bool,
    {
        let mut labels = Vec::with_capacity(tokens.len());

        for token in tokens {
            // Check for self-reference
            if token == theorem_label.encoded() {
                return Err(ProofError::SelfReference {
                    label: token.clone(),
                    line,
                });
            }

            // Validate label exists in database
            if !label_validator(token) {
                return Err(ProofError::UndefinedLabel {
                    label: token.clone(),
                    line,
                });
            }

            labels.push(Arc::from(token.as_str()));
        }

        Ok(Proof::Expanded(labels))
    }

    /// Parse a compressed proof: `( label1 label2 ... ) PROOF_STRING`
    fn parse_compressed<F>(
        tokens: &[String],
        theorem_label: &Label,
        label_validator: F,
        line: usize,
    ) -> Result<Self, ProofError>
    where
        F: Fn(&str) -> bool,
    {
        // Find the closing parenthesis
        let close_paren_pos = tokens.iter().position(|t| t == ")").ok_or_else(|| {
            ProofError::MalformedCompressed {
                line,
                details: "missing closing parenthesis for label list".to_string(),
            }
        })?;

        // Extract label list (between '(' and ')')
        let label_tokens = &tokens[1..close_paren_pos];
        let mut labels = Vec::with_capacity(label_tokens.len());

        for token in label_tokens {
            // Check for self-reference
            if token == theorem_label.encoded() {
                return Err(ProofError::SelfReference {
                    label: token.clone(),
                    line,
                });
            }

            // Validate label exists in database
            if !label_validator(token) {
                return Err(ProofError::UndefinedLabel {
                    label: token.clone(),
                    line,
                });
            }

            labels.push(Arc::from(token.as_str()));
        }

        // Extract proof string (everything after ')')
        let proof_string_tokens = &tokens[close_paren_pos + 1..];
        if proof_string_tokens.is_empty() {
            return Err(ProofError::MalformedCompressed {
                line,
                details: "missing proof string after label list".to_string(),
            });
        }

        // Join proof string tokens (in case they were separated by whitespace)
        let proof_string = proof_string_tokens.join("");

        Ok(Proof::Compressed {
            labels,
            proof_string,
        })
    }
}

/// Iterator over proof steps.
///
/// Yields labels (`&Arc<str>`) representing each proof step.
pub enum ProofIterator<'a> {
    /// Iterator over expanded proof labels.
    Expanded(std::slice::Iter<'a, Arc<str>>),
    /// Iterator that decodes compressed proof on-the-fly.
    Compressed(CompressedProofIterator<'a>),
}

impl<'a> Iterator for ProofIterator<'a> {
    type Item = &'a Arc<str>;

    fn next(&mut self) -> Option<Self::Item> {
        match self {
            ProofIterator::Expanded(iter) => iter.next(),
            ProofIterator::Compressed(iter) => iter.next(),
        }
    }
}

/// Iterator for compressed proofs that decodes the proof string on-the-fly.
///
/// Implements the Metamath compressed proof mixed radix encoding:
/// - Codes: `[U-Y]*[A-T]` format (zero or more U-Y, terminated by A-T)
/// - A-T contributes 0-19 (ones place)
/// - U-Y contributes (1-5) × (place value), where place values are 20, 100, 500, ...
/// - Z is the "save to stack" operation (skipped during iteration)
/// - Decoded numbers index into: `mandatory_hypotheses` ++ `label_list`
pub struct CompressedProofIterator<'a> {
    /// Label list from the compressed proof.
    labels: &'a [Arc<str>],
    /// Compressed proof string.
    proof_string: &'a str,
    /// Current position in the proof string.
    position: usize,
    /// Mandatory hypotheses (for A-T decoding).
    ///
    /// TODO: This needs proper population from theorem hypotheses
    /// in the correct order (floating + essential) during proof verification
    /// (Architecture Phase 7).
    mandatory_hyps: &'a [Arc<str>],
}

impl<'a> Iterator for CompressedProofIterator<'a> {
    type Item = &'a Arc<str>;

    fn next(&mut self) -> Option<Self::Item> {
        let bytes = self.proof_string.as_bytes();

        loop {
            // Skip whitespace
            while self.position < bytes.len() && bytes[self.position].is_ascii_whitespace() {
                self.position += 1;
            }

            if self.position >= bytes.len() {
                return None;
            }

            // Accumulate U-Y characters (higher-order digits)
            let mut uy_chars = Vec::new();
            while self.position < bytes.len() {
                let ch = bytes[self.position] as char;
                if ('U'..='Y').contains(&ch) {
                    uy_chars.push(ch);
                    self.position += 1;
                } else {
                    break;
                }
            }

            if self.position >= bytes.len() {
                return None;
            }

            let ch = bytes[self.position] as char;
            self.position += 1;

            if ('A'..='T').contains(&ch) {
                // Decode [U-Y]*[A-T] as a mixed radix number
                // A-T contributes 0-19 (ones place)
                // Each U-Y contributes (1-5) × (place value)
                // Place values: 20, 100, 500, 2500, ... (× 5 for each position leftward)

                let mut number = (ch as u8 - b'A') as usize; // 0-19

                // Add contributions from U-Y digits (process right-to-left)
                // Use saturating arithmetic to prevent overflow from malicious input
                let mut place_value = 20usize;
                for &uy_char in uy_chars.iter().rev() {
                    let digit_value = (uy_char as u8 - b'U' + 1) as usize; // 1-5
                    number = number.saturating_add(digit_value.saturating_mul(place_value));
                    place_value = place_value.saturating_mul(5);
                }

                // Look up in combined list: `mandatory_hyps` followed by labels
                if number < self.mandatory_hyps.len() {
                    return Some(&self.mandatory_hyps[number]);
                } else {
                    let label_index = number - self.mandatory_hyps.len();
                    return self.labels.get(label_index);
                }
            } else if ch == 'Z' {
                // Z is the "save to stack" operation
                // For current proof parsing, we skip this
                // Proof verification (Architecture Phase 7) will implement full stack operations
                continue;
            } else {
                // Invalid character - skip and continue
                continue;
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn is_valid(label: &str) -> bool {
        matches!(label, "ax-mp" | "ax-1" | "ax-2" | "th1")
    }

    #[test]
    fn parse_expanded_proof() -> Result<(), ProofError> {
        let tokens = vec!["ax-mp".to_string(), "ax-1".to_string()];
        let theorem_label = Label::from_encoded("th1").unwrap();

        let proof = Proof::parse(&tokens, &theorem_label, is_valid, 1)?;

        match proof {
            Proof::Expanded(labels) => {
                assert_eq!(labels.len(), 2);
                assert_eq!(labels[0].as_ref(), "ax-mp");
                assert_eq!(labels[1].as_ref(), "ax-1");
            }
            _ => panic!("Expected expanded proof"),
        }

        Ok(())
    }

    #[test]
    fn parse_compressed_proof() -> Result<(), ProofError> {
        let tokens = vec![
            "(".to_string(),
            "ax-mp".to_string(),
            "ax-1".to_string(),
            ")".to_string(),
            "ABC".to_string(),
        ];
        let theorem_label = Label::from_encoded("th1").unwrap();

        let proof = Proof::parse(&tokens, &theorem_label, is_valid, 1)?;

        match proof {
            Proof::Compressed {
                labels,
                proof_string,
            } => {
                assert_eq!(labels.len(), 2);
                assert_eq!(labels[0].as_ref(), "ax-mp");
                assert_eq!(labels[1].as_ref(), "ax-1");
                assert_eq!(proof_string, "ABC");
            }
            _ => panic!("Expected compressed proof"),
        }

        Ok(())
    }

    #[test]
    fn reject_self_reference() {
        let tokens = vec!["ax-mp".to_string(), "th1".to_string()];
        let theorem_label = Label::from_encoded("th1").unwrap();

        let result = Proof::parse(&tokens, &theorem_label, is_valid, 1);

        assert!(matches!(result, Err(ProofError::SelfReference { .. })));
    }

    #[test]
    fn reject_undefined_label() {
        let tokens = vec!["ax-mp".to_string(), "undefined".to_string()];
        let theorem_label = Label::from_encoded("th1").unwrap();

        let result = Proof::parse(&tokens, &theorem_label, is_valid, 1);

        assert!(matches!(result, Err(ProofError::UndefinedLabel { .. })));
    }

    #[test]
    fn expanded_proof_iterator() -> Result<(), ProofError> {
        let proof = Proof::Expanded(vec![Arc::from("ax-mp"), Arc::from("ax-1")]);

        let labels: Vec<_> = proof.iter(&[]).map(|r| r.as_ref()).collect();

        assert_eq!(labels, vec!["ax-mp", "ax-1"]);
        Ok(())
    }

    #[test]
    fn compressed_proof_iterator_basic() -> Result<(), ProofError> {
        // Test basic A-T codes (0-19)
        let mandatory_hyps = vec![
            Arc::from("hyp0"),
            Arc::from("hyp1"),
            Arc::from("hyp2"),
            Arc::from("hyp19"),
        ];

        let proof = Proof::Compressed {
            labels: vec![],
            proof_string: "ABC".to_string(), // A=0, B=1, C=2
        };

        let labels: Vec<_> = proof.iter(&mandatory_hyps).map(|r| r.as_ref()).collect();
        assert_eq!(labels, vec!["hyp0", "hyp1", "hyp2"]);
        Ok(())
    }

    #[test]
    fn compressed_proof_iterator_with_uy_prefix() -> Result<(), ProofError> {
        // Test `[U-Y]*[A-T]` mixed radix encoding
        // `UA` = 20, `VA` = 40, `WA` = 60, `YA` = 100
        let mut hyps = Vec::new();
        for i in 0..70 {
            hyps.push(Arc::from(format!("hyp{}", i)));
        }

        let proof = Proof::Compressed {
            labels: vec![],
            proof_string: "UAVAWA".to_string(), // `UA` = 20, `VA` = 40, `WA` = 60
        };

        let labels: Vec<_> = proof.iter(&hyps).map(|r| r.as_ref()).collect();
        assert_eq!(labels, vec!["hyp20", "hyp40", "hyp60"]);
        Ok(())
    }

    #[test]
    fn compressed_proof_iterator_multi_uy() -> Result<(), ProofError> {
        // Test multiple `U..=Y` prefixes: `UUA` = 120, `VUA` = 220
        let mut hyps = Vec::new();
        for i in 0..250 {
            hyps.push(Arc::from(format!("hyp{}", i)));
        }

        let proof = Proof::Compressed {
            labels: vec![],
            proof_string: "UUAVUA".to_string(), // `UUA` = 120, `VUA` = 220
        };

        let labels: Vec<_> = proof.iter(&hyps).map(|r| r.as_ref()).collect();
        assert_eq!(labels, vec!["hyp120", "hyp220"]);
        Ok(())
    }

    #[test]
    fn compressed_proof_with_labels() -> Result<(), ProofError> {
        // Test that numbers beyond hypotheses reference the label list
        let mandatory_hyps = vec![Arc::from("hyp0"), Arc::from("hyp1")];
        let labels = vec![Arc::from("ax-mp"), Arc::from("ax-1")];

        let proof = Proof::Compressed {
            labels,
            proof_string: "ABC".to_string(), // `A` = `hyp0`, `B` = `hyp1`, `C` = `ax-mp` (index 2)
        };

        let result: Vec<_> = proof.iter(&mandatory_hyps).map(|r| r.as_ref()).collect();
        assert_eq!(result, vec!["hyp0", "hyp1", "ax-mp"]);
        Ok(())
    }

    #[test]
    fn compressed_proof_with_z() -> Result<(), ProofError> {
        // Test that Z is skipped (save to stack operation)
        let mandatory_hyps = vec![Arc::from("hyp0"), Arc::from("hyp1"), Arc::from("hyp2")];

        let proof = Proof::Compressed {
            labels: vec![],
            proof_string: "AZBZC".to_string(), // A, Z (skip), B, Z (skip), C
        };

        let labels: Vec<_> = proof.iter(&mandatory_hyps).map(|r| r.as_ref()).collect();
        assert_eq!(labels, vec!["hyp0", "hyp1", "hyp2"]);
        Ok(())
    }

    #[test]
    fn compressed_proof_mixed_radix_examples() -> Result<(), ProofError> {
        // Test the specific examples:
        // `A` = 0, `T` = 19, `UA` = 20, `UT` = 39, `VA` = 40, `YA` = 100, `UUA` = 120, `UYA` = 200, `VUA` = 220
        let mut all_refs = Vec::new();
        for i in 0..250 {
            all_refs.push(Arc::from(format!("ref{}", i)));
        }

        let proof = Proof::Compressed {
            labels: vec![],
            proof_string: "ATUAUTVAYAUUAUYAVUA".to_string(),
        };

        let result: Vec<_> = proof.iter(&all_refs).map(|r| r.as_ref()).collect();
        assert_eq!(
            result,
            vec![
                "ref0", "ref19", "ref20", "ref39", "ref40", "ref100", "ref120", "ref200", "ref220"
            ]
        );
        Ok(())
    }
}
