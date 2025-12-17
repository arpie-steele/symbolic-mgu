//! Metamath database parser with UTF-8 and filesystem abstraction support.
//!
//! This module provides a parser for Metamath databases that:
//! - Relaxes the ASCII-only requirement by supporting UTF-8 in comments and punycode for labels
//! - Abstracts filesystem operations to support reading from various sources
//! - Preserves comment metadata including contributor attributions
//! - Uses crate for proof verification
//!
//! # Example
//!
//! ```no_run
//! use symbolic_mgu::metamath::{MetamathDatabase, Parser, StdFilesystem, TypeMapping};
//!
//! # fn main() -> Result<(), Box<dyn std::error::Error>> {
//! // Parse a Metamath database file
//! let fs = StdFilesystem::new();
//! let db = MetamathDatabase::new(TypeMapping::set_mm());
//! let parser = Parser::new(fs, "set.mm", db)?;
//! let db = parser.parse()?;
//!
//! // Query theorems and axioms
//! // let theorem = db.get_theorem(&label)?;
//! # Ok(())
//! # }
//! ```

pub(crate) mod comment;
pub(crate) mod database;
pub(crate) mod expr_parser;
pub(crate) mod filesystem;
pub(crate) mod label;
pub(crate) mod parser;
pub(crate) mod pattern;
pub(crate) mod proof;
pub(crate) mod symbolic;
pub(crate) mod tokenizer;
pub(crate) mod verification;

pub use comment::CommentError;
pub use comment::CommentMetadata;
pub use comment::Contribution;
pub use comment::ContributionDate;
pub use comment::ContributionKind;
pub use comment::Month;
pub use database::AssertionCore;
pub use database::Axiom;
pub use database::ConstantInfo;
pub use database::DatabaseError;
pub use database::EssentialHyp;
pub use database::FloatingHyp;
pub use database::MetamathDatabase;
pub use database::Scope;
pub use database::SymbolKind;
pub use database::SyntaxInfo;
pub use database::Theorem;
pub use database::TypeMapping;
pub use database::VariableInfo;
pub use expr_parser::parse_expression;
pub use filesystem::FilesystemProvider;
pub use filesystem::MemoryFilesystem;
pub use filesystem::StdFilesystem;
pub use label::Label;
pub use label::LabelError;
pub use parser::ParseError;
pub use parser::Parser;
pub use pattern::PatternElement;
pub use pattern::PatternHints;
pub use pattern::SyntaxAxiomPattern;
pub use proof::CompressedProofIterator;
pub use proof::Proof;
pub use proof::ProofError;
pub use proof::ProofIterator;
pub use symbolic::DbMetavariable;
pub use symbolic::DbMetavariableFactory;
pub use symbolic::DbMetavariableIterator;
pub use symbolic::DbNode;
pub use symbolic::DbTerm;
pub use symbolic::DbType;
pub use tokenizer::Token;
pub use tokenizer::TokenKind;
pub use tokenizer::Tokenizer;
pub use verification::verify_theorem;
pub use verification::DistinctnessViolationDetails;
pub use verification::EssentialMismatchDetails;
pub use verification::FinalStatementMismatchDetails;
pub use verification::StackUnderflowDetails;
pub use verification::VerificationError;
