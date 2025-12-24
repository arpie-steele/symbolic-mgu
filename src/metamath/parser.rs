//! Parser for Metamath database files.
//!
//! This module connects the tokenizer with the database to parse Metamath
//! statements and populate the database with constants, variables, and
//! their scoping information.

use crate::metamath::{
    AssertionCore, Axiom, CommentMetadata, ConstantInfo, DatabaseError, EssentialHyp,
    FilesystemProvider, FloatingHyp, Label, MetamathDatabase, Proof, ProofError, SyntaxInfo,
    Theorem, Token, TokenKind, Tokenizer, VariableInfo,
};
use std::collections::HashSet;
use std::io;
use std::sync::Arc;
use thiserror::Error;

/// Errors that can occur during parsing.
#[derive(Debug, Error)]
pub enum ParseError {
    /// I/O error from reading files.
    #[error("I/O error: {0}")]
    Io(#[from] io::Error),

    /// Database error (symbol conflicts, scope errors, etc.).
    #[error("Database error: {0}")]
    Database(#[from] DatabaseError),

    /// Proof parsing error.
    #[error("Proof error: {0}")]
    Proof(#[from] ProofError),

    /// Unexpected token encountered.
    #[error("Unexpected token at line {line}, column {column}: expected {expected}, got {got}")]
    UnexpectedToken {
        /// Line number
        line: usize,
        /// Column number
        column: usize,
        /// Expected token description
        expected: String,
        /// Actual token received
        got: String,
    },

    /// Unexpected end of file.
    #[error("Unexpected end of file at line {line}")]
    UnexpectedEof {
        /// Line number where EOF occurred
        line: usize,
    },

    /// Invalid syntax.
    #[error("Invalid syntax at line {line}: {message}")]
    InvalidSyntax {
        /// Line number of the error
        line: usize,
        /// Error message
        message: String,
    },

    /// Variable used without a floating hypothesis (type declaration).
    #[error("Variable '{variable}' used in {context} at line {line} but has no $f (floating hypothesis) declaring its type")]
    MissingFloatingHypothesis {
        /// The variable without a type
        variable: String,
        /// Context (axiom or theorem label)
        context: String,
        /// Line number
        line: usize,
    },
}

/// Parser for Metamath database files.
///
/// The parser consumes tokens from a tokenizer and builds up a database
/// by processing statements in order.
pub struct Parser<F: FilesystemProvider> {
    /// Tokenizer for reading tokens from the input file
    tokenizer: Tokenizer<F>,
    /// Database being constructed
    database: Arc<MetamathDatabase>,
    /// Track current line for error reporting.
    current_line: usize,
}

impl<F: FilesystemProvider> Parser<F> {
    /// Create a new parser for the given file.
    ///
    /// # Errors
    ///
    /// Returns an error if the file cannot be opened or read.
    pub fn new(
        filesystem: F,
        identifier: &str,
        database: MetamathDatabase,
    ) -> Result<Self, ParseError> {
        let tokenizer = Tokenizer::new(filesystem, identifier)?;

        Ok(Self {
            tokenizer,
            database: Arc::new(database),
            current_line: 1,
        })
    }

    /// Parse the entire database.
    ///
    /// Consumes all tokens and returns the populated database.
    ///
    /// # Errors
    ///
    /// Returns an error if parsing fails due to syntax errors, I/O errors, or database errors.
    pub fn parse(mut self) -> Result<Arc<MetamathDatabase>, ParseError> {
        while let Some(token) = self.next_non_whitespace()? {
            self.current_line = token.line;

            match token.kind {
                TokenKind::BeginConstant => self.parse_constant_declaration(&token)?,
                TokenKind::BeginVariable => self.parse_variable_declaration(&token)?,
                TokenKind::BeginDisjoint => self.parse_distinctness_constraint(&token)?,
                TokenKind::BeginScope => self.database.push_scope(),
                TokenKind::EndScope => self.database.pop_scope(token.line)?,
                TokenKind::BeginComment | TokenKind::EndComment => {
                    // Comments already handled by tokenizer
                }
                TokenKind::BeginInclusion => self.parse_file_inclusion(&token)?,
                TokenKind::Word => {
                    // This is a label for a statement (`$f`, `$e`, `$a`, `$p`)
                    self.parse_labeled_statement(token)?;
                }
                _ => {
                    return Err(ParseError::UnexpectedToken {
                        line: token.line,
                        column: token.column,
                        expected: "statement keyword or label".to_string(),
                        got: format!("{:?}", token.kind),
                    });
                }
            }
        }

        Ok(self.database)
    }

    /// Get the next non-whitespace token.
    fn next_non_whitespace(&mut self) -> Result<Option<Token>, ParseError> {
        loop {
            match self.tokenizer.next_token()? {
                None => return Ok(None),
                Some(token) if token.kind.is_whitespace() => continue,
                Some(token) => return Ok(Some(token)),
            }
        }
    }

    /// Parse a file inclusion directive: `$[` filename `$]`
    fn parse_file_inclusion(&mut self, _start_token: &Token) -> Result<(), ParseError> {
        // Read the filename token
        let filename_token = self
            .next_non_whitespace()?
            .ok_or(ParseError::UnexpectedEof {
                line: self.current_line,
            })?;

        if filename_token.kind != TokenKind::Word {
            return Err(ParseError::UnexpectedToken {
                line: filename_token.line,
                column: filename_token.column,
                expected: "filename".to_string(),
                got: format!("{:?}", filename_token.kind),
            });
        }

        // Read the `$]` end token
        let end_token = self
            .next_non_whitespace()?
            .ok_or(ParseError::UnexpectedEof {
                line: self.current_line,
            })?;

        if end_token.kind != TokenKind::EndInclusion {
            return Err(ParseError::UnexpectedToken {
                line: end_token.line,
                column: end_token.column,
                expected: "$]".to_string(),
                got: format!("{:?}", end_token.kind),
            });
        }

        // Include the file (tokenizer handles identifier resolution and cycle detection)
        self.tokenizer.include_file(filename_token.value.as_ref())?;

        Ok(())
    }

    /// Expect a specific token kind.
    #[allow(dead_code)]
    fn expect_token(&mut self, expected: TokenKind) -> Result<Token, ParseError> {
        match self.next_non_whitespace()? {
            None => Err(ParseError::UnexpectedEof {
                line: self.current_line,
            }),
            Some(token) if token.kind == expected => Ok(token),
            Some(token) => Err(ParseError::UnexpectedToken {
                line: token.line,
                column: token.column,
                expected: format!("{:?}", expected),
                got: format!("{:?} ({})", token.kind, token.value),
            }),
        }
    }

    /// Parse a `$c` constant declaration.
    ///
    /// Format: `$c` &lt;symbol&gt;+ `$.`
    fn parse_constant_declaration(&mut self, start_token: &Token) -> Result<(), ParseError> {
        let mut symbols = Vec::new();

        // Read symbols until `$.`, skipping comments
        let mut in_comment = false;
        loop {
            let token = self
                .next_non_whitespace()?
                .ok_or(ParseError::UnexpectedEof {
                    line: self.current_line,
                })?;

            if token.kind == TokenKind::EndStatement {
                break;
            }

            // Skip comment markers and content
            match token.kind {
                TokenKind::BeginComment => {
                    in_comment = true;
                    continue;
                }
                TokenKind::EndComment => {
                    in_comment = false;
                    continue;
                }
                TokenKind::Word => {
                    if !in_comment {
                        symbols.push(token.value);
                    }
                }
                _ => {
                    if !in_comment {
                        return Err(ParseError::UnexpectedToken {
                            line: token.line,
                            column: token.column,
                            expected: "symbol or $.".to_string(),
                            got: format!("{:?}", token.kind),
                        });
                    }
                }
            }
        }

        // Declare each constant
        for symbol in symbols {
            let info = ConstantInfo {
                symbol,
                line: start_token.line,
                arity: None,
                is_type: false, // We'll determine this later from syntax axioms
            };

            self.database.declare_constant(info)?;
        }

        Ok(())
    }

    /// Parse a `$v` variable declaration.
    ///
    /// Format: `$v` &lt;symbol&gt;+ `$.`
    fn parse_variable_declaration(&mut self, start_token: &Token) -> Result<(), ParseError> {
        let mut symbols = Vec::new();

        // Read symbols until `$.`, skipping comments
        let mut in_comment = false;
        loop {
            let token = self
                .next_non_whitespace()?
                .ok_or(ParseError::UnexpectedEof {
                    line: self.current_line,
                })?;

            if token.kind == TokenKind::EndStatement {
                break;
            }

            // Skip comment markers and content
            match token.kind {
                TokenKind::BeginComment => {
                    in_comment = true;
                    continue;
                }
                TokenKind::EndComment => {
                    in_comment = false;
                    continue;
                }
                TokenKind::Word => {
                    if !in_comment {
                        symbols.push(token.value);
                    }
                }
                _ => {
                    if !in_comment {
                        return Err(ParseError::UnexpectedToken {
                            line: token.line,
                            column: token.column,
                            expected: "symbol or $.".to_string(),
                            got: format!("{:?}", token.kind),
                        });
                    }
                }
            }
        }

        // Declare each variable
        for symbol in symbols {
            let info = VariableInfo {
                symbol,
                line: start_token.line,
                type_code: None,
                active: true,
            };

            self.database.declare_variable(info)?;
        }

        Ok(())
    }

    /// Skip tokens until we find `$.`
    #[allow(dead_code)]
    fn skip_until_statement_end(&mut self) -> Result<(), ParseError> {
        loop {
            match self.next_non_whitespace()? {
                None => return Ok(()),
                Some(token) if token.kind == TokenKind::EndStatement => return Ok(()),
                Some(_) => continue,
            }
        }
    }

    /// Parse a distinctness constraint (`$d` statement).
    ///
    /// Format: `$d <variable>+ $.`
    fn parse_distinctness_constraint(&mut self, _start_token: &Token) -> Result<(), ParseError> {
        let mut variables = Vec::new();

        // Read variables until `$.`, skipping comments
        let mut in_comment = false;
        loop {
            let token = self
                .next_non_whitespace()?
                .ok_or(ParseError::UnexpectedEof {
                    line: self.current_line,
                })?;

            if token.kind == TokenKind::EndStatement {
                break;
            }

            // Skip comment markers and content
            match token.kind {
                TokenKind::BeginComment => {
                    in_comment = true;
                    continue;
                }
                TokenKind::EndComment => {
                    in_comment = false;
                    continue;
                }
                TokenKind::Word => {
                    if !in_comment {
                        variables.push(token.value);
                    }
                }
                _ => {
                    if !in_comment {
                        return Err(ParseError::UnexpectedToken {
                            line: token.line,
                            column: token.column,
                            expected: "variable or `$.`".to_string(),
                            got: format!("{:?}", token.kind),
                        });
                    }
                }
            }
        }

        // Add pairwise distinctness constraints
        for i in 0..variables.len() {
            for j in (i + 1)..variables.len() {
                self.database
                    .add_distinctness(variables[i].clone(), variables[j].clone());
            }
        }

        Ok(())
    }

    /// Parse a labeled statement (`$f`, `$e`, `$a`, or `$p`).
    fn parse_labeled_statement(&mut self, label_token: Token) -> Result<(), ParseError> {
        // Parse label
        let label =
            Label::from_encoded(&label_token.value).map_err(|e| ParseError::InvalidSyntax {
                line: label_token.line,
                message: format!("Invalid label: {}", e),
            })?;

        // Get the statement type keyword (it will be a specific token kind)
        let keyword = self
            .next_non_whitespace()?
            .ok_or(ParseError::UnexpectedEof {
                line: self.current_line,
            })?;

        match keyword.kind {
            TokenKind::BeginFloating => self.parse_floating_hyp(label, label_token.line),
            TokenKind::BeginEssential => self.parse_essential_hyp(label, label_token.line),
            TokenKind::BeginAxiom => self.parse_axiom(label, label_token.line),
            TokenKind::BeginTheorem => self.parse_theorem(label, label_token.line),
            _ => Err(ParseError::UnexpectedToken {
                line: keyword.line,
                column: keyword.column,
                expected: "$f, $e, $a, or $p".to_string(),
                got: format!("{:?}", keyword.kind),
            }),
        }
    }

    /// Parse a floating hypothesis.
    ///
    /// Format: `label $f <type-code> <variable> $.`
    fn parse_floating_hyp(&mut self, label: Label, line: usize) -> Result<(), ParseError> {
        // Read type code
        let type_code_token = self.expect_token(TokenKind::Word)?;
        let type_code = type_code_token.value;

        // Read variable
        let var_token = self.expect_token(TokenKind::Word)?;
        let variable = var_token.value;

        // Expect `$.`
        self.expect_token(TokenKind::EndStatement)?;

        let hyp = FloatingHyp {
            label,
            variable: variable.clone(),
            type_code: type_code.clone(),
            line,
        };

        // Register this variable with its type for `MetavariableFactory` support
        self.database
            .register_variable_type(type_code, variable, line)?;

        self.database.add_floating_hyp(hyp)?;
        Ok(())
    }

    /// Parse an essential hypothesis.
    ///
    /// Format: `label $e <symbol>+ $.`
    fn parse_essential_hyp(&mut self, label: Label, line: usize) -> Result<(), ParseError> {
        let mut statement = Vec::new();

        // Read symbols until `$.`, skipping comments
        let mut in_comment = false;
        loop {
            let token = self
                .next_non_whitespace()?
                .ok_or(ParseError::UnexpectedEof {
                    line: self.current_line,
                })?;

            if token.kind == TokenKind::EndStatement {
                break;
            }

            // Skip comment markers and content
            match token.kind {
                TokenKind::BeginComment => {
                    in_comment = true;
                    continue;
                }
                TokenKind::EndComment => {
                    in_comment = false;
                    continue;
                }
                TokenKind::Word => {
                    if !in_comment {
                        statement.push(token.value);
                    }
                }
                _ => {
                    if !in_comment {
                        return Err(ParseError::UnexpectedToken {
                            line: token.line,
                            column: token.column,
                            expected: "symbol or `$.`".to_string(),
                            got: format!("{:?}", token.kind),
                        });
                    }
                }
            }
        }

        let hyp = EssentialHyp {
            label,
            statement,
            line,
        };

        self.database.add_essential_hyp(hyp)?;
        Ok(())
    }

    /// Parse an axiom.
    ///
    /// Format: `label $a <symbol>+ $.`
    fn parse_axiom(&mut self, label: Label, line: usize) -> Result<(), ParseError> {
        let mut statement = Vec::new();

        // Read symbols until `$.`, skipping comments
        let mut in_comment = false;
        loop {
            let token = self
                .next_non_whitespace()?
                .ok_or(ParseError::UnexpectedEof {
                    line: self.current_line,
                })?;

            if token.kind == TokenKind::EndStatement {
                break;
            }

            // Skip comment markers and content
            match token.kind {
                TokenKind::BeginComment => {
                    in_comment = true;
                    continue;
                }
                TokenKind::EndComment => {
                    in_comment = false;
                    continue;
                }
                TokenKind::Word => {
                    if !in_comment {
                        statement.push(token.value);
                    }
                }
                _ => {
                    if !in_comment {
                        return Err(ParseError::UnexpectedToken {
                            line: token.line,
                            column: token.column,
                            expected: "symbol or `$.`".to_string(),
                            got: format!("{:?}", token.kind),
                        });
                    }
                }
            }
        }

        // Get associated comment from tokenizer and parse metadata
        let comment = self.tokenizer.last_comment().map(CommentMetadata::parse);

        // Extract type code (first symbol) and compute syntax info
        let type_code = statement.first().cloned().unwrap_or_else(|| Arc::from(""));

        let active_vars = self.database.active_variables();
        let syntax_info =
            SyntaxInfo::from_statement(&statement, &active_vars, self.database.type_mapping());

        // Collect mandatory hypotheses (only those for variables in the statement)
        let hypotheses = self
            .database
            .current_scope()
            .collect_mandatory_hypotheses(&statement, &active_vars);

        // Validate that every variable in the statement has a floating hypothesis
        let mentioned_vars: HashSet<Arc<str>> = statement
            .iter()
            .filter(|sym| active_vars.contains(*sym))
            .cloned()
            .collect();

        for var in &mentioned_vars {
            let has_floating = hypotheses.0.iter().any(|hyp| &hyp.variable == var);

            if !has_floating {
                return Err(ParseError::MissingFloatingHypothesis {
                    variable: var.to_string(),
                    context: format!("axiom '{}'", label.encoded()),
                    line,
                });
            }
        }

        // Build distinctness graph from ALL active variables in scope
        let distinctness = self
            .database
            .build_distinctness_graph(&active_vars, &self.database);

        let axiom = Axiom {
            core: AssertionCore {
                label,
                statement,
                line,
                hypotheses,
                comment,
                distinctness,
            },
            type_code,
            syntax_info,
        };

        self.database.add_axiom(axiom)?;
        Ok(())
    }

    /// Parse a theorem (with proof placeholder for now).
    ///
    /// Format: `label $p <symbol>+ $= <proof> $.`
    fn parse_theorem(&mut self, label: Label, line: usize) -> Result<(), ParseError> {
        let mut statement = Vec::new();

        // Read symbols until `$=`, skipping comments
        let mut in_comment = false;
        loop {
            let token = self
                .next_non_whitespace()?
                .ok_or(ParseError::UnexpectedEof {
                    line: self.current_line,
                })?;

            if token.kind == TokenKind::BeginProof {
                break;
            }

            // Skip comment markers and content
            match token.kind {
                TokenKind::BeginComment => {
                    in_comment = true;
                    continue;
                }
                TokenKind::EndComment => {
                    in_comment = false;
                    continue;
                }
                TokenKind::Word => {
                    if !in_comment {
                        statement.push(token.value);
                    }
                }
                _ => {
                    if !in_comment {
                        return Err(ParseError::UnexpectedToken {
                            line: token.line,
                            column: token.column,
                            expected: "symbol or `$=`".to_string(),
                            got: format!("{:?}", token.kind),
                        });
                    }
                }
            }
        }

        // Collect mandatory hypotheses (only those for variables in the statement)
        let active_vars = self.database.active_variables();
        let hypotheses = self
            .database
            .current_scope()
            .collect_mandatory_hypotheses(&statement, &active_vars);

        // Validate that every variable in the statement has a floating hypothesis
        let mentioned_vars: HashSet<Arc<str>> = statement
            .iter()
            .filter(|sym| active_vars.contains(*sym))
            .cloned()
            .collect();

        for var in &mentioned_vars {
            let has_floating = hypotheses.0.iter().any(|hyp| &hyp.variable == var);

            if !has_floating {
                return Err(ParseError::MissingFloatingHypothesis {
                    variable: var.to_string(),
                    context: format!("theorem '{}'", label.encoded()),
                    line,
                });
            }
        }

        // Also collect ALL hypotheses in scope (for label lookup in compressed proofs)
        let all_hypotheses = self.database.current_scope().collect_hypotheses();

        // Get mandatory hypothesis labels in declaration order for compressed proof decoding
        let mandatory_hyp_labels = self
            .database
            .current_scope()
            .mandatory_hypothesis_labels(&statement, &active_vars);

        // Parse proof (Phase 5)
        // Read proof tokens until we find `$.`, skipping comments
        let mut proof_tokens = Vec::new();
        let mut in_comment = false;
        loop {
            let token = self
                .next_non_whitespace()?
                .ok_or(ParseError::UnexpectedEof {
                    line: self.current_line,
                })?;

            if token.kind == TokenKind::EndStatement {
                break;
            }

            // Skip comment markers and content
            match token.kind {
                TokenKind::BeginComment => {
                    in_comment = true;
                    continue;
                }
                TokenKind::EndComment => {
                    in_comment = false;
                    continue;
                }
                _ => {
                    // Only collect non-comment tokens
                    if !in_comment {
                        proof_tokens.push(token.value.to_string());
                    }
                }
            }
        }

        // Parse proof using Proof::parse() with label validation
        let proof = if proof_tokens.is_empty() {
            None
        } else {
            let parsed_proof = Proof::parse(
                &proof_tokens,
                &label,
                |lbl| self.database.label_exists(lbl),
                line,
            )?;
            Some(parsed_proof)
        };

        // Get associated comment from tokenizer and parse metadata
        let comment = self.tokenizer.last_comment().map(CommentMetadata::parse);

        // Build distinctness graph from ALL active variables in scope
        // This includes variables that appear only in the proof (not in statement/hypotheses)
        // which is necessary for correct distinctness checking during verification
        let active_vars = self.database.active_variables();
        let distinctness = self
            .database
            .build_distinctness_graph(&active_vars, &self.database);

        let theorem = Theorem {
            core: AssertionCore {
                label,
                statement,
                line,
                hypotheses,
                comment,
                distinctness,
            },
            all_hypotheses,
            mandatory_hyp_labels,
            proof,
        };

        self.database.add_theorem(theorem)?;
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::metamath::{ContributionKind, Proof, StdFilesystem, TypeMapping};
    use std::io::Write;
    use std::sync::Arc;

    #[test]
    fn parse_simple_constants() -> Result<(), Box<dyn std::error::Error>> {
        let temp_dir = std::env::temp_dir();
        let test_file = temp_dir.join("test_parse_constants.mm");

        // Create test file
        {
            let mut file = std::fs::File::create(&test_file)?;
            writeln!(file, "$c wff ( ) -> $.")?;
        }

        // Parse
        let fs = StdFilesystem::with_base_dir(&temp_dir);
        let db = MetamathDatabase::new(TypeMapping::set_mm());
        let parser = Parser::new(fs, "test_parse_constants.mm", db)?;
        let db = parser.parse()?;

        // Verify constants were declared
        assert!(db.type_mapping().is_boolean("wff"));

        // Cleanup
        std::fs::remove_file(&test_file)?;
        Ok(())
    }

    #[test]
    fn parse_variables() -> Result<(), Box<dyn std::error::Error>> {
        let temp_dir = std::env::temp_dir();
        let test_file = temp_dir.join("test_parse_variables.mm");

        {
            let mut file = std::fs::File::create(&test_file)?;
            writeln!(file, "$c wff $.")?;
            writeln!(file, "$v ph ps $.")?;
        }

        let fs = StdFilesystem::with_base_dir(&temp_dir);
        let db = MetamathDatabase::new(TypeMapping::set_mm());
        let parser = Parser::new(fs, "test_parse_variables.mm", db)?;
        let _db = parser.parse()?;

        // Variables should be in the database
        // (We'd need accessor methods to verify this properly)

        std::fs::remove_file(&test_file)?;
        Ok(())
    }

    #[test]
    fn parse_scopes() -> Result<(), Box<dyn std::error::Error>> {
        let temp_dir = std::env::temp_dir();
        let test_file = temp_dir.join("test_parse_scopes.mm");

        {
            let mut file = std::fs::File::create(&test_file)?;
            writeln!(file, "$c wff $.")?;
            writeln!(file, "$v x $.")?;
            writeln!(file, "${{")?;
            writeln!(file, "  $v y $.")?;
            writeln!(file, "$}}")?;
        }

        let fs = StdFilesystem::with_base_dir(&temp_dir);
        let db = MetamathDatabase::new(TypeMapping::set_mm());
        let parser = Parser::new(fs, "test_parse_scopes.mm", db)?;
        let _db = parser.parse()?;

        // Should parse without errors

        std::fs::remove_file(&test_file)?;
        Ok(())
    }

    #[test]
    fn parse_demo0_full() -> Result<(), Box<dyn std::error::Error>> {
        // This test parses the complete `demo0.mm` file and verifies
        // that axioms and theorems are properly stored

        let project_root = std::env::current_dir()?;
        let test_file = project_root.join("tests/metamath-exe/demo0.mm");

        if !test_file.exists() {
            // Skip test if file doesn't exist
            eprintln!("Skipping test: demo0.mm not found");
            return Ok(());
        }

        let fs = StdFilesystem::new();
        let db_config = MetamathDatabase::new(TypeMapping::set_mm());
        let test_file_str = test_file.to_str().ok_or("Invalid path")?;
        let parser = Parser::new(fs, test_file_str, db_config)?;

        let db = parser.parse()?;

        // Verify some axioms were parsed
        let a1_label = Label::new("a1")?;
        assert!(db.get_axiom(&a1_label).is_some(), "Axiom a1 should exist");

        let a2_label = Label::new("a2")?;
        assert!(db.get_axiom(&a2_label).is_some(), "Axiom a2 should exist");

        // Verify theorem was parsed
        let th1_label = Label::new("th1")?;
        let th1 = db.get_theorem(&th1_label);
        assert!(th1.is_some(), "Theorem th1 should exist");

        // Check theorem has a proof (even if just as string for now)
        let th1 = th1.unwrap();
        assert!(th1.proof.is_some(), "Theorem th1 should have proof");

        // Verify theorem statement
        assert!(
            !th1.core.statement.is_empty(),
            "Theorem should have a statement"
        );

        println!("Parsed {} axioms", db.axioms().len());
        println!("Parsed {} theorems", db.theorems().len());

        Ok(())
    }

    #[test]
    fn proof_parsing_integration() -> Result<(), Box<dyn std::error::Error>> {
        // Integration test for Phase 5: parse both expanded and compressed proofs

        let temp_dir = std::env::temp_dir();
        let test_file = temp_dir.join("test_proof_parsing.mm");

        {
            let mut file = std::fs::File::create(&test_file)?;
            writeln!(file, "$( Minimal database with proofs $)")?;
            writeln!(file, "$c wff |- ( ) -> $.")?;
            writeln!(file, "$v ph ps $.")?;
            writeln!(file, "${{")?;
            writeln!(file, "  wph $f wff ph $.")?;
            writeln!(file, "  wps $f wff ps $.")?;
            writeln!(file)?;
            writeln!(file, "  $( Axiom: implication introduction $)")?;
            writeln!(file, "  ax-1 $a |- ( ph -> ( ps -> ph ) ) $.")?;
            writeln!(file)?;
            writeln!(file, "  $( Axiom: implication distribution $)")?;
            writeln!(file, "  ax-2 $a |- ( ( ph -> ( ps -> ph ) ) -> ph ) $.")?;
            writeln!(file)?;
            writeln!(file, "  $( Modus ponens $)")?;
            writeln!(file, "  min $e |- ph $.")?;
            writeln!(file, "  maj $e |- ( ph -> ps ) $.")?;
            writeln!(file, "  ax-mp $a |- ps $.")?;
            writeln!(file)?;
            writeln!(file, "  $( Theorem with expanded proof $)")?;
            writeln!(
                file,
                "  th-exp $p |- ( ph -> ( ps -> ph ) ) $= wph wps ax-1 $."
            )?;
            writeln!(file)?;
            writeln!(file, "  $( Theorem with compressed proof $)")?;
            writeln!(
                file,
                "  th-cmp $p |- ( ph -> ( ps -> ph ) ) $= ( ax-1 ) AB $."
            )?;
            writeln!(file, "$}}")?;
        }

        // Parse the file
        let fs = StdFilesystem::with_base_dir(&temp_dir);
        let db = MetamathDatabase::new(TypeMapping::set_mm());
        let parser = Parser::new(fs, "test_proof_parsing.mm", db)?;
        let db = parser.parse()?;

        // Verify expanded proof
        let th_exp_label = Label::new("th-exp")?;
        let th_exp = db
            .get_theorem(&th_exp_label)
            .expect("th-exp theorem should exist");
        assert!(th_exp.proof.is_some(), "th-exp should have a proof");

        if let Some(Proof::Expanded(labels)) = &th_exp.proof {
            assert_eq!(labels.len(), 3, "Expanded proof should have 3 steps");
            assert_eq!(labels[0].as_ref(), "wph");
            assert_eq!(labels[1].as_ref(), "wps");
            assert_eq!(labels[2].as_ref(), "ax-1");
        } else {
            panic!("th-exp proof should be Expanded");
        }

        // Verify compressed proof
        let th_cmp_label = Label::new("th-cmp")?;
        let th_cmp = db
            .get_theorem(&th_cmp_label)
            .expect("th-cmp theorem should exist");
        assert!(th_cmp.proof.is_some(), "th-cmp should have a proof");

        if let Some(Proof::Compressed {
            labels,
            proof_string,
        }) = &th_cmp.proof
        {
            assert_eq!(labels.len(), 1, "Compressed proof should have 1 label");
            assert_eq!(labels[0].as_ref(), "ax-1");
            assert_eq!(proof_string, "AB", "Proof string should be 'AB'");

            // Test iteration over compressed proof
            let mandatory_hyps = vec![Arc::from("wph"), Arc::from("wps")];
            let proof_steps: Vec<_> = th_cmp
                .proof
                .as_ref()
                .unwrap()
                .iter(&mandatory_hyps)
                .map(|r| r.as_ref())
                .collect();
            assert_eq!(
                proof_steps,
                vec!["wph", "wps"],
                "Compressed proof should decompress to hypotheses"
            );
        } else {
            panic!("th-cmp proof should be Compressed");
        }

        std::fs::remove_file(&test_file)?;
        Ok(())
    }

    #[test]
    fn comment_metadata_extraction() -> Result<(), Box<dyn std::error::Error>> {
        // Integration test: parse a file with contributor comments

        let temp_dir = std::env::temp_dir();
        let test_file = temp_dir.join("test_parse_comments.mm");

        {
            let mut file = std::fs::File::create(&test_file)?;
            writeln!(file, "$c wff |- $.")?;
            writeln!(file, "$v ph ps $.")?;
            writeln!(file, "wph $f wff ph $.")?;
            writeln!(file, "wps $f wff ps $.")?;
            writeln!(file)?;
            writeln!(
                file,
                "  $( Axiom of implication. (Contributed by NM, 5-Aug-1993.) $)"
            )?;
            writeln!(file, "  ax-1 $a |- ( ph -> ps ) $.")?;
            writeln!(file)?;
            writeln!(file, "  $( Double modus ponens.")?;
            writeln!(file, "     (Contributed by Mario Carneiro, 24-Jan-2013.)")?;
            writeln!(
                file,
                "     (Proof shortened by Wolf Lammen, 23-Jul-2013.) $)"
            )?;
            writeln!(file, "  mp2 $a |- ps $.")?;
        }

        let fs = StdFilesystem::with_base_dir(&temp_dir);
        let db = MetamathDatabase::new(TypeMapping::set_mm());
        let parser = Parser::new(fs, "test_parse_comments.mm", db)?;
        let db = parser.parse()?;

        // Check ax-1 comment
        let ax1_label = Label::new("ax-1")?;
        let ax1 = db.get_axiom(&ax1_label).expect("ax-1 should exist");

        assert!(ax1.core.comment.is_some());
        let metadata = ax1.core.comment.as_ref().unwrap();
        assert_eq!(metadata.contributions.len(), 1);
        assert_eq!(metadata.contributions[0].contributor, "NM");
        assert_eq!(metadata.contributions[0].date.year, 1993);
        assert_eq!(
            metadata.contributions[0].kind,
            ContributionKind::Contributed
        );

        // Check `mp2` comment with multiple contributions
        let mp2_label = Label::new("mp2")?;
        let mp2 = db.get_axiom(&mp2_label).expect("mp2 should exist");

        assert!(mp2.core.comment.is_some());
        let metadata = mp2.core.comment.as_ref().unwrap();
        assert_eq!(metadata.contributions.len(), 2);

        // First contribution
        assert_eq!(metadata.contributions[0].contributor, "Mario Carneiro");
        assert_eq!(metadata.contributions[0].date.year, 2013);
        assert_eq!(metadata.contributions[0].date.month.as_number(), 1);
        assert_eq!(
            metadata.contributions[0].kind,
            ContributionKind::Contributed
        );

        // Second contribution
        assert_eq!(metadata.contributions[1].contributor, "Wolf Lammen");
        assert_eq!(metadata.contributions[1].date.day, 23);
        assert_eq!(
            metadata.contributions[1].kind,
            ContributionKind::ProofShortened
        );

        std::fs::remove_file(&test_file)?;
        Ok(())
    }
}
