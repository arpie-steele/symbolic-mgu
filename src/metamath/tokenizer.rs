//! Tokenizer for Metamath database files.
//!
//! This module provides tokenization of Metamath source files, handling:
//! - Keyword recognition (`$c`, `$v`, `$f`, `$e`, `$d`, `$a`, `$p`, etc.)
//! - File inclusion via `$[` filename `$]`
//! - Comment skipping/preservation via `$(` ... `$)`
//! - Whitespace handling
//! - Line and column tracking for error reporting
//!
//! # Memory Efficiency
//!
//! Token values use `Arc<str>` to share string data. This is critical for large
//! files (50+ MB) where keywords and common symbols appear millions of times.

use crate::metamath::filesystem::FilesystemProvider;
use std::collections::{HashSet, VecDeque};
use std::io::{self, BufRead};
use std::sync::Arc;

/// A token in a Metamath source file.
///
/// # Memory Efficiency
///
/// The `value` field uses `Arc<str>` to share string data across tokens.
/// For large files, this dramatically reduces memory usage since keywords
/// and common symbols are repeated millions of times.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Token {
    /// The kind of token.
    pub kind: TokenKind,
    /// The actual text of the token (shared via Rc).
    pub value: Arc<str>,
    /// Line number (1-indexed).
    pub line: usize,
    /// Column number (1-indexed).
    pub column: usize,
}

impl Token {
    /// Create a new token.
    pub fn new(kind: TokenKind, value: impl Into<Arc<str>>, line: usize, column: usize) -> Self {
        Self {
            kind,
            value: value.into(),
            line,
            column,
        }
    }

    /// Create a new token from a string slice.
    pub fn from_str(kind: TokenKind, value: &str, line: usize, column: usize) -> Self {
        Self::new(kind, Arc::from(value), line, column)
    }
}

/// The kind of token found in a Metamath source file.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum TokenKind {
    // Statement keywords
    /// `$c` - Constant declaration
    BeginConstant,
    /// `$v` - Variable declaration
    BeginVariable,
    /// `$f` - Floating hypothesis (variable type declaration)
    BeginFloating,
    /// `$e` - Essential hypothesis
    BeginEssential,
    /// `$d` - Disjoint variable restriction
    BeginDisjoint,
    /// `$a` - Axiom or definition
    BeginAxiom,
    /// `$p` - Theorem (provable assertion)
    BeginTheorem,

    // Delimiters
    /// `${` - Begin scope block
    BeginScope,
    /// `$}` - End scope block
    EndScope,
    /// `$(` - Begin comment
    BeginComment,
    /// `$)` - End comment
    EndComment,
    /// `$[` - Begin file inclusion
    BeginInclusion,
    /// `$]` - End file inclusion
    EndInclusion,
    /// `$.` - End statement
    EndStatement,
    /// `$=` - Begin proof
    BeginProof,

    // Content
    /// A word: label, math symbol, or proof symbol
    Word,

    /// Whitespace (spaces, tabs)
    Whitespace,
    /// Newline (CR, LF, CRLF, or FF)
    Newline,
}

impl TokenKind {
    /// Check if this is a keyword token.
    pub fn is_keyword(self) -> bool {
        !matches!(
            self,
            TokenKind::Word | TokenKind::Whitespace | TokenKind::Newline
        )
    }

    /// Check if this is whitespace.
    pub fn is_whitespace(self) -> bool {
        matches!(self, TokenKind::Whitespace | TokenKind::Newline)
    }

    /// Try to parse a keyword from a string.
    ///
    /// Returns Some(`TokenKind`) if the string is a valid keyword, None otherwise.
    pub fn from_keyword(s: &str) -> Option<Self> {
        match s {
            "$c" => Some(TokenKind::BeginConstant),
            "$v" => Some(TokenKind::BeginVariable),
            "$f" => Some(TokenKind::BeginFloating),
            "$e" => Some(TokenKind::BeginEssential),
            "$d" => Some(TokenKind::BeginDisjoint),
            "$a" => Some(TokenKind::BeginAxiom),
            "$p" => Some(TokenKind::BeginTheorem),
            "${" => Some(TokenKind::BeginScope),
            "$}" => Some(TokenKind::EndScope),
            "$(" => Some(TokenKind::BeginComment),
            "$)" => Some(TokenKind::EndComment),
            "$[" => Some(TokenKind::BeginInclusion),
            "$]" => Some(TokenKind::EndInclusion),
            "$." => Some(TokenKind::EndStatement),
            "$=" => Some(TokenKind::BeginProof),
            _ => None,
        }
    }
}

/// Tokenizer for Metamath source files.
///
/// The tokenizer reads from a stack of files (to handle `$[` `$]` inclusion),
/// tracks line and column positions, and produces a stream of tokens.
///
/// # Memory Efficiency
///
/// Common keywords are cached as `Arc<str>` to avoid repeated allocations.
///
/// # Comment Handling
///
/// Comments are accumulated between `$(` and `$)` tokens and made available
/// via `last_comment()`. The accumulated comment is cleared when:
/// - A new comment starts (`$(`)
/// - A scope ends (`$}`)
/// - The first token after a statement ends (`$.`)
pub struct Tokenizer<F: FilesystemProvider> {
    /// Filesystem provider for reading files.
    filesystem: F,
    /// Stack of file readers (for handling `$[` `$]` inclusion).
    file_stack: Vec<FileReader<F::Reader>>,
    /// Set of already-included files (canonical identifiers) for cycle detection.
    included: HashSet<String>,
    /// Buffer of tokens waiting to be consumed.
    token_buffer: VecDeque<Token>,
    /// Current line number (1-indexed).
    current_line: usize,
    /// Current column number (1-indexed).
    current_column: usize,
    /// Character buffer for current line.
    line_buffer: Vec<char>,
    /// Position in line buffer.
    line_pos: usize,
    /// Cached keyword strings to avoid allocations.
    keyword_cache: KeywordCache,
    /// Last complete comment (available after `$)` until cleared).
    last_comment: Option<String>,
    /// Comment currently being accumulated (between `$(` and `$)`).
    accumulating_comment: Option<String>,
    /// Whether we're currently inside a comment.
    inside_comment: bool,
    /// Flag to clear comment after next token (after `$.`).
    clear_comment_after_next: bool,
}

/// Cache of common keyword strings to reduce allocations.
#[derive(Clone)]
struct KeywordCache {
    /// `$c` - constant declaration
    begin_constant: Arc<str>,
    /// `$v` - variable declaration
    begin_variable: Arc<str>,
    /// `$f` - floating hypothesis
    begin_floating: Arc<str>,
    /// `$e` - essential hypothesis
    begin_essential: Arc<str>,
    /// `$d` - disjoint variable constraint
    begin_disjoint: Arc<str>,
    /// `$a` - axiom
    begin_axiom: Arc<str>,
    /// `$p` - theorem (provable)
    begin_theorem: Arc<str>,
    /// `${` - begin scope
    begin_scope: Arc<str>,
    /// `$}` - end scope
    end_scope: Arc<str>,
    /// `$(` - begin comment
    begin_comment: Arc<str>,
    /// `$)` - end comment
    end_comment: Arc<str>,
    /// `$[` - begin file inclusion
    begin_inclusion: Arc<str>,
    /// `$]` - end file inclusion
    end_inclusion: Arc<str>,
    /// `$.` - end statement
    end_statement: Arc<str>,
    /// `$=` - begin proof
    begin_proof: Arc<str>,
}

impl KeywordCache {
    /// Create a new keyword cache with all common keywords.
    fn new() -> Self {
        Self {
            begin_constant: Arc::from("$c"),
            begin_variable: Arc::from("$v"),
            begin_floating: Arc::from("$f"),
            begin_essential: Arc::from("$e"),
            begin_disjoint: Arc::from("$d"),
            begin_axiom: Arc::from("$a"),
            begin_theorem: Arc::from("$p"),
            begin_scope: Arc::from("${"),
            end_scope: Arc::from("$}"),
            begin_comment: Arc::from("$("),
            end_comment: Arc::from("$)"),
            begin_inclusion: Arc::from("$["),
            end_inclusion: Arc::from("$]"),
            end_statement: Arc::from("$."),
            begin_proof: Arc::from("$="),
        }
    }

    /// Get the cached keyword string for a given token kind.
    fn get(&self, kind: TokenKind) -> Arc<str> {
        match kind {
            TokenKind::BeginConstant => self.begin_constant.clone(),
            TokenKind::BeginVariable => self.begin_variable.clone(),
            TokenKind::BeginFloating => self.begin_floating.clone(),
            TokenKind::BeginEssential => self.begin_essential.clone(),
            TokenKind::BeginDisjoint => self.begin_disjoint.clone(),
            TokenKind::BeginAxiom => self.begin_axiom.clone(),
            TokenKind::BeginTheorem => self.begin_theorem.clone(),
            TokenKind::BeginScope => self.begin_scope.clone(),
            TokenKind::EndScope => self.end_scope.clone(),
            TokenKind::BeginComment => self.begin_comment.clone(),
            TokenKind::EndComment => self.end_comment.clone(),
            TokenKind::BeginInclusion => self.begin_inclusion.clone(),
            TokenKind::EndInclusion => self.end_inclusion.clone(),
            TokenKind::EndStatement => self.end_statement.clone(),
            TokenKind::BeginProof => self.begin_proof.clone(),
            _ => panic!("Not a keyword token: {:?}", kind),
        }
    }
}

/// A file reader with associated path information.
struct FileReader<R: BufRead> {
    /// Buffered reader for the file
    reader: R,
    /// Identifier for the file (for error reporting).
    #[allow(dead_code)]
    identifier: String,
    /// Current line number
    line: usize,
}

impl<F: FilesystemProvider> Tokenizer<F> {
    /// Create a new tokenizer for a file.
    ///
    /// # Arguments
    /// * `filesystem` - The filesystem provider to use
    /// * `identifier` - Identifier for the initial file to read
    ///
    /// # Errors
    /// Returns an error if the file cannot be opened.
    pub fn new(mut filesystem: F, identifier: &str) -> io::Result<Self> {
        let canonical_identifier = filesystem.resolve_identifier(identifier)?;
        let reader = filesystem.open(identifier)?;

        let mut included = HashSet::new();
        included.insert(canonical_identifier.clone());

        Ok(Self {
            filesystem,
            file_stack: vec![FileReader {
                reader,
                identifier: canonical_identifier,
                line: 1,
            }],
            included,
            token_buffer: VecDeque::new(),
            current_line: 1,
            current_column: 1,
            line_buffer: Vec::new(),
            line_pos: 0,
            keyword_cache: KeywordCache::new(),
            last_comment: None,
            accumulating_comment: None,
            inside_comment: false,
            clear_comment_after_next: false,
        })
    }

    /// Read the next token.
    ///
    /// Returns None when end of all files is reached.
    ///
    /// # Errors
    /// Returns an error if file I/O fails.
    pub fn next_token(&mut self) -> io::Result<Option<Token>> {
        // Return buffered tokens first
        if let Some(token) = self.token_buffer.pop_front() {
            return Ok(Some(token));
        }

        // Read more tokens
        self.read_tokens()?;

        Ok(self.token_buffer.pop_front())
    }

    /// Peek at the next token without consuming it.
    ///
    /// # Errors
    ///
    /// Returns an error if file I/O fails.
    pub fn peek_token(&mut self) -> io::Result<Option<&Token>> {
        if self.token_buffer.is_empty() {
            self.read_tokens()?;
        }
        Ok(self.token_buffer.front())
    }

    /// Read tokens from the current file into the buffer.
    fn read_tokens(&mut self) -> io::Result<()> {
        while self.token_buffer.is_empty() && !self.file_stack.is_empty() {
            // Get more characters if needed
            if self.line_pos >= self.line_buffer.len() && !self.read_line()? {
                // End of current file, pop the stack
                self.file_stack.pop();
                if let Some(top) = self.file_stack.last() {
                    self.current_line = top.line;
                    self.current_column = 1;
                    self.line_buffer.clear();
                    self.line_pos = 0;
                }
                continue;
            }

            // Tokenize the current line
            self.tokenize_current_line()?;
        }

        Ok(())
    }

    /// Read a line from the current file.
    ///
    /// Returns false if end of file is reached.
    fn read_line(&mut self) -> io::Result<bool> {
        let Some(ref mut file_reader) = self.file_stack.last_mut() else {
            return Ok(false);
        };

        let mut line = String::new();
        let bytes_read = file_reader.reader.read_line(&mut line)?;

        if bytes_read == 0 {
            return Ok(false);
        }

        file_reader.line += 1;
        self.current_line = file_reader.line;
        self.current_column = 1;
        self.line_buffer = line.chars().collect();
        self.line_pos = 0;

        Ok(true)
    }

    /// Tokenize characters from the current position in the line buffer.
    fn tokenize_current_line(&mut self) -> io::Result<()> {
        while self.line_pos < self.line_buffer.len() {
            let start_col = self.current_column;
            let ch = self.line_buffer[self.line_pos];

            // If inside a comment, accumulate all characters until we see `$)`
            if self.inside_comment {
                // Check for end of comment
                if ch == '$'
                    && self.line_pos + 1 < self.line_buffer.len()
                    && self.line_buffer[self.line_pos + 1] == ')'
                {
                    // Found `$)` - end comment mode and make comment available
                    self.inside_comment = false;
                    self.last_comment = self.accumulating_comment.take();
                    self.line_pos += 2;
                    self.current_column += 2;
                    let value = self.keyword_cache.get(TokenKind::EndComment);
                    self.token_buffer.push_back(Token::new(
                        TokenKind::EndComment,
                        value,
                        self.current_line,
                        start_col,
                    ));
                    continue;
                }

                // Accumulate character into comment being built
                if let Some(ref mut comment) = self.accumulating_comment {
                    comment.push(ch);
                } else {
                    self.accumulating_comment = Some(ch.to_string());
                }
                self.line_pos += 1;
                self.current_column += 1;
                continue;
            }

            // Check for whitespace
            if ch == ' ' || ch == '\t' {
                let ws_start = self.line_pos;
                while self.line_pos < self.line_buffer.len()
                    && matches!(self.line_buffer[self.line_pos], ' ' | '\t')
                {
                    self.line_pos += 1;
                    self.current_column += 1;
                }
                let value: String = self.line_buffer[ws_start..self.line_pos].iter().collect();
                self.token_buffer.push_back(Token::from_str(
                    TokenKind::Whitespace,
                    &value,
                    self.current_line,
                    start_col,
                ));
                continue;
            }

            // Check for newline
            if ch == '\r' || ch == '\n' || ch == '\x0C' {
                let mut value = String::new();
                value.push(ch);
                self.line_pos += 1;

                // Handle CRLF
                if ch == '\r'
                    && self.line_pos < self.line_buffer.len()
                    && self.line_buffer[self.line_pos] == '\n'
                {
                    value.push('\n');
                    self.line_pos += 1;
                }

                self.token_buffer.push_back(Token::from_str(
                    TokenKind::Newline,
                    &value,
                    self.current_line,
                    start_col,
                ));
                self.current_column = 1;
                break; // Move to next line
            }

            // Check for keywords (starting with `$)`
            if ch == '$' && self.line_pos + 1 < self.line_buffer.len() {
                let next_ch = self.line_buffer[self.line_pos + 1];
                let keyword = format!("{}{}", ch, next_ch);

                if let Some(kind) = TokenKind::from_keyword(&keyword) {
                    self.line_pos += 2;
                    self.current_column += 2;

                    // Clear comment if flag is set (first non-whitespace token after `$.`)
                    if self.clear_comment_after_next {
                        self.clear_comment();
                        self.clear_comment_after_next = false;
                    }

                    // Handle comment state transitions
                    match kind {
                        TokenKind::BeginComment => {
                            // Start new comment accumulation
                            self.inside_comment = true;
                            self.accumulating_comment = Some(String::new());
                            // Note: comment was already cleared above if needed
                        }
                        TokenKind::EndScope => {
                            // Clear comment when scope ends
                            self.clear_comment();
                        }
                        TokenKind::EndStatement => {
                            // Mark to clear comment after next non-whitespace token
                            self.clear_comment_after_next = true;
                        }
                        _ => {}
                    }

                    // Use cached keyword string to avoid allocation
                    let value = self.keyword_cache.get(kind);
                    self.token_buffer.push_back(Token::new(
                        kind,
                        value,
                        self.current_line,
                        start_col,
                    ));
                    continue;
                }
            }

            // Read a word (label, symbol, or proof character)
            let word_start = self.line_pos;
            while self.line_pos < self.line_buffer.len() {
                let c = self.line_buffer[self.line_pos];
                if c == ' ' || c == '\t' || c == '\r' || c == '\n' || c == '\x0C' {
                    break;
                }
                self.line_pos += 1;
                self.current_column += 1;
            }

            let value: String = self.line_buffer[word_start..self.line_pos].iter().collect();

            // Clear comment if flag is set (first non-whitespace token after `$.`)
            if self.clear_comment_after_next {
                self.clear_comment();
                self.clear_comment_after_next = false;
            }

            self.token_buffer.push_back(Token::from_str(
                TokenKind::Word,
                &value,
                self.current_line,
                start_col,
            ));
        }

        Ok(())
    }

    /// Get the current line number.
    pub fn line(&self) -> usize {
        self.current_line
    }

    /// Get the current column number.
    pub fn column(&self) -> usize {
        self.current_column
    }

    /// Include a file (handle `$[` filename `$]` directive).
    ///
    /// This pushes a new file onto the file stack. The file will be read
    /// until exhausted, then the tokenizer will resume reading from the
    /// previous file.
    ///
    /// # Arguments
    /// * `path` - Path to the file to include (relative to current directory)
    ///
    /// # Errors
    /// Returns an error if:
    /// - The file cannot be opened
    /// - The file creates a circular inclusion
    pub fn include_file(&mut self, identifier: &str) -> io::Result<()> {
        // Resolve to canonical identifier for cycle detection
        let canonical_identifier = self.filesystem.resolve_identifier(identifier)?;

        // Check for circular inclusion
        if self.included.contains(&canonical_identifier) {
            return Err(io::Error::other(format!(
                "Circular file inclusion detected: {}",
                canonical_identifier
            )));
        }

        // Open the file
        let reader = self.filesystem.open(identifier)?;

        // Add to included set and push onto stack
        self.included.insert(canonical_identifier.clone());
        self.file_stack.push(FileReader {
            reader,
            identifier: canonical_identifier,
            line: 0, // Will be incremented to 1 on first read
        });

        // Reset line buffer for new file
        self.line_buffer.clear();
        self.line_pos = 0;

        Ok(())
    }

    /// Check if a file has already been included.
    ///
    /// # Errors
    ///
    /// Returns an error if the path cannot be resolved.
    pub fn is_included(&self, identifier: &str) -> io::Result<bool> {
        let canonical_identifier = self.filesystem.resolve_identifier(identifier)?;
        Ok(self.included.contains(&canonical_identifier))
    }

    /// Get the last complete comment text.
    ///
    /// Returns the comment text that was accumulated between the most recent
    /// `$(` and `$)` tokens. This comment is associated with the next labeled
    /// statement (`$a` or `$p`).
    ///
    /// The comment is cleared when:
    /// - A new comment starts (`$(`)
    /// - A scope ends (`$}`)
    /// - The first non-whitespace token after a statement ends (`$.`)
    ///
    /// # Returns
    /// The last complete comment text, or `None` if no comment is available.
    pub fn last_comment(&self) -> Option<&str> {
        self.last_comment.as_deref()
    }

    /// Clear the last comment.
    fn clear_comment(&mut self) {
        self.last_comment = None;
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::metamath::filesystem::StdFilesystem;
    use std::io::Write;

    #[test]
    fn token_kind_from_keyword() {
        assert_eq!(
            TokenKind::from_keyword("$c"),
            Some(TokenKind::BeginConstant)
        );
        assert_eq!(
            TokenKind::from_keyword("$v"),
            Some(TokenKind::BeginVariable)
        );
        assert_eq!(TokenKind::from_keyword("$a"), Some(TokenKind::BeginAxiom));
        assert_eq!(TokenKind::from_keyword("$."), Some(TokenKind::EndStatement));
        assert_eq!(TokenKind::from_keyword("$="), Some(TokenKind::BeginProof));
        assert_eq!(TokenKind::from_keyword("foo"), None);
    }

    #[test]
    fn tokenize_simple() -> io::Result<()> {
        // Use pre-populated fixture file
        let fs = StdFilesystem::with_base_dir("tests/fixtures");
        let mut tokenizer = Tokenizer::new(fs, "simple.mm")?;

        let tokens: Vec<_> = std::iter::from_fn(|| tokenizer.next_token().transpose())
            .collect::<Result<Vec<_>, _>>()?;

        // Filter out whitespace for easier testing
        let tokens: Vec<_> = tokens
            .into_iter()
            .filter(|t| !t.kind.is_whitespace())
            .collect();

        assert_eq!(tokens.len(), 4);
        assert_eq!(tokens[0].kind, TokenKind::BeginConstant);
        assert_eq!(tokens[1].kind, TokenKind::Word);
        assert_eq!(tokens[1].value.as_ref(), "A");
        assert_eq!(tokens[2].kind, TokenKind::Word);
        assert_eq!(tokens[2].value.as_ref(), "B");
        assert_eq!(tokens[3].kind, TokenKind::EndStatement);

        Ok(())
    }

    #[test]
    fn tokenize_multiple_lines() -> io::Result<()> {
        // Use pre-populated fixture file
        let fs = StdFilesystem::with_base_dir("tests/fixtures");
        let mut tokenizer = Tokenizer::new(fs, "multiline.mm")?;

        let tokens: Vec<_> = std::iter::from_fn(|| tokenizer.next_token().transpose())
            .collect::<Result<Vec<_>, _>>()?
            .into_iter()
            .filter(|t| !t.kind.is_whitespace())
            .collect();

        assert_eq!(tokens.len(), 6);
        assert_eq!(tokens[0].kind, TokenKind::BeginConstant);
        assert_eq!(tokens[3].kind, TokenKind::BeginVariable);

        Ok(())
    }

    #[test]
    fn file_inclusion() -> io::Result<()> {
        let temp_dir = std::env::temp_dir();
        let main_file = temp_dir.join("test_tokenize_main.mm");
        let included_file = temp_dir.join("test_tokenize_included.mm");

        // Create included file
        {
            let mut file = std::fs::File::create(&included_file)?;
            writeln!(file, "$c INCLUDED $.")?;
        }

        // Create main file with inclusion directive
        {
            let mut file = std::fs::File::create(&main_file)?;
            writeln!(file, "$c MAIN $.")?;
            writeln!(file, "$[ test_tokenize_included.mm $]")?;
            writeln!(file, "$c AFTER $.")?;
        }

        let fs = StdFilesystem::with_base_dir(&temp_dir);
        let mut tokenizer = Tokenizer::new(fs, "test_tokenize_main.mm")?;

        // Manually trigger inclusion when we see `$[`
        let mut all_words = Vec::new();
        while let Some(token) = tokenizer.next_token()? {
            if token.kind == TokenKind::BeginInclusion {
                // Skip whitespace and read filename
                let mut filename_token;
                loop {
                    filename_token = tokenizer.next_token()?.unwrap();
                    if !filename_token.kind.is_whitespace() {
                        break;
                    }
                }
                assert_eq!(filename_token.kind, TokenKind::Word);

                // Skip whitespace and read `$]`
                let mut end_token;
                loop {
                    end_token = tokenizer.next_token()?.unwrap();
                    if !end_token.kind.is_whitespace() {
                        break;
                    }
                }
                assert_eq!(end_token.kind, TokenKind::EndInclusion);

                // Include the file
                tokenizer.include_file(filename_token.value.as_ref())?;
            } else if token.kind == TokenKind::Word {
                all_words.push(token.value);
            }
        }

        // Should have: MAIN, INCLUDED, AFTER
        let expected: Vec<Arc<str>> =
            vec![Arc::from("MAIN"), Arc::from("INCLUDED"), Arc::from("AFTER")];
        assert_eq!(all_words, expected);

        // Cleanup
        std::fs::remove_file(&main_file)?;
        std::fs::remove_file(&included_file)?;
        Ok(())
    }

    #[test]
    fn circular_inclusion_detection() -> io::Result<()> {
        let temp_dir = std::env::temp_dir();
        let file_a = temp_dir.join("test_tokenize_circular_a.mm");
        let file_b = temp_dir.join("test_tokenize_circular_b.mm");

        // Create `file_a` that includes `file_b`
        {
            let mut file = std::fs::File::create(&file_a)?;
            writeln!(file, "$[ test_tokenize_circular_b.mm $]")?;
        }

        // Create `file_b` that includes `file_a` (circular!)
        {
            let mut file = std::fs::File::create(&file_b)?;
            writeln!(file, "$[ test_tokenize_circular_a.mm $]")?;
        }

        let fs = StdFilesystem::with_base_dir(&temp_dir);
        let mut tokenizer = Tokenizer::new(fs, "test_tokenize_circular_a.mm")?;

        // Helper to skip whitespace
        let skip_ws = |tokenizer: &mut Tokenizer<StdFilesystem>| -> io::Result<Token> {
            loop {
                let token = tokenizer.next_token()?.unwrap();
                if !token.kind.is_whitespace() {
                    return Ok(token);
                }
            }
        };

        // Read first `$[` and filename
        skip_ws(&mut tokenizer)?; // `$[`
        let filename = skip_ws(&mut tokenizer)?;
        skip_ws(&mut tokenizer)?; // `$]`

        // Include `file_b`
        tokenizer.include_file(filename.value.as_ref())?;

        // Now in `file_b`, try to include `file_a` again
        skip_ws(&mut tokenizer)?; // `$[`
        let filename2 = skip_ws(&mut tokenizer)?;
        skip_ws(&mut tokenizer)?; // `$]`

        // This should fail with circular inclusion error
        let result = tokenizer.include_file(filename2.value.as_ref());
        assert!(result.is_err());
        assert!(result.unwrap_err().to_string().contains("Circular"));

        // Cleanup
        std::fs::remove_file(&file_a)?;
        std::fs::remove_file(&file_b)?;
        Ok(())
    }

    #[test]
    fn realistic_metamath_snippet() -> io::Result<()> {
        // Use pre-populated fixture file
        let fs = StdFilesystem::with_base_dir("tests/fixtures");
        let mut tokenizer = Tokenizer::new(fs, "realistic.mm")?;

        // Collect all non-whitespace tokens
        let mut tokens = Vec::new();
        while let Some(token) = tokenizer.next_token()? {
            if !token.kind.is_whitespace() {
                tokens.push((token.kind, token.value));
            }
        }

        // Verify we got the expected structure
        // Should see: `BeginComment`, ..., `EndComment`, `BeginConstant`, ..., `EndStatement`, etc.
        assert!(tokens.iter().any(|(k, _)| *k == TokenKind::BeginComment));
        assert!(tokens.iter().any(|(k, _)| *k == TokenKind::EndComment));
        assert!(tokens.iter().any(|(k, _)| *k == TokenKind::BeginConstant));
        assert!(tokens.iter().any(|(k, _)| *k == TokenKind::BeginVariable));
        assert!(tokens.iter().any(|(k, _)| *k == TokenKind::BeginScope));
        assert!(tokens.iter().any(|(k, _)| *k == TokenKind::EndScope));
        assert!(tokens.iter().any(|(k, _)| *k == TokenKind::BeginFloating));
        assert!(tokens.iter().any(|(k, _)| *k == TokenKind::BeginAxiom));

        // Check for specific words
        let words: Vec<_> = tokens
            .iter()
            .filter(|(k, _)| *k == TokenKind::Word)
            .map(|(_, v)| v.as_ref())
            .collect();

        assert!(words.contains(&"wff"));
        assert!(words.contains(&"ph"));
        assert!(words.contains(&"ps"));
        assert!(words.contains(&"ax-1"));

        Ok(())
    }

    #[test]
    fn comment_accumulation() -> io::Result<()> {
        // Use pre-populated fixture file
        let fs = StdFilesystem::with_base_dir("tests/fixtures");
        let mut tokenizer = Tokenizer::new(fs, "comments.mm")?;

        // Read until we find the first comment
        while let Some(token) = tokenizer.next_token()? {
            if token.kind == TokenKind::BeginComment {
                break;
            }
        }

        // After `EndComment`, the comment should be accumulated
        while let Some(token) = tokenizer.next_token()? {
            if token.kind == TokenKind::EndComment {
                break;
            }
        }

        let comment1 = tokenizer.last_comment().expect("Should have comment");
        assert_eq!(comment1.trim(), "This is a comment");

        // Read until second comment
        while let Some(token) = tokenizer.next_token()? {
            if token.kind == TokenKind::EndComment {
                break;
            }
        }

        let comment2 = tokenizer
            .last_comment()
            .expect("Should have second comment");
        assert!(comment2.contains("Multi-line"));
        assert!(comment2.contains("comment"));

        // Read until after first `$.`
        while let Some(token) = tokenizer.next_token()? {
            if token.kind == TokenKind::EndStatement {
                break;
            }
        }

        // The comment from before the axiom should still be available here
        // (it gets cleared on the first non-whitespace token AFTER `$.`)
        assert!(tokenizer.last_comment().is_some());

        // Read until we see the theorem label
        while let Some(token) = tokenizer.next_token()? {
            if token.kind == TokenKind::Word && token.value.as_ref() == "thm" {
                break;
            }
        }

        // By now, we've read the `BeginComment` (which cleared the old comment),
        // accumulated the new comment, read `EndComment` (which made it available),
        // and then read `"thm"`. So we should have the NEW comment
        let comment3 = tokenizer
            .last_comment()
            .expect("Should have new comment for theorem");
        assert!(comment3.contains("Comment before theorem"));

        Ok(())
    }

    #[test]
    fn utf8_label_tokenization() -> io::Result<()> {
        use crate::metamath::label::Label;

        // Use pre-populated fixture file
        let fs = StdFilesystem::with_base_dir("tests/fixtures");
        let mut tokenizer = Tokenizer::new(fs, "utf8_labels.mm")?;

        // Collect all word tokens
        let mut words = Vec::new();
        while let Some(token) = tokenizer.next_token()? {
            if token.kind == TokenKind::Word {
                words.push(token.value);
            }
        }

        // Should find the punycode-encoded labels
        let label1_encoded = Label::new("теорема").unwrap().encoded().to_string();
        let label2_encoded = Label::new("定理").unwrap().encoded().to_string();

        assert!(words.iter().any(|w| w.as_ref() == label1_encoded.as_str()));
        assert!(words.iter().any(|w| w.as_ref() == label2_encoded.as_str()));

        // Verify we can decode them
        let label1_decoded = Label::from_encoded(&label1_encoded).unwrap();
        let label2_decoded = Label::from_encoded(&label2_encoded).unwrap();
        assert_eq!(label1_decoded.as_str(), "теорема");
        assert_eq!(label2_decoded.as_str(), "定理");

        Ok(())
    }
}
