//! Filesystem abstraction for reading Metamath database files.
//!
//! This module provides an abstraction over filesystem operations to support
//! reading from various sources: local filesystem, tarballs, gzip files, URLs, etc.

use std::io::{self, BufRead, BufReader};
use std::path::{Path, PathBuf};

/// Abstraction over filesystem operations for reading Metamath databases.
///
/// This trait allows the parser to work with different sources of Metamath files:
/// - Local filesystem (via `StdFilesystem`)
/// - Compressed archives (tarballs, gzip)
/// - Remote URLs (HTTP/HTTPS)
/// - In-memory buffers (for testing)
///
/// The trait is designed to support `$[` `$]` file inclusion with cycle detection.
///
/// # Design Note
///
/// This trait uses string identifiers rather than `Path`/`PathBuf` because different
/// implementations have different path semantics:
/// - `StdFilesystem` uses OS-specific paths (with platform-specific separators)
/// - URL-based filesystems would use URL syntax (always forward slash)
/// - In-memory filesystems use simple string keys
///
/// The Metamath `$[` `$]` specification doesn't officially support directories,
/// and in practice only simple filenames are used.
pub trait FilesystemProvider {
    /// The type of reader returned when opening a file.
    type Reader: BufRead;

    /// Open a file for reading.
    ///
    /// # Arguments
    /// * `identifier` - A string identifying the file to open. Interpretation depends
    ///   on the implementation (filesystem path, URL, memory key, etc.)
    ///
    /// # Returns
    /// A buffered reader for the file contents, or an error if the file cannot be opened.
    ///
    /// # Errors
    /// Returns an error if the file does not exist or cannot be read.
    fn open(&mut self, identifier: &str) -> io::Result<Self::Reader>;

    /// Resolve an identifier to its canonical form for cycle detection.
    ///
    /// This is used to track which files have already been included via `$[` `$]`
    /// to prevent infinite inclusion loops.
    ///
    /// # Arguments
    /// * `identifier` - The identifier to resolve (may be relative)
    ///
    /// # Returns
    /// A canonical identifier that uniquely identifies this file, or an error if the
    /// identifier cannot be resolved.
    ///
    /// # Errors
    /// Returns an error if the identifier is invalid or cannot be resolved.
    fn resolve_identifier(&self, identifier: &str) -> io::Result<String>;

    /// Check if a file exists.
    ///
    /// # Arguments
    /// * `identifier` - The identifier to check
    ///
    /// # Returns
    /// `true` if the file exists and is readable, `false` otherwise.
    fn exists(&self, identifier: &str) -> bool;
}

/// Standard filesystem implementation using `std::fs`.
///
/// This implementation reads files from the local filesystem using standard
/// Rust I/O operations. It serves as the default implementation and reference
/// for other filesystem providers.
///
/// # Examples
///
/// ```no_run
/// use symbolic_mgu::metamath::{FilesystemProvider, StdFilesystem};
///
/// let mut fs = StdFilesystem::new();
/// let reader = fs.open("database.mm")?;
/// # Ok::<(), std::io::Error>(())
/// ```
#[derive(Debug, Default)]
pub struct StdFilesystem {
    /// Base directory for resolving relative paths.
    /// If None, uses current working directory.
    base_dir: Option<PathBuf>,
}

impl StdFilesystem {
    /// Create a new standard filesystem provider.
    ///
    /// Relative paths will be resolved from the current working directory.
    pub fn new() -> Self {
        Self { base_dir: None }
    }

    /// Create a filesystem provider with a specific base directory.
    ///
    /// Relative paths will be resolved from the given base directory.
    ///
    /// # Arguments
    /// * `base_dir` - The base directory for resolving relative paths
    ///
    /// # Examples
    ///
    /// ```
    /// use symbolic_mgu::metamath::StdFilesystem;
    ///
    /// let fs = StdFilesystem::with_base_dir("/path/to/databases");
    /// ```
    pub fn with_base_dir(base_dir: impl Into<PathBuf>) -> Self {
        Self {
            base_dir: Some(base_dir.into()),
        }
    }

    /// Resolve a path relative to the base directory if set.
    fn resolve_relative(&self, path: &Path) -> PathBuf {
        if path.is_absolute() {
            path.to_path_buf()
        } else if let Some(ref base) = self.base_dir {
            base.join(path)
        } else {
            path.to_path_buf()
        }
    }
}

impl FilesystemProvider for StdFilesystem {
    type Reader = BufReader<std::fs::File>;

    fn open(&mut self, identifier: &str) -> io::Result<Self::Reader> {
        let path = Path::new(identifier);
        let resolved = self.resolve_relative(path);
        let file = std::fs::File::open(resolved)?;
        Ok(BufReader::new(file))
    }

    fn resolve_identifier(&self, identifier: &str) -> io::Result<String> {
        let path = Path::new(identifier);
        let resolved = self.resolve_relative(path);
        // Canonicalize to get absolute path and resolve symlinks
        let canonical = std::fs::canonicalize(resolved)?;
        // Convert back to String for the trait
        canonical
            .to_str()
            .ok_or_else(|| {
                io::Error::new(io::ErrorKind::InvalidData, "Path contains invalid UTF-8")
            })
            .map(String::from)
    }

    fn exists(&self, identifier: &str) -> bool {
        let path = Path::new(identifier);
        let resolved = self.resolve_relative(path);
        resolved.exists()
    }
}

/// In-memory filesystem for testing and demonstrating virtual filesystem support.
///
/// This implementation stores files in a `HashMap` in memory, demonstrating that
/// the `FilesystemProvider` trait can handle non-disk-based storage. This serves as
/// a proof-of-concept for Phase 9 advanced filesystem implementations:
///
/// - **`TarballFilesystem`**: Would load files from a tarball into memory similarly
/// - **`UrlFilesystem`**: Would fetch files from URLs and cache them in memory
/// - **`ZipFilesystem`**: Would extract from zip archives into memory
///
/// # Example
///
/// ```
/// use symbolic_mgu::metamath::{FilesystemProvider, MemoryFilesystem, MetamathDatabase, Parser, TypeMapping};
///
/// let mut fs = MemoryFilesystem::new();
/// fs.add_file("demo.mm", "$c A $.\n".to_string());
///
/// let db = MetamathDatabase::new(TypeMapping::set_mm());
/// let parser = Parser::new(fs, "demo.mm", db).unwrap();
/// let db = parser.parse().unwrap();
/// # Ok::<(), Box<dyn std::error::Error>>(())
/// ```
#[derive(Debug, Default)]
pub struct MemoryFilesystem {
    /// In-memory storage: identifier -> file contents
    files: std::collections::HashMap<String, String>,
    /// Base directory prefix for resolving relative identifiers
    base_dir: String,
}

impl MemoryFilesystem {
    /// Create a new empty in-memory filesystem.
    ///
    /// Files are stored relative to the root directory "/".
    pub fn new() -> Self {
        Self {
            files: std::collections::HashMap::new(),
            base_dir: String::from("/"),
        }
    }

    /// Create a new in-memory filesystem with a specific base directory.
    ///
    /// This allows simulating a virtual directory structure, similar to how
    /// a tarball or URL-based filesystem would present files relative to a base path.
    pub fn with_base_dir(base_dir: impl Into<String>) -> Self {
        Self {
            files: std::collections::HashMap::new(),
            base_dir: base_dir.into(),
        }
    }

    /// Add a file to the in-memory filesystem.
    ///
    /// This simulates loading a file from a tarball, URL, or other source.
    ///
    /// # Arguments
    /// * `identifier` - The identifier where the file should be accessible (relative to `base_dir`)
    /// * `content` - The file contents as a string
    ///
    /// # Example
    ///
    /// ```
    /// use symbolic_mgu::metamath::MemoryFilesystem;
    ///
    /// let mut fs = MemoryFilesystem::new();
    /// fs.add_file("constants.mm", "$c A B C $.".to_string());
    /// fs.add_file("axioms/ax1.mm", "$v x $.\nax1 $a wff x $.".to_string());
    /// ```
    pub fn add_file(&mut self, identifier: &str, content: String) {
        let normalized = self.normalize_identifier(identifier);
        self.files.insert(normalized, content);
    }

    /// Normalize an identifier relative to the base directory.
    ///
    /// This is similar to how `StdFilesystem::resolve_relative` works, but for
    /// virtual identifiers that don't exist on disk.
    fn normalize_identifier(&self, identifier: &str) -> String {
        if identifier.starts_with('/') {
            // Absolute identifier
            identifier.to_string()
        } else if self.base_dir.is_empty() || self.base_dir == "/" {
            // No base or root base - use as-is
            format!("/{}", identifier)
        } else {
            // Join with base directory
            format!("{}/{}", self.base_dir.trim_end_matches('/'), identifier)
        }
    }
}

impl FilesystemProvider for MemoryFilesystem {
    type Reader = BufReader<std::io::Cursor<String>>;

    fn open(&mut self, identifier: &str) -> io::Result<Self::Reader> {
        let normalized = self.normalize_identifier(identifier);
        let content = self.files.get(&normalized).ok_or_else(|| {
            io::Error::new(
                io::ErrorKind::NotFound,
                format!("File not found in memory: {}", normalized),
            )
        })?;

        // Create a Cursor over the string and wrap in `BufReader`
        let cursor = std::io::Cursor::new(content.clone());
        Ok(BufReader::new(cursor))
    }

    fn resolve_identifier(&self, identifier: &str) -> io::Result<String> {
        // For in-memory filesystem, just normalize the identifier
        // (no need to check if it exists for cycle detection purposes)
        Ok(self.normalize_identifier(identifier))
    }

    fn exists(&self, identifier: &str) -> bool {
        let normalized = self.normalize_identifier(identifier);
        self.files.contains_key(&normalized)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::metamath::{Label, MetamathDatabase, Parser, TypeMapping};
    use std::io::Read;

    #[test]
    fn std_filesystem_open() {
        // Use pre-populated fixture file
        let mut fs = StdFilesystem::with_base_dir("tests/fixtures");
        let mut reader = fs.open("fs_test.mm").unwrap();

        let mut contents = String::new();
        reader.read_to_string(&mut contents).unwrap();
        assert!(contents.contains("$c A B $."));
    }

    #[test]
    fn std_filesystem_exists() {
        // Use pre-populated fixture directory
        let fs = StdFilesystem::with_base_dir("tests/fixtures");

        // File exists
        assert!(fs.exists("fs_test.mm"));

        // File doesn't exist
        assert!(!fs.exists("nonexistent_file.mm"));
    }

    #[test]
    fn std_filesystem_resolve_identifier() {
        // Use pre-populated fixture directory
        let fs = StdFilesystem::with_base_dir("tests/fixtures");
        let resolved = fs.resolve_identifier("fs_test.mm").unwrap();

        // Should be absolute path (starts with /)
        assert!(resolved.starts_with('/') || resolved.chars().nth(1) == Some(':'));

        // Should end with the expected path
        assert!(resolved.ends_with("tests/fixtures/fs_test.mm"));
    }

    #[test]
    fn memory_filesystem_basic_operations() {
        let mut fs = MemoryFilesystem::new();

        // Initially no files exist
        assert!(!fs.exists("test.mm"));

        // Add a file
        fs.add_file("test.mm", "$c A B $.".to_string());

        // Now it should exist
        assert!(fs.exists("test.mm"));

        // Can open and read it
        let mut reader = fs.open("test.mm").unwrap();
        let mut contents = String::new();
        reader.read_to_string(&mut contents).unwrap();
        assert_eq!(contents, "$c A B $.");

        // Non-existent file returns error
        assert!(fs.open("nonexistent.mm").is_err());
    }

    #[test]
    fn memory_filesystem_with_base_dir() {
        let mut fs = MemoryFilesystem::with_base_dir("/virtual/base");

        // Add file with relative path
        fs.add_file("subdir/test.mm", "$c X Y $.".to_string());

        // Should be normalized to absolute path
        let resolved = fs.resolve_identifier("subdir/test.mm").unwrap();
        assert_eq!(resolved, "/virtual/base/subdir/test.mm");

        // Can open with relative path
        let mut reader = fs.open("subdir/test.mm").unwrap();
        let mut contents = String::new();
        reader.read_to_string(&mut contents).unwrap();
        assert_eq!(contents, "$c X Y $.");
    }

    #[test]
    fn memory_filesystem_parser_integration() {
        // Create an in-memory Metamath database
        let mut fs = MemoryFilesystem::new();
        fs.add_file(
            "demo.mm",
            r#"$c ( ) -> wff $.
$v ph ps $.
wph $f wff ph $.
wps $f wff ps $.
ax-1 $a wff ( ph -> ( ps -> ph ) ) $.
"#
            .to_string(),
        );

        // Parse it using the virtual filesystem
        let db = MetamathDatabase::new(TypeMapping::set_mm());
        let parser = Parser::new(fs, "demo.mm", db).unwrap();
        let db = parser.parse().unwrap();

        // Verify the database was populated correctly
        let ax1_label = Label::new("ax-1").unwrap();
        assert!(
            db.get_axiom(&ax1_label).is_some(),
            "Axiom ax-1 should exist"
        );

        // Verify constants were declared
        assert!(db.type_mapping().is_boolean("wff"));
    }

    #[test]
    fn memory_filesystem_file_inclusion() {
        // Create a virtual filesystem with file inclusion
        let mut fs = MemoryFilesystem::new();

        // Main file that includes another
        fs.add_file(
            "main.mm",
            r#"$c wff $.
$( Include the variables $)
$[ included.mm $]
ax-test $a wff ph $.
"#
            .to_string(),
        );

        // Included file
        fs.add_file(
            "included.mm",
            r#"$v ph $.
wph $f wff ph $.
"#
            .to_string(),
        );

        // Parse the main file - should automatically include the other
        let db = MetamathDatabase::new(TypeMapping::set_mm());
        let parser = Parser::new(fs, "main.mm", db).unwrap();
        let db = parser.parse().unwrap();

        // Verify constants were declared
        assert!(db.type_mapping().is_boolean("wff"));

        // Check that ax-test from main file exists
        let ax_test_label = Label::new("ax-test").unwrap();
        assert!(
            db.get_axiom(&ax_test_label).is_some(),
            "Axiom ax-test should exist from main file"
        );
    }
}
