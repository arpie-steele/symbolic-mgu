//! Verify all theorems in a Metamath database.
//!
//! This example demonstrates how to:
//! 1. Parse a Metamath database file
//! 2. Verify all theorems in the database
//! 3. Report verification results
//!
//! # Usage
//!
//! ```bash
//! cargo run --example verify_database tests/metamath-exe/demo0.mm
//! ```
//!
//! For larger databases like set.mm, use release mode for better performance:
//!
//! ```bash
//! cargo run --release --example verify_database tests/metamath-test/set.mm
//! ```

use std::env;
use std::path::Path;
use std::process;
use std::time::Instant;
use symbolic_mgu::metamath::{
    verify_theorem, MetamathDatabase, Parser, StdFilesystem, TypeMapping,
};

fn main() {
    // Get database filename from command line
    let args: Vec<String> = env::args().collect();
    if args.len() != 2 {
        eprintln!("Usage: {} <database-file>", args[0]);
        eprintln!();
        eprintln!("Examples:");
        eprintln!("  {} tests/metamath-exe/demo0.mm", args[0]);
        eprintln!("  {} tests/metamath-test/set.mm", args[0]);
        process::exit(1);
    }

    let filename = &args[1];
    let path = Path::new(filename);

    // Check if file exists
    if !path.exists() {
        eprintln!("Error: File '{}' not found", filename);
        process::exit(1);
    }

    println!("Parsing {}...", filename);
    let parse_start = Instant::now();

    // Parse the database
    // Use the directory of the main file as the base directory for resolving includes
    let base_dir = path.parent().unwrap_or_else(|| Path::new("."));
    let file_name = path
        .file_name()
        .and_then(|n| n.to_str())
        .unwrap_or(filename);
    let fs = StdFilesystem::with_base_dir(base_dir);
    let db = MetamathDatabase::new(TypeMapping::set_mm());
    let parser = match Parser::new(fs, file_name, db) {
        Ok(p) => p,
        Err(e) => {
            eprintln!("Error creating parser: {:?}", e);
            process::exit(1);
        }
    };

    let db = match parser.parse() {
        Ok(db) => db,
        Err(e) => {
            eprintln!("Parse error: {:?}", e);
            process::exit(1);
        }
    };

    let parse_duration = parse_start.elapsed();
    println!("Parsed in {:.2}s", parse_duration.as_secs_f64());

    // Get all theorems
    let theorems = db.theorems();
    let total_theorems = theorems.len();

    if total_theorems == 0 {
        println!("No theorems found in database.");
        return;
    }

    println!("Verifying {} theorems...", total_theorems);
    let verify_start = Instant::now();

    let mut success_count = 0;
    let mut failure_count = 0;
    let mut first_failures = Vec::new();

    for (label, theorem) in theorems.iter() {
        match verify_theorem(theorem, &db) {
            Ok(()) => {
                success_count += 1;
            }
            Err(e) => {
                failure_count += 1;
                if first_failures.len() < 5 {
                    first_failures.push((label.to_string(), e.to_string()));
                }
            }
        }
    }

    let verify_duration = verify_start.elapsed();

    // Report results
    println!();
    println!("========================================");
    println!("Verification Results");
    println!("========================================");
    println!("Total theorems:  {}", total_theorems);
    println!("Verified:        {}", success_count);
    println!("Failed:          {}", failure_count);
    println!("Time:            {:.2}s", verify_duration.as_secs_f64());
    println!(
        "Average:         {:.2}ms/theorem",
        verify_duration.as_secs_f64() * 1000.0 / total_theorems as f64
    );

    if !first_failures.is_empty() {
        println!();
        println!("First {} failure(s):", first_failures.len());
        for (label, error) in &first_failures {
            println!("  {}: {}", label, error);
        }
    }

    if failure_count == 0 {
        println!();
        println!("✓ All theorems verified successfully!");
    } else {
        process::exit(1);
    }
}
