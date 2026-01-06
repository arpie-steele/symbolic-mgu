use std::sync::Arc;
use std::time::Instant;
use symbolic_mgu::metamath::{
    verify_theorem, MetamathDatabase, Parser, StdFilesystem, TypeMapping,
};

fn main() {
    println!("Parsing set.mm...");
    let parse_start = Instant::now();
    let fs = StdFilesystem::new();
    let db = MetamathDatabase::new(TypeMapping::set_mm());
    let parser =
        Parser::new(fs, "tests/metamath-test/set.mm", db).expect("Failed to create parser");
    let db = Arc::new(parser.parse().expect("Failed to parse set.mm"));
    let parse_time = parse_start.elapsed();

    println!(
        "Database parsed successfully in {:.3}s",
        parse_time.as_secs_f64()
    );
    println!("Verifying theorems...");

    let theorems = db.theorems();
    let total = theorems.len();
    println!("Total theorems: {}", total);

    let limit = std::env::args()
        .nth(1)
        .and_then(|s| s.parse::<usize>().ok())
        .unwrap_or(total);
    println!("Checking first {} theorems", limit.min(total));

    let mut slowest_theorems: Vec<(String, f64)> = Vec::new();
    let verify_start = Instant::now();

    for (i, (label, theorem)) in theorems.iter().take(limit).enumerate() {
        if i % 100 == 0 {
            println!("Progress: {}/{} theorems checked", i, limit.min(total));
        }

        let theorem_start = Instant::now();
        match verify_theorem(theorem, &db) {
            Ok(_) => {
                let theorem_time = theorem_start.elapsed().as_secs_f64();

                // Track slowest theorems
                slowest_theorems.push((label.to_string(), theorem_time));
                slowest_theorems.sort_by(|a, b| b.1.partial_cmp(&a.1).unwrap());
                if slowest_theorems.len() > 10 {
                    slowest_theorems.truncate(10);
                }
            }
            Err(e) => {
                println!("\n=== FIRST FAILING THEOREM ===");
                println!("Theorem: {}", label);
                println!(
                    "Statement: {:?}",
                    theorem
                        .core
                        .statement
                        .iter()
                        .map(|s| s.as_ref())
                        .collect::<Vec<_>>()
                );
                println!("Error: {:?}", e);
                return;
            }
        }
    }

    let verify_time = verify_start.elapsed();
    let avg_time = verify_time.as_secs_f64() / limit.min(total) as f64;

    if limit >= total {
        println!("\nAll {} theorems verified successfully!", total);
    } else {
        println!("\nFirst {} theorems verified successfully!", limit);
    }

    println!("\n=== TIMING STATISTICS ===");
    println!("Parse time: {:.3}s", parse_time.as_secs_f64());
    println!("Verification time: {:.3}s", verify_time.as_secs_f64());
    println!("Average per theorem: {:.3}s", avg_time);
    println!("\nSlowest 10 theorems:");
    for (label, time) in &slowest_theorems {
        println!("  {}: {:.3}s", label, time);
    }
}
