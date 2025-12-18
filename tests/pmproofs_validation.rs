//! Integration test for Principia Mathematica proof validation.
//!
//! This test validates subproofs from the PM proof database,
//! verifying that each compact proof string evaluates to a tautology.
//!
//! Without `bigint` feature: validates proofs with ≤7 Boolean variables
//! With `bigint` feature: validates all proofs regardless of size
//!
//! Run with: `cargo test --test pmproofs_validation --ignored --features serde`
//! Full validation: `cargo test --test pmproofs_validation --ignored --features serde,bigint`
//!
//! Note: This test is marked #[ignore] because it takes several seconds
//! to validate all proofs. Use `--ignored` flag to run it explicitly.

#![cfg(feature = "serde")]
use serde_json::Value;
use symbolic_mgu::bool_eval::test_validity;
use symbolic_mgu::logic::create_dict;
use symbolic_mgu::{
    EnumTerm, EnumTermFactory, Metavariable, NodeByte, SimpleType, Statement, WideMetavariable,
    WideMetavariableFactory,
};
use SimpleType::*;

// Type alias for readability
type WideStatement = Statement<
    SimpleType,
    WideMetavariable,
    NodeByte,
    EnumTerm<SimpleType, WideMetavariable, NodeByte>,
>;
type WideTerm = EnumTerm<SimpleType, WideMetavariable, NodeByte>;

/// Count the number of distinct Boolean variables in a statement
fn count_boolean_variables(stmt: &WideStatement) -> usize {
    use std::collections::HashSet;

    let mut vars = HashSet::new();

    // Collect variables from assertion
    collect_vars_from_term(stmt.get_assertion(), &mut vars);

    // Collect variables from all hypotheses
    for hyp in stmt.get_hypotheses() {
        collect_vars_from_term(hyp, &mut vars);
    }

    // Count only Boolean variables
    vars.iter()
        .filter(|v| v.get_type().map(|t| t == Boolean).unwrap_or(false))
        .count()
}

/// Helper to recursively collect variables from a term
fn collect_vars_from_term(term: &WideTerm, vars: &mut std::collections::HashSet<WideMetavariable>) {
    match term {
        EnumTerm::Leaf(v) => {
            vars.insert(*v);
        }
        EnumTerm::NodeOrLeaf(_, children) => {
            for child in children {
                collect_vars_from_term(child, vars);
            }
        }
    }
}

#[test]
#[ignore]
fn all_pm_subproofs_are_tautologies() {
    // Determine variable limit based on feature flags
    #[cfg(feature = "bigint")]
    let max_vars: Option<usize> = None; // Unlimited with bigint

    #[cfg(not(feature = "bigint"))]
    let max_vars: Option<usize> = Some(7); // u128 supports up to 7 variables

    // Read the JSON file from pmproofs_history
    let data = std::fs::read_to_string("pmproofs_history/subproofs.json")
        .expect("Failed to read pmproofs_history/subproofs.json");
    let subproofs: Vec<Value> =
        serde_json::from_str(&data).expect("Failed to parse subproofs.json");

    println!("Validating PM subproofs...");
    if let Some(limit) = max_vars {
        println!("  Variable limit: {} (bigint feature not enabled)", limit);
        println!("  Proofs with >{} variables will be skipped", limit);
    } else {
        println!("  Variable limit: unlimited (bigint feature enabled)");
    }
    println!("  Total subproofs in database: {}", subproofs.len());

    // Set up factories and dictionary using WideMetavariable for unlimited variable space
    let var_factory = WideMetavariableFactory();
    let term_factory = EnumTermFactory::<SimpleType, WideMetavariable, NodeByte>::new();
    let dict = create_dict(
        &term_factory,
        &var_factory,
        NodeByte::Implies,
        NodeByte::Not,
    )
    .expect("Failed to create statement dictionary");

    let mut parse_failures = Vec::new();
    let mut validation_failures = Vec::new();
    let mut not_tautologies = Vec::new();
    let mut skipped_too_large = Vec::new();
    let mut validated_count = 0;

    for (i, entry) in subproofs.iter().enumerate() {
        let subproof = entry["subproof"]
            .as_str()
            .expect("Missing 'subproof' field");

        // Parse the compact proof
        let stmt_result =
            Statement::from_compact_proof(subproof, &var_factory, &term_factory, &dict);

        match stmt_result {
            Ok(stmt) => {
                // Count Boolean variables in this proof
                let var_count = count_boolean_variables(&stmt);

                // Check if we can validate this proof
                if let Some(limit) = max_vars {
                    if var_count > limit {
                        skipped_too_large.push((i, subproof.to_string(), var_count));
                        continue;
                    }
                }

                // Verify it's a tautology
                match test_validity(&stmt, &term_factory, &Some(NodeByte::Implies)) {
                    Ok(true) => {
                        validated_count += 1;
                    }
                    Ok(false) => {
                        not_tautologies.push((i, subproof.to_string(), var_count));
                    }
                    Err(e) => {
                        validation_failures.push((
                            i,
                            subproof.to_string(),
                            var_count,
                            format!("{:?}", e),
                        ));
                    }
                }
            }
            Err(e) => {
                parse_failures.push((i, subproof.to_string(), format!("{:?}", e)));
            }
        }

        // Progress reporting every 100 proofs
        if (i + 1) % 100 == 0 {
            println!("  Processed {}/{} subproofs...", i + 1, subproofs.len());
        }
    }

    // Report results
    println!("\n========================================");
    println!("PM SUBPROOF VALIDATION RESULTS");
    println!("========================================");
    println!("Total subproofs: {}", subproofs.len());
    println!("Parse failures: {}", parse_failures.len());
    println!("Skipped (too many variables): {}", skipped_too_large.len());
    println!("Validation errors: {}", validation_failures.len());
    println!("Not tautologies: {}", not_tautologies.len());
    println!("Successfully validated: {}", validated_count);

    // Show details of failures
    if !parse_failures.is_empty() {
        println!("\nPARSE FAILURES:");
        for (i, proof, error) in parse_failures.iter().take(10) {
            println!("  #{}: {} - {}", i, proof, error);
        }
        if parse_failures.len() > 10 {
            println!("  ... and {} more", parse_failures.len() - 10);
        }
    }

    if !skipped_too_large.is_empty() {
        println!("\nSKIPPED (TOO MANY VARIABLES):");
        let max_skipped = skipped_too_large
            .iter()
            .map(|(_, _, count)| count)
            .max()
            .unwrap();
        println!("  Count: {}", skipped_too_large.len());
        println!("  Maximum variables in skipped proofs: {}", max_skipped);
        if let Some(limit) = max_vars {
            println!(
                "  Hint: Run with --features bigint to validate proofs with >{} variables",
                limit
            );
        }
        // Show first few examples
        for (i, proof, count) in skipped_too_large.iter().take(5) {
            println!("  #{}: {} ({} vars)", i, proof, count);
        }
        if skipped_too_large.len() > 5 {
            println!("  ... and {} more", skipped_too_large.len() - 5);
        }
    }

    if !validation_failures.is_empty() {
        println!("\nVALIDATION ERRORS:");
        for (i, proof, var_count, error) in validation_failures.iter().take(10) {
            println!("  #{}: {} ({} vars) - {}", i, proof, var_count, error);
        }
        if validation_failures.len() > 10 {
            println!("  ... and {} more", validation_failures.len() - 10);
        }
    }

    if !not_tautologies.is_empty() {
        println!("\nNOT TAUTOLOGIES:");
        for (i, proof, var_count) in not_tautologies.iter().take(10) {
            println!("  #{}: {} ({} vars)", i, proof, var_count);
        }
        if not_tautologies.len() > 10 {
            println!("  ... and {} more", not_tautologies.len() - 10);
        }
    }

    // Fail the test if any failures occurred (but skipped proofs are OK)
    assert!(
        parse_failures.is_empty() && validation_failures.is_empty() && not_tautologies.is_empty(),
        "PM subproof validation failed: {} parse failures, {} validation errors, {} non-tautologies",
        parse_failures.len(),
        validation_failures.len(),
        not_tautologies.len()
    );

    println!("\n✓ Successfully validated {} subproofs!", validated_count);
    if !skipped_too_large.is_empty() {
        println!(
            "  ({} skipped due to variable limit)",
            skipped_too_large.len()
        );
    }
}
