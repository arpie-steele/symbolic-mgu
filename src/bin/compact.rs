//! Compact proof processor for symbolic-mgu.
//!
//! This binary processes compact proof strings using the standard
//! propositional calculus axioms (Simp, Frege, Transp) and Modus Ponens.
//!
//! # Usage
//!
//! ```bash
//! # Process a compact proof
//! cargo run --bin compact -- "DD211"
//!
//! # Process multiple proofs
//! cargo run --bin compact -- "D__" "DD211" "DD2D111"
//!
//! # Verify tautology
//! cargo run --bin compact -- --verify "DD211"
//! ```

use symbolic_mgu::{
    logic::create_dict, test_tautology, EnumTermFactory, MetaByteFactory, MguError, NodeByte,
    SimpleType, Statement, Term, TermFactory, TypeCore,
};

/// Check if a statement with hypotheses is valid.
///
/// Builds the nested implication H₁ → (H₂ → (... → (Hₙ → A))) and tests if it's a tautology.
/// This checks **validity**: whether the conclusion logically follows from the premises.
fn check_validity(
    statement: &Statement<
        SimpleType,
        symbolic_mgu::MetaByte,
        NodeByte,
        symbolic_mgu::EnumTerm<SimpleType, symbolic_mgu::MetaByte, NodeByte>,
    >,
    term_factory: &EnumTermFactory<SimpleType, symbolic_mgu::MetaByte, NodeByte>,
) -> Result<bool, MguError> {
    // Check if all hypotheses and assertion are Boolean
    if !statement.get_assertion().get_type()?.is_boolean() {
        return Err(MguError::UnificationFailure(
            "Assertion is not Boolean type".to_string(),
        ));
    }

    for hyp in statement.get_hypotheses() {
        if !hyp.get_type()?.is_boolean() {
            return Err(MguError::UnificationFailure(
                "Not all hypotheses are Boolean type".to_string(),
            ));
        }
    }

    // Build nested implication: H₁ → (H₂ → (... → (Hₙ → A)))
    let mut implication = statement.get_assertion().clone();

    // Build from right to left (innermost to outermost)
    for hyp in statement.get_hypotheses().iter().rev() {
        implication =
            term_factory.create_node(NodeByte::Implies, vec![hyp.clone(), implication])?;
    }

    // Test if the nested implication is a tautology
    test_tautology(&implication)
}

fn main() {
    if let Err(e) = run() {
        eprintln!("Error: {}", e);
        std::process::exit(1);
    }
}

fn run() -> Result<(), MguError> {
    let args: Vec<String> = std::env::args().collect();

    if args.len() < 2 {
        print_usage(&args[0]);
        return Ok(());
    }

    // Parse arguments
    let mut verify = false;
    let mut proofs = Vec::new();

    for arg in args.iter().skip(1) {
        match arg.as_str() {
            "--help" | "-h" => {
                print_usage(&args[0]);
                return Ok(());
            }
            "--verify" | "-v" => {
                verify = true;
            }
            proof => {
                proofs.push(proof);
            }
        }
    }

    if proofs.is_empty() {
        eprintln!("No proof strings provided.");
        print_usage(&args[0]);
        return Ok(());
    }

    // Create factories
    let var_factory = MetaByteFactory();
    let term_factory = EnumTermFactory::new();

    // Create standard dictionary
    let dict = create_dict(
        &term_factory,
        &var_factory,
        NodeByte::Implies,
        NodeByte::Not,
    )?;

    println!("Compact Proof Processor");
    println!("=======================\n");
    println!("Dictionary:");
    println!("  D = Modus Ponens: (ψ; φ, (φ → ψ); ∅)");
    println!("  1 = Simp: ((φ → (ψ → φ)); ∅; ∅)");
    println!("  2 = Frege: (((φ → (ψ → χ)) → ((φ → ψ) → (φ → χ))); ∅; ∅)");
    println!("  3 = Transp: (((¬φ → ¬ψ) → (ψ → φ)); ∅; ∅)");
    println!("  _ = Placeholder (unsatisfied hypothesis)\n");

    // Process each proof
    for (i, proof_str) in proofs.iter().enumerate() {
        println!("Proof {}: \"{}\"", i + 1, proof_str);
        println!("{}", "─".repeat(50));

        match Statement::from_compact_proof(proof_str, &var_factory, &term_factory, &dict) {
            Ok(result) => {
                println!("✓ Parsed successfully");
                println!("  Assertion: {}", result.get_assertion());
                println!("  Hypotheses: {}", result.get_n_hypotheses());

                if result.get_n_hypotheses() > 0 {
                    for (j, hyp) in result.get_hypotheses().iter().enumerate() {
                        println!("    {}: {}", j, hyp);
                    }
                }

                // Verify tautology or validity if requested
                if verify {
                    if result.get_n_hypotheses() == 0 {
                        // No hypotheses: verify assertion is a tautology
                        match test_tautology(result.get_assertion()) {
                            Ok(true) => println!("  ✓ Verified: This is a tautology"),
                            Ok(false) => println!("  ✗ Warning: This is NOT a tautology"),
                            Err(e) => println!("  ? Could not verify: {}", e),
                        }
                    } else {
                        // Has hypotheses: check if all terms are Boolean, then verify validity
                        match check_validity(&result, &term_factory) {
                            Ok(true) => {
                                println!("  ✓ Valid: Hypotheses logically entail the assertion")
                            }
                            Ok(false) => {
                                println!("  ✗ Invalid: Hypotheses do NOT entail the assertion")
                            }
                            Err(e) => println!("  ? Could not verify validity: {}", e),
                        }
                    }
                }
            }
            Err(e) => {
                println!("✗ Parse failed: {}", e);
            }
        }
        println!();
    }

    Ok(())
}

fn print_usage(program: &str) {
    println!("Usage: {} [OPTIONS] <PROOF>...", program);
    println!();
    println!("Process compact proof strings using standard propositional calculus axioms.");
    println!();
    println!("OPTIONS:");
    println!("  -h, --help     Show this help message");
    println!("  -v, --verify   Verify tautologies (theorems) or validity (inferences)");
    println!();
    println!("VERIFICATION:");
    println!("  For theorems (no hypotheses): Checks if assertion is a tautology");
    println!("  For inferences (has hypotheses): Checks if hypotheses entail assertion");
    println!(
        "                                   by verifying H₁ → (H₂ → (... → A)) is a tautology"
    );
    println!();
    println!("EXAMPLES:");
    println!("  {} DD211              # Prove φ → φ", program);
    println!(
        "  {} --verify DD211     # Prove and verify φ → φ is a tautology",
        program
    );
    println!(
        "  {} --verify D__       # Check if modus ponens is valid",
        program
    );
    println!("  {} D__ DD211          # Process multiple proofs", program);
}
