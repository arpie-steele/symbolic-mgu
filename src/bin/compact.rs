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
    get_formatter, logic::create_dict, test_tautology, EnumTermFactory, MetaByte, MetaByteFactory,
    Metavariable, MetavariableFactory, MguError, MguErrorType, Node, NodeByte, SimpleType,
    Statement, Term, TermFactory, Type, WideMetavariable, WideMetavariableFactory,
};

/// Check if a statement with possible hypotheses is valid.
///
/// Builds the nested implication H₁ → (H₂ → (... → (Hₙ → A))) and tests if it's a tautology.
/// This checks **validity**: whether the conclusion logically follows from the premises.
///
/// This still can work if `implies_node` is `None` when there are zero hypotheses,
/// but in general it should be a Boolean operator with semantics identical to material implication.
fn check_validity<Ty, V, N, T, TF>(
    statement: &Statement<Ty, V, N, TF::Term>,
    term_factory: &TF,
    implies_node: &Option<N>,
) -> Result<bool, MguError>
where
    Ty: Type,
    V: Metavariable<Type = Ty>,
    N: Node<Type = Ty>,
    T: Term<Ty, V, N>,
    TF: TermFactory<T, Ty, V, N, TermNode = N>,
{
    use MguErrorType::VerificationFailure;
    // Check if all hypotheses and assertion are Boolean
    if !statement.get_assertion().get_type()?.is_boolean() {
        return Err(MguError::from_err_type_and_message(
            VerificationFailure,
            "Assertion is not Boolean type",
        ));
    }

    for hyp in statement.get_hypotheses() {
        if !hyp.get_type()?.is_boolean() {
            return Err(MguError::from_err_type_and_message(
                VerificationFailure,
                "Not all hypotheses are Boolean type",
            ));
        }
    }

    // Build nested implication: H₁ → (H₂ → (... → (Hₙ → A)))
    let mut implication = statement.get_assertion().clone();

    // Build from right to left (innermost to outermost), but usually order does not matter.
    for hyp in statement.get_hypotheses().iter().rev() {
        if let Some(actual_implies) = implies_node {
            implication =
                term_factory.create_node(actual_implies.clone(), vec![hyp.clone(), implication])?;
        } else {
            return Err(MguError::from_err_type_and_message(
            VerificationFailure,
                "Unable to produce a single-term Statement without being supplied an implication Node."
                ));
        }
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
    let mut short_vars: Option<bool> = None;
    let mut format = "utf8"; // Default format
    let mut skip_next = false;

    for (idx, arg) in args.iter().skip(1).enumerate() {
        if skip_next {
            skip_next = false;
            continue;
        }

        match arg.as_str() {
            "--help" | "-h" => {
                print_usage(&args[0]);
                return Ok(());
            }
            "--verify" | "-v" => {
                verify = true;
            }
            "--format" | "-f" => {
                // Get next argument as format name
                if let Some(fmt) = args.get(idx + 2) {
                    format = fmt.as_str();
                    skip_next = true;
                } else {
                    return Err(MguError::from_err_type_and_message(
                        MguErrorType::ArgumentError,
                        "--format requires a format name (ascii, utf8, utf8-color, latex, html, html-color)",
                    ));
                }
            }
            "--no-byte" | "--wide" | "-w" => {
                let goal = Some(false);
                if short_vars.is_some() && short_vars != goal {
                    return Err(MguError::from_err_type_and_message(
                        MguErrorType::ArgumentError,
                        "The --wide and --byte flags may not be used together.",
                    ));
                }
                short_vars = goal;
            }
            "--byte" | "--no-wide" | "-b" => {
                let goal = Some(true);
                if short_vars.is_some() && short_vars != goal {
                    return Err(MguError::from_err_type_and_message(
                        MguErrorType::ArgumentError,
                        "The --wide and --byte flags may not be used together.",
                    ));
                }
                short_vars = goal;
            }
            proof => {
                proofs.push(proof);
            }
        }
    }
    let short_vars = short_vars.unwrap_or(true);

    if proofs.is_empty() {
        eprintln!("No proof strings provided.");
        print_usage(&args[0]);
        return Ok(());
    }

    // Create factory
    if short_vars {
        let var_factory = MetaByteFactory();
        run_by_factory::<MetaByte, MetaByteFactory>(&var_factory, &proofs, verify, format)?;
    } else {
        let var_factory = WideMetavariableFactory();
        run_by_factory::<WideMetavariable, WideMetavariableFactory>(&var_factory, &proofs, verify, format)?;
    }

    Ok(())
}

fn run_by_factory<V, VF>(
    var_factory: &VF,
    proofs: &[&str],
    verify: bool,
    format: &str,
) -> Result<(), MguError>
where
    V: Metavariable<Type = SimpleType> + Default,
    VF: MetavariableFactory<MetavariableType = SimpleType, Metavariable = V>,
{
    let term_factory: EnumTermFactory<SimpleType, V, NodeByte> = EnumTermFactory::new();

    // Create standard dictionary
    let dict = create_dict(&term_factory, var_factory, NodeByte::Implies, NodeByte::Not)?;

    // Get formatter
    let formatter = get_formatter(format);

    println!("Compact Proof Processor");
    println!("=======================");
    println!("Format: {}\n", format);
    println!("Dictionary:");
    println!("  D = Modus Ponens: (ψ; φ, (φ → ψ); ∅)");
    println!("  1 = Simp: ((φ → (ψ → φ)); ∅; ∅)");
    println!("  2 = Frege: (((φ → (ψ → χ)) → ((φ → ψ) → (φ → χ))); ∅; ∅)");
    println!("  3 = Transp: (((¬φ → ¬ψ) → (ψ → φ)); ∅; ∅)");
    println!("  _ = Placeholder (unsatisfied hypothesis)\n");

    // Process each proof
    for (i, proof_str) in proofs.iter().copied().enumerate() {
        println!("Proof {}: \"{}\"", i + 1, proof_str);
        println!("{}", "─".repeat(50));

        match Statement::from_compact_proof(proof_str, var_factory, &term_factory, &dict) {
            Ok(result) => {
                println!("✓ Parsed successfully");
                println!(
                    "  Assertion: {}",
                    result.get_assertion().format_with(&*formatter)
                );
                println!("  Hypotheses: {}", result.get_n_hypotheses());

                if result.get_n_hypotheses() > 0 {
                    for (j, hyp) in result.get_hypotheses().iter().enumerate() {
                        println!("    {}: {}", j, hyp.format_with(&*formatter));
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
                        match check_validity(&result, &term_factory, &Some(NodeByte::Implies)) {
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
    println!("  -h, --help              Show this help message");
    println!("  -b, --byte              Use a small subset of ASCII letters for variables");
    println!("  -w, --wide              Use a large library of UTF-8 symbols for variables");
    println!("  -v, --verify            Verify tautologies (theorems) or validity (inferences)");
    println!("  -f, --format <FORMAT>   Output format (default: utf8)");
    println!();
    println!("FORMATS:");
    println!("  ascii        ASCII operators (->, /\\, \\/, -.)");
    println!("  utf8         Unicode operators (→, ∧, ∨, ¬)");
    println!("  utf8-color   Unicode with ANSI terminal colors");
    println!("  latex        LaTeX math mode (\\to, \\land, \\lor, \\neg)");
    println!("  html         HTML with Unicode symbols");
    println!("  html-color   HTML with inline color styles");
    println!();
    println!("VERIFICATION:");
    println!("  For theorems (no hypotheses): Checks if assertion is a tautology");
    println!("  For inferences (has hypotheses): Checks if hypotheses entail assertion");
    println!(
        "                                   by verifying H₁ → (H₂ → (... → A)) is a tautology"
    );
    println!();
    println!("EXAMPLES:");
    println!("  {} DD211                        # Prove φ → φ", program);
    println!(
        "  {} --verify DD211               # Prove and verify φ → φ is a tautology",
        program
    );
    println!(
        "  {} --format ascii DD211         # Display using ASCII operators",
        program
    );
    println!(
        "  {} --format utf8-color DD211    # Display with colors",
        program
    );
    println!(
        "  {} --format latex --verify DD211  # LaTeX output with verification",
        program
    );
    println!(
        "  {} --verify D__                 # Check if modus ponens is valid",
        program
    );
    println!("  {} D__ DD211          # Process multiple proofs", program);
}
