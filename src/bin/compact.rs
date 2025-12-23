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

use symbolic_mgu::bool_eval::{test_tautology, test_validity};
use symbolic_mgu::logic::create_dict;
use symbolic_mgu::{
    get_formatter, EnumTerm, EnumTermFactory, MetaByte, MetaByteFactory, Metavariable,
    MetavariableFactory, MguError, MguErrorType, NodeByte, NodeByteFactory, OutputFormatter,
    SimpleType, SimpleTypeFactory, Statement, Term, TermFactory, WideMetavariable,
    WideMetavariableFactory,
};

/// Metavariable implementation mode
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum MetavariableMode {
    /// Use MetaByte (limited to 32 variables total)
    Byte,
    /// Use WideMetavariable (unlimited variables)
    Wide,
    /// Parse with WideMetavariable, convert to MetaByte when possible
    Both,
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
    let mut mode: Option<MetavariableMode> = None;
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
                let goal = MetavariableMode::Wide;
                if mode.is_some() && mode != Some(goal) {
                    return Err(MguError::from_err_type_and_message(
                        MguErrorType::ArgumentError,
                        "The --wide, --byte, and --both flags are mutually exclusive.",
                    ));
                }
                mode = Some(goal);
            }
            "--byte" | "--no-wide" | "-b" => {
                let goal = MetavariableMode::Byte;
                if mode.is_some() && mode != Some(goal) {
                    return Err(MguError::from_err_type_and_message(
                        MguErrorType::ArgumentError,
                        "The --wide, --byte, and --both flags are mutually exclusive.",
                    ));
                }
                mode = Some(goal);
            }
            "--both" => {
                let goal = MetavariableMode::Both;
                if mode.is_some() && mode != Some(goal) {
                    return Err(MguError::from_err_type_and_message(
                        MguErrorType::ArgumentError,
                        "The --wide, --byte, and --both flags are mutually exclusive.",
                    ));
                }
                mode = Some(goal);
            }
            proof => {
                proofs.push(proof);
            }
        }
    }
    let mode = mode.unwrap_or(MetavariableMode::Byte);

    if proofs.is_empty() {
        eprintln!("No proof strings provided.");
        print_usage(&args[0]);
        return Ok(());
    }

    // Dispatch based on mode
    match mode {
        MetavariableMode::Byte => {
            let var_factory = MetaByteFactory::new(SimpleTypeFactory);
            run_by_factory::<MetaByte, MetaByteFactory<SimpleTypeFactory>>(
                &var_factory,
                &proofs,
                verify,
                format,
            )?;
        }
        MetavariableMode::Wide => {
            let var_factory = WideMetavariableFactory::new(SimpleTypeFactory);
            run_by_factory::<WideMetavariable, WideMetavariableFactory<SimpleTypeFactory>>(
                &var_factory,
                &proofs,
                verify,
                format,
            )?;
        }
        MetavariableMode::Both => {
            run_both_mode(&proofs, verify, format)?;
        }
    }

    Ok(())
}

/// Run in "both" mode: parse with WideMetavariable, convert to MetaByte when possible
fn run_both_mode(proofs: &[&str], verify: bool, format: &str) -> Result<(), MguError> {
    let wide_var_factory = WideMetavariableFactory::new(SimpleTypeFactory);
    let wide_term_factory: EnumTermFactory<
        SimpleType,
        WideMetavariable,
        NodeByte,
        SimpleTypeFactory,
    > = EnumTermFactory::new(SimpleTypeFactory);

    // Create standard dictionary with WideMetavariable
    let dict = create_dict(
        &wide_term_factory,
        &wide_var_factory,
        NodeByte::Implies,
        NodeByte::Not,
    )?;

    // Get formatter
    let formatter = get_formatter(format);

    println!("Compact Proof Processor (Both Mode)");
    println!("====================================");
    println!("Format: {}", format);
    println!("Mode: Parse with unlimited variables, convert to byte variables when possible\n");
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

        match Statement::from_compact_proof(proof_str, &wide_var_factory, &wide_term_factory, &dict)
        {
            Ok(wide_result) => {
                println!("✓ Parsed successfully (wide variables)");

                // IMPORTANT: Canonicalize the parsed result before conversion or display.
                // This ensures deterministic variable ordering regardless of Rust's randomized
                // hash function, which would otherwise cause the same proof to display
                // differently on each run.
                let canonical_wide =
                    wide_result.canonicalize(&wide_var_factory, &wide_term_factory)?;

                // Try to convert to MetaByte
                let byte_var_factory = MetaByteFactory::new(SimpleTypeFactory);
                let node_factory: NodeByteFactory<SimpleType> = NodeByteFactory::new();
                let byte_term_factory: EnumTermFactory<
                    SimpleType,
                    MetaByte,
                    NodeByte,
                    SimpleTypeFactory,
                > = EnumTermFactory::new(SimpleTypeFactory);

                match canonical_wide.convert::<
                    SimpleType,
                    MetaByte,
                    NodeByte,
                    EnumTerm<SimpleType, MetaByte, NodeByte>,
                    _,
                    _,
                    _,
                    _,
                >(&byte_var_factory, &node_factory, &byte_term_factory)
                {
                    Ok(byte_result) => {
                        println!("✓ Successfully converted to byte variables");
                        // Note: Even though `canonical_wide` was canonical, convert() maps variables
                        // based on the order they're encountered in the source, which may not match
                        // the destination's canonical ordering. Re-canonicalize for consistency.
                        let canonical_byte = byte_result.canonicalize(&byte_var_factory, &byte_term_factory)?;
                        display_statement(&canonical_byte, &*formatter, verify, &byte_term_factory)?;
                    }
                    Err(e) => {
                        println!("⚠ Cannot convert to byte variables: {}", e);
                        println!("  Displaying with wide variables:");
                        display_statement(&canonical_wide, &*formatter, verify, &wide_term_factory)?;
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

/// Display a statement with verification
fn display_statement<V, T, TF>(
    result: &Statement<SimpleType, V, NodeByte, T>,
    formatter: &dyn OutputFormatter,
    verify: bool,
    term_factory: &TF,
) -> Result<(), MguError>
where
    V: Metavariable<Type = SimpleType>,
    T: Term<SimpleType, V, NodeByte>,
    TF: TermFactory<
        T,
        SimpleType,
        V,
        NodeByte,
        SimpleTypeFactory,
        Term = T,
        TermNode = NodeByte,
        TermMetavariable = V,
    >,
{
    println!(
        "  Assertion: {}",
        result.get_assertion().format_with(formatter)
    );
    println!("  Hypotheses: {}", result.get_n_hypotheses());

    if result.get_n_hypotheses() > 0 {
        for (j, hyp) in result.get_hypotheses().iter().enumerate() {
            println!("    {}: {}", j, hyp.format_with(formatter));
        }
    }

    // Verify tautology or validity if requested
    if verify {
        if result.get_n_hypotheses() == 0 {
            // No hypotheses: verify assertion is a tautology
            match test_tautology(term_factory.type_factory(), result.get_assertion()) {
                Ok(true) => println!("  ✓ Verified: This is a tautology"),
                Ok(false) => println!("  ✗ Warning: This is NOT a tautology"),
                Err(e) => println!("  ? Could not verify: {}", e),
            }
        } else {
            // Has hypotheses: check validity
            match test_validity(result, term_factory, &Some(NodeByte::Implies)) {
                Ok(true) => println!("  ✓ Valid: Hypotheses logically entail the assertion"),
                Ok(false) => println!("  ✗ Invalid: Hypotheses do NOT entail the assertion"),
                Err(e) => println!("  ? Could not verify validity: {}", e),
            }
        }
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
    V: Metavariable<Type = SimpleType>,
    VF: MetavariableFactory<SimpleTypeFactory, MetavariableType = SimpleType, Metavariable = V>,
{
    let term_factory: EnumTermFactory<SimpleType, V, NodeByte, SimpleTypeFactory> =
        EnumTermFactory::new(SimpleTypeFactory);

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

                // IMPORTANT: Canonicalize before display to ensure deterministic output.
                // Without canonicalization, variable ordering depends on Rust's randomized
                // hash function, causing the same proof to display differently on each run.
                // Canonicalization produces minimal lexicographic variable ordering and
                // ensures consistent, reproducible output for mathematical results.
                let canonical = result.canonicalize(var_factory, &term_factory)?;

                println!(
                    "  Assertion: {}",
                    canonical.get_assertion().format_with(&*formatter)
                );
                println!("  Hypotheses: {}", canonical.get_n_hypotheses());

                if canonical.get_n_hypotheses() > 0 {
                    for (j, hyp) in canonical.get_hypotheses().iter().enumerate() {
                        println!("    {}: {}", j, hyp.format_with(&*formatter));
                    }
                }

                // Verify tautology or validity if requested
                if verify {
                    if canonical.get_n_hypotheses() == 0 {
                        // No hypotheses: verify assertion is a tautology
                        match test_tautology(term_factory.type_factory(), canonical.get_assertion())
                        {
                            Ok(true) => println!("  ✓ Verified: This is a tautology"),
                            Ok(false) => println!("  ✗ Warning: This is NOT a tautology"),
                            Err(e) => println!("  ? Could not verify: {}", e),
                        }
                    } else {
                        // Has hypotheses: check if all terms are Boolean, then verify validity
                        match test_validity(&canonical, &term_factory, &Some(NodeByte::Implies)) {
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
    println!("      --both              Parse with wide variables, convert to byte when possible");
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
    println!(
        "  {} --both DD211                 # Parse with wide vars, show byte vars if possible",
        program
    );
    println!("  {} D__ DD211          # Process multiple proofs", program);
}
