//! Stress test for formatter system with large proofs.
//!
//! This test validates that formatters can handle:
//! - Large numbers of variables (100+)
//! - Deep nesting of terms
//! - All formatter types (ascii, utf8, latex, etc.)

use symbolic_mgu::logic::create_dict;
use symbolic_mgu::{
    get_formatter, EnumTerm, EnumTermFactory, MguError, NodeByte, SimpleType, SimpleTypeFactory,
    Statement, Term, WideMetavariable, WideMetavariableFactory,
};

type WideStatement = Statement<
    SimpleType,
    WideMetavariable,
    NodeByte,
    EnumTerm<SimpleType, WideMetavariable, NodeByte>,
>;

#[test]
fn stress_test_deep_proof_100_plus_variables() -> Result<(), MguError> {
    // Create a very deep proof by prepending D1 many times
    // D1x always has 1 more variable than x, so D1^100 + 1 gives us 100+ variables
    let depth = 100;
    let mut proof = "D1".repeat(depth);
    proof.push('1'); // Final axiom

    println!(
        "Testing proof with depth {}: {} characters",
        depth,
        proof.len()
    );

    // Create factories - must use WideMetavariable since MetaByte maxes out at 11 Boolean vars
    let term_factory = EnumTermFactory::new(SimpleTypeFactory);
    let metavar_factory = WideMetavariableFactory::new(SimpleTypeFactory);

    // Create dictionary
    let dict = create_dict(
        &term_factory,
        &metavar_factory,
        NodeByte::Implies,
        NodeByte::Not,
    )?;

    // Parse the proof
    let result: WideStatement =
        Statement::from_compact_proof(&proof, &metavar_factory, &term_factory, &dict)?;

    // Collect variables to see how many we have
    let vars = result.collect_metavariables()?;
    println!("Proof generated {} unique variables", vars.len());

    // D1 adds one variable per application, so we should have depth + base_vars
    assert!(
        vars.len() > 100,
        "Expected > 100 variables with depth {}, got {}",
        depth,
        vars.len()
    );

    // Test all formatter types
    let formatters = vec!["ascii", "utf8", "latex", "display"];

    for format_name in formatters {
        let formatter = get_formatter(format_name);
        let output = result.get_assertion().format_with(&*formatter);

        println!("\n=== {} formatter ===", format_name);
        println!("Output length: {} characters", output.len());
        println!(
            "First 200 chars: {}",
            &output.chars().take(200).collect::<String>()
        );

        // Verify output is non-empty and reasonable
        assert!(
            !output.is_empty(),
            "{} formatter produced empty output",
            format_name
        );
        assert!(
            output.len() < 1_000_000,
            "{} formatter produced suspiciously large output: {} chars",
            format_name,
            output.len()
        );
    }

    Ok(())
}

#[test]
fn stress_test_wide_metavariable_subscripts() -> Result<(), MguError> {
    // Create a proof that will exercise subscripts
    // We need more than 12 Boolean variables to trigger subscripts (φ, ψ, χ, ... κ are 0-11)
    let depth = 15; // Should give us 15+ variables, ensuring subscripts
    let mut proof = "D1".repeat(depth);
    proof.push('1');

    let term_factory = EnumTermFactory::new(SimpleTypeFactory);
    let metavar_factory = WideMetavariableFactory::new(SimpleTypeFactory);
    let dict = create_dict(
        &term_factory,
        &metavar_factory,
        NodeByte::Implies,
        NodeByte::Not,
    )?;

    let result: WideStatement =
        Statement::from_compact_proof(&proof, &metavar_factory, &term_factory, &dict)?;

    let vars = result.collect_metavariables()?;
    println!("Proof (depth {}) has {} variables", depth, vars.len());

    // Test UTF8 formatter with subscripts
    let formatter = get_formatter("utf8");
    let output = result.get_assertion().format_with(&*formatter);

    println!("UTF8 output: {}", output);
    println!("UTF8 output length: {} chars", output.len());

    // Check that we have subscript characters (₀₁₂₃₄₅₆₇₈₉)
    let has_subscripts = output.chars().any(|c| {
        matches!(
            c,
            '\u{2080}'
                | '\u{2081}'
                | '\u{2082}'
                | '\u{2083}'
                | '\u{2084}'
                | '\u{2085}'
                | '\u{2086}'
                | '\u{2087}'
                | '\u{2088}'
                | '\u{2089}'
        )
    });

    // With 15+ variables, we should definitely have subscripts
    assert!(
        has_subscripts,
        "Expected subscripts with {} variables",
        vars.len()
    );

    Ok(())
}

#[test]
fn stress_test_very_deep_nesting() -> Result<(), MguError> {
    // Test extreme depth (but fewer variables to keep it fast)
    // This tests the recursion depth handling in formatters
    let depth = 50;
    let mut proof = "D1".repeat(depth);
    proof.push('1');

    let term_factory = EnumTermFactory::new(SimpleTypeFactory);
    let metavar_factory = WideMetavariableFactory::new(SimpleTypeFactory);
    let dict = create_dict(
        &term_factory,
        &metavar_factory,
        NodeByte::Implies,
        NodeByte::Not,
    )?;

    let result: WideStatement =
        Statement::from_compact_proof(&proof, &metavar_factory, &term_factory, &dict)?;

    // Test that all formatters can handle the deep nesting without stack overflow
    for format_name in &["ascii", "utf8", "utf8-color", "latex", "display"] {
        let formatter = get_formatter(format_name);
        let output = result.get_assertion().format_with(&*formatter);

        println!("{}: {} chars", format_name, output.len());

        assert!(!output.is_empty(), "{} failed on deep nesting", format_name);
    }

    Ok(())
}
