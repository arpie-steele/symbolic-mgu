//! Test custom formatter implementation to validate extension API.
//!
//! This test creates a throwaway JSON formatter to ensure that:
//! - Third parties can implement OutputFormatter trait
//! - The delegation pattern works correctly
//! - Formatters can be registered and retrieved

use symbolic_mgu::logic::create_dict;
use symbolic_mgu::{
    register_formatter, Color, EnumTermFactory, MguError, NodeByte, OutputFormatter, Statement,
    Term, WideMetavariable, WideMetavariableFactory,
};

/// A simple JSON formatter for testing the extension API.
///
/// This is a throwaway implementation to validate that third parties
/// can create custom formatters.
#[derive(Debug, Clone, Copy)]
struct JsonFormatter;

impl OutputFormatter for JsonFormatter {
    fn name(&self) -> &str {
        "json"
    }

    fn get_boolean_color(&self) -> Option<Color> {
        None // JSON doesn't use colors
    }

    fn get_setvar_color(&self) -> Option<Color> {
        None
    }

    fn get_class_color(&self) -> Option<Color> {
        None
    }
}

type WideStatement = Statement<
    symbolic_mgu::SimpleType,
    WideMetavariable,
    NodeByte,
    symbolic_mgu::EnumTerm<symbolic_mgu::SimpleType, WideMetavariable, NodeByte>,
>;

#[test]
fn test_custom_formatter_implementation() -> Result<(), MguError> {
    // Register the custom formatter
    register_formatter("json-test", JsonFormatter);

    // Create a simple proof
    let term_factory = EnumTermFactory::new();
    let metavar_factory = WideMetavariableFactory();
    let dict = create_dict(
        &term_factory,
        &metavar_factory,
        NodeByte::Implies,
        NodeByte::Not,
    )?;

    let result: WideStatement =
        Statement::from_compact_proof("DD211", &metavar_factory, &term_factory, &dict)?;

    // Get the custom formatter
    let formatter = symbolic_mgu::get_formatter("json-test");

    // Format the assertion
    let output = result.get_assertion().format_with(&*formatter);

    println!("Custom JSON formatter output: {}", output);

    // Verify the formatter was used (even though it falls back to Display)
    assert!(!output.is_empty(), "Formatter should produce output");
    assert_eq!(formatter.name(), "json");

    Ok(())
}

#[test]
fn test_custom_formatter_with_complex_proof() -> Result<(), MguError> {
    // Test with a more complex proof to exercise the formatter
    let depth = 10;
    let mut proof = "D1".repeat(depth);
    proof.push('1');

    let term_factory = EnumTermFactory::new();
    let metavar_factory = WideMetavariableFactory();
    let dict = create_dict(
        &term_factory,
        &metavar_factory,
        NodeByte::Implies,
        NodeByte::Not,
    )?;

    let result: WideStatement =
        Statement::from_compact_proof(&proof, &metavar_factory, &term_factory, &dict)?;

    // Use the custom formatter
    let formatter = JsonFormatter;
    let output = result.get_assertion().format_with(&formatter);

    println!(
        "Complex proof with custom formatter ({} chars): {}",
        output.len(),
        output
    );

    // Verify it handles deep nesting
    assert!(!output.is_empty());
    assert!(output.contains('→'), "Should contain implication operator");

    Ok(())
}

#[test]
fn test_formatter_trait_methods() {
    // Verify the OutputFormatter trait is properly implemented
    let formatter = JsonFormatter;

    assert_eq!(formatter.name(), "json");
    assert_eq!(formatter.get_boolean_color(), None);
    assert_eq!(formatter.get_setvar_color(), None);
    assert_eq!(formatter.get_class_color(), None);
}

#[test]
fn test_formatter_registration_and_retrieval() {
    // Test that formatters can be registered and retrieved
    register_formatter("json-test-2", JsonFormatter);

    let retrieved = symbolic_mgu::get_formatter("json-test-2");

    // Should get our formatter back
    assert_eq!(retrieved.name(), "json");

    // Unknown formatter should fall back to display formatter
    let fallback = symbolic_mgu::get_formatter("nonexistent-formatter-xyz");
    assert_eq!(fallback.name(), "display");
}
