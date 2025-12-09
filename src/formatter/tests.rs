//! Tests for formatter system.

use crate::formatter::{get_formatter, Color};
use crate::{
    EnumTerm, EnumTermFactory, MetaByte, MetaByteFactory, Metavariable, MetavariableFactory, Node,
    NodeByte, NodeByteFactory, NodeFactory, SimpleType, Term, TermFactory,
};

/// Helper to create a simple term: P → Q
#[must_use]
fn create_simple_term() -> EnumTerm<SimpleType, MetaByte, NodeByte> {
    let term_factory: EnumTermFactory<SimpleType, MetaByte, NodeByte> = EnumTermFactory::new();
    let metavar_factory = MetaByteFactory();
    let node_factory: NodeByteFactory<SimpleType> = NodeByteFactory::new();

    let p = metavar_factory.create("P", &SimpleType::Boolean).unwrap();
    let q = metavar_factory.create("Q", &SimpleType::Boolean).unwrap();
    let p_term = term_factory.create_leaf(p).unwrap();
    let q_term = term_factory.create_leaf(q).unwrap();

    let implies = node_factory.create_by_name("Implies", 2).unwrap();
    term_factory
        .create_node(implies, vec![p_term, q_term])
        .unwrap()
}

#[test]
fn formatter_registry() {
    // Test that formatters are registered
    let ascii_fmt = get_formatter("ascii");
    assert_eq!(ascii_fmt.name(), "ascii");

    let utf8_fmt = get_formatter("utf8");
    assert_eq!(utf8_fmt.name(), "utf8");

    let utf8_color_fmt = get_formatter("utf8-color");
    assert_eq!(utf8_color_fmt.name(), "utf8-color");

    let html_fmt = get_formatter("html");
    assert_eq!(html_fmt.name(), "html");

    let html_color_fmt = get_formatter("html-color");
    assert_eq!(html_color_fmt.name(), "html-color");

    let latex_fmt = get_formatter("latex");
    assert_eq!(latex_fmt.name(), "latex");
}

#[test]
fn color_formatters_provide_colors() {
    let utf8_color_fmt = get_formatter("utf8-color");
    assert_eq!(utf8_color_fmt.get_boolean_color(), Some(Color::BLUE));
    assert_eq!(utf8_color_fmt.get_setvar_color(), Some(Color::GREEN));
    assert_eq!(utf8_color_fmt.get_class_color(), Some(Color::RED));

    let html_color_fmt = get_formatter("html-color");
    assert_eq!(html_color_fmt.get_boolean_color(), Some(Color::BLUE));
    assert_eq!(html_color_fmt.get_setvar_color(), Some(Color::GREEN));
    assert_eq!(html_color_fmt.get_class_color(), Some(Color::RED));

    // Non-color formatters return None
    let ascii_fmt = get_formatter("ascii");
    assert_eq!(ascii_fmt.get_boolean_color(), None);
    assert_eq!(ascii_fmt.get_setvar_color(), None);
    assert_eq!(ascii_fmt.get_class_color(), None);
}

#[test]
fn metabyte_ascii_formatting() {
    let metavar_factory = MetaByteFactory();
    let p = metavar_factory.create("P", &SimpleType::Boolean).unwrap();

    let formatter = get_formatter("ascii");
    let formatted = p.format_with(&*formatter);
    assert_eq!(formatted, "P"); // MetaByte returns literal ASCII character
}

#[test]
fn metabyte_utf8_formatting() {
    let metavar_factory = MetaByteFactory();
    let p = metavar_factory.create("P", &SimpleType::Boolean).unwrap();

    let formatter = get_formatter("utf8");
    let formatted = p.format_with(&*formatter);
    assert_eq!(formatted, "P"); // Uses Display, which shows 'P'
}

#[test]
fn nodebyte_ascii_formatting() {
    let node_factory: NodeByteFactory<SimpleType> = NodeByteFactory::new();
    let implies = node_factory.create_by_name("Implies", 2).unwrap();

    let formatter = get_formatter("ascii");
    let formatted = implies.format_with(&*formatter);
    assert_eq!(formatted, "->"); // ASCII arrow
}

#[test]
fn nodebyte_utf8_formatting() {
    let node_factory: NodeByteFactory<SimpleType> = NodeByteFactory::new();
    let implies = node_factory.create_by_name("Implies", 2).unwrap();

    let formatter = get_formatter("utf8");
    let formatted = implies.format_with(&*formatter);
    assert_eq!(formatted, "→"); // Unicode arrow
}

#[test]
fn nodebyte_latex_formatting() {
    let node_factory: NodeByteFactory<SimpleType> = NodeByteFactory::new();
    let implies = node_factory.create_by_name("Implies", 2).unwrap();

    let formatter = get_formatter("latex");
    let formatted = implies.format_with(&*formatter);
    assert_eq!(formatted, r"\to "); // LaTeX command
}

#[test]
fn term_ascii_formatting() {
    let term = create_simple_term();
    let formatter = get_formatter("ascii");
    let formatted = term.format_with(&*formatter);
    // P → Q formatted in ASCII (MetaByte uses literal characters)
    assert_eq!(formatted, "(P -> Q)");
}

#[test]
fn term_utf8_formatting() {
    let term = create_simple_term();
    let formatter = get_formatter("utf8");
    let formatted = term.format_with(&*formatter);
    // P → Q formatted in UTF-8: (P → Q)
    assert_eq!(formatted, "(P → Q)");
}

#[test]
fn term_latex_formatting() {
    let term = create_simple_term();
    let formatter = get_formatter("latex");
    let formatted = term.format_with(&*formatter);
    // P → Q formatted in LaTeX (MetaByte uses literal characters)
    assert_eq!(formatted, r"(P \to  Q)");
}

#[test]
fn complex_term_formatting() {
    // Build: (P ∧ Q) → R
    let term_factory: EnumTermFactory<SimpleType, MetaByte, NodeByte> = EnumTermFactory::new();
    let metavar_factory = MetaByteFactory();
    let node_factory: NodeByteFactory<SimpleType> = NodeByteFactory::new();

    let p = term_factory
        .create_leaf(metavar_factory.create("P", &SimpleType::Boolean).unwrap())
        .unwrap();
    let q = term_factory
        .create_leaf(metavar_factory.create("Q", &SimpleType::Boolean).unwrap())
        .unwrap();
    let r = term_factory
        .create_leaf(metavar_factory.create("R", &SimpleType::Boolean).unwrap())
        .unwrap();

    let and_node = node_factory.create_by_name("And", 2).unwrap();
    let p_and_q = term_factory.create_node(and_node, vec![p, q]).unwrap();

    let implies_node = node_factory.create_by_name("Implies", 2).unwrap();
    let formula = term_factory
        .create_node(implies_node, vec![p_and_q, r])
        .unwrap();

    // Test UTF-8 formatting
    let utf8_formatter = get_formatter("utf8");
    let utf8_output = formula.format_with(&*utf8_formatter);
    assert_eq!(utf8_output, "((P ∧ Q) → R)");

    // Test ASCII formatting (MetaByte uses literal characters)
    let ascii_formatter = get_formatter("ascii");
    let ascii_output = formula.format_with(&*ascii_formatter);
    assert_eq!(ascii_output, "((P /\\ Q) -> R)");
}

#[test]
fn unary_operator_formatting() {
    // Build: ¬P
    let term_factory: EnumTermFactory<SimpleType, MetaByte, NodeByte> = EnumTermFactory::new();
    let metavar_factory = MetaByteFactory();
    let node_factory: NodeByteFactory<SimpleType> = NodeByteFactory::new();

    let p = term_factory
        .create_leaf(metavar_factory.create("P", &SimpleType::Boolean).unwrap())
        .unwrap();

    let not_node = node_factory.create_by_name("Not", 1).unwrap();
    let not_p = term_factory.create_node(not_node, vec![p]).unwrap();

    // Test UTF-8 formatting
    let utf8_formatter = get_formatter("utf8");
    let utf8_output = not_p.format_with(&*utf8_formatter);
    assert_eq!(utf8_output, "¬(P)");

    // Test ASCII formatting (MetaByte uses literal characters)
    let ascii_formatter = get_formatter("ascii");
    let ascii_output = not_p.format_with(&*ascii_formatter);
    assert_eq!(ascii_output, "-.(P)");
}
