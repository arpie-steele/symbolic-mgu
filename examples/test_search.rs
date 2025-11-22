//! Demonstrates systematic term enumeration using the search module.
//!
//! This example shows how to generate all terms of various types up to a given
//! depth, demonstrating the type system with Boolean, Setvar, and Class types.

use symbolic_mgu::search::{get_iterator, TermSearchStaticState};
use symbolic_mgu::{
    get_formatter, EnumTermFactory, MetavariableFactory, MguError, NodeByte, SimpleType, Term,
    WideMetavariable, WideMetavariableFactory,
};

fn run() -> Result<(), MguError> {
    let formatter = get_formatter("utf8");

    // Create variables of different types
    let vf = WideMetavariableFactory();
    let vars = vf
        .list_metavariables_by_type(&SimpleType::Boolean)
        .take(2)
        .chain(vf.list_metavariables_by_type(&SimpleType::Setvar).take(2))
        .chain(vf.list_metavariables_by_type(&SimpleType::Class).take(1))
        .collect::<Vec<_>>();

    // Nodes spanning different types and arities
    let nodes = vec![
        NodeByte::True,         // Boolean, arity 0
        NodeByte::Not,          // Boolean, arity 1
        NodeByte::Implies,      // Boolean, arity 2
        NodeByte::ForAll,       // Boolean, arity 2 (Setvar, Boolean)
        NodeByte::UniversalCls, // Class, arity 0
    ];

    let factory = EnumTermFactory::<SimpleType, WideMetavariable, NodeByte>::new();
    let search = TermSearchStaticState::new(factory, &nodes, &vars)?;

    // Demonstrate term generation for different types
    for term_type in &[SimpleType::Boolean, SimpleType::Setvar, SimpleType::Class] {
        println!("=== Type: {} ===", term_type);

        for depth in 0..=1 {
            let iterator = get_iterator(&search, *term_type, depth)?;
            let terms: Vec<_> = iterator.collect();

            if terms.is_empty() {
                continue;
            }

            println!("Depth {}: {} terms", depth, terms.len());
            for term in &terms {
                let formatted = term.format_with(&*formatter);
                println!("  {}", formatted);
            }
        }
        println!();
    }

    Ok(())
}

fn main() {
    if let Err(e) = run() {
        eprintln!("Error: {}", e);
        std::process::exit(1);
    }
}
