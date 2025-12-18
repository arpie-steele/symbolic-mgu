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
    use NodeByte::*;
    use SimpleType::*;
    let formatter = get_formatter("utf8");

    // Create variables of different types
    let vf = WideMetavariableFactory();
    let vars = vf
        .list_metavariables_by_type(&Boolean)
        .take(3)
        .chain(vf.list_metavariables_by_type(&Setvar).take(3))
        .chain(vf.list_metavariables_by_type(&Class).take(3))
        .collect::<Vec<_>>();

    // Nodes spanning different types and arities
    let nodes = vec![
        True,                // Boolean, arity 0
        Not,                 // Boolean, arity 1 (Boolean)
        OrdinalPred,         // Boolean, arity 1 (Class)
        Implies,             // Boolean, arity 2 (Boolean, Boolean)
        ForAll,              // Boolean, arity 2 (Setvar, Boolean)
        SetNotFreeInCls,     // Boolean, arity 2 (Setvar, Class)
        IsElementOf,         // Boolean, arity 2 (Class, Class)
        And3,                // Boolean, arity 3 (Boolean, Boolean, Boolean)
        ResForAll,           // Boolean, arity 3 (Setvar, Class, Boolean)
        SubClassInWff,       // Boolean, arity 3 (Class, Setvar, Boolean)
        BinaryRelation,      // Boolean, arity 3 (Class, Class, Class)
        RelationIsometry,    // Boolean, arity 5 (Class, Class, Class, Class, Class)
        UniversalCls,        // Class, arity 0
        PowerCls,            // Class, arity 1 (Class)
        UnionOp,             // Class, arity 2 (Class, Class)
        ClassIf,             // Class, arity 3 (Boolean, Class, Class)
        OrdPairsBuilder,     // Class, arity 3 (Setvar, Setvar, Boolean)
        IndexedIntersection, // Class, arity 3 (Setvar, Class, Class)
        SubClassInCls,       // Class, arity 3 (Class, Setvar, Class)
        OperatorBuilder,     // Class, arity 4 (Setvar, Setvar, Setvar, Boolean)
        OperatorMapsTo,      // Class, arity 5 (Setvar, Class, Setvar, Class, Class)
    ];

    let factory = EnumTermFactory::<SimpleType, WideMetavariable, NodeByte>::new();
    let search = TermSearchStaticState::new(factory, &nodes, &vars)?;

    // Demonstrate term generation for different types
    for term_type in &[Boolean, Setvar, Class] {
        println!("=== Type: {} ===", term_type);

        for depth in 0..=1 {
            println!();
            println!("Depth {}:", depth);
            let mut count = 0;
            for term in get_iterator(&search, *term_type, depth)? {
                count += 1;
                let formatted = term.format_with(&*formatter);
                if formatted.contains('?') {
                    println!("  {}", term);
                } else {
                    println!("  {}", formatted);
                }
            }
            println!();
            println!("Depth {}: {} terms", depth, count);
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
