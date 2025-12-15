//! Debug a specific theorem's verification.

use symbolic_mgu::metamath::{
    verify_theorem, Label, MetamathDatabase, Parser, StdFilesystem, TypeMapping,
};

fn main() {
    // Parse set.mm
    println!("Parsing set.mm...");
    let fs = StdFilesystem::new();
    let db = MetamathDatabase::new(TypeMapping::set_mm());
    let parser =
        Parser::new(fs, "tests/metamath-test/set.mm", db).expect("Failed to create parser");
    let db = parser.parse().expect("Failed to parse set.mm");

    // Get the 2lt10 theorem
    let label = Label::new("2lt10").expect("Failed to create label");
    let theorems = db.theorems();
    let theorem = theorems.get(&label).expect("Theorem not found");

    println!("\nTheorem: {}", label);
    println!("Statement: {:?}", theorem.statement);
    println!("\nHypotheses:");
    println!("  Floating ({}):", theorem.hypotheses.0.len());
    for hyp in &theorem.hypotheses.0 {
        println!("    {} $f {} {}", hyp.label, hyp.type_code, hyp.variable);
    }
    println!("  Essential ({}):", theorem.hypotheses.1.len());
    for hyp in &theorem.hypotheses.1 {
        println!("    {} $e {:?}", hyp.label, hyp.statement);
    }

    println!("\nProof:");
    if let Some(proof) = &theorem.proof {
        println!("  {:?}", proof);
    }

    // Check a few axioms used in the proof
    println!("\nAxioms used in proof:");
    for ax_name in &["wbr", "c2"] {
        let ax_label = Label::new(ax_name).expect("Failed to create label");
        if let Some(axiom) = db.axioms().get(&ax_label) {
            println!("  {} $a {:?}", ax_name, axiom.statement);
            println!("    Floating hyps: {}", axiom.hypotheses.0.len());
            println!("    Essential hyps: {}", axiom.hypotheses.1.len());
            for hyp in &axiom.hypotheses.0 {
                println!("      {} $f {} {}", hyp.label, hyp.type_code, hyp.variable);
            }
        }
    }

    println!("\nVerifying...");
    match verify_theorem(theorem, &db) {
        Ok(()) => println!("✓ Verification succeeded"),
        Err(e) => println!("✗ Verification failed: {:?}", e),
    }
}
