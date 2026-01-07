//! Pattern matching structures for efficient Metamath expression parsing.
//!
//! This module provides data structures for pre-processing syntax axioms into
//! efficient pattern matching structures. Syntax axioms define term constructors
//! (like implication, conjunction, etc.) and their arity and argument types.

use crate::metamath::{Axiom, Label, MetamathDatabase, SymbolKind, SyntaxInfo};
use std::sync::Arc;

/// A pre-processed syntax axiom pattern for efficient matching.
///
/// During parsing, we need to match symbol sequences against syntax axioms.
/// This struct provides pre-computed hints to quickly eliminate non-matching patterns.
#[derive(Debug, Clone)]
pub struct SyntaxAxiomPattern {
    /// The axiom label (e.g., `"wi"` for implication)
    pub label: Label,

    /// Result type code (e.g., `"wff"`)
    pub type_code: Arc<str>,

    /// The pattern sequence (statement minus type code)
    pub pattern: Vec<PatternElement>,

    /// Pre-computed matching hints for fast elimination
    pub hints: PatternHints,
}

/// An element in a syntax axiom pattern.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum PatternElement {
    /// A constant symbol (e.g., "(", "->", ")")
    Constant(Arc<str>),

    /// A variable placeholder (e.g., "ph" of type "wff")
    Variable {
        /// Variable name from the pattern
        name: Arc<str>,
        /// Type code of the variable
        type_code: Arc<str>,
    },
}

/// Pre-computed hints for fast pattern elimination.
///
/// These hints allow us to quickly eliminate patterns that cannot match
/// a given symbol sequence without doing full pattern matching.
#[derive(Debug, Clone)]
pub struct PatternHints {
    /// First constant in pattern (None if starts with variable)
    pub first_constant: Option<Arc<str>>,

    /// Last constant in pattern (None if ends with variable)
    pub last_constant: Option<Arc<str>>,

    /// All constants in pattern, in order of appearance
    pub constants_in_order: Vec<Arc<str>>,

    /// Pairs of adjacent constants (for quick elimination)
    pub adjacent_constants: Vec<(Arc<str>, Arc<str>)>,

    /// Number of variable slots (arity)
    pub arity: usize,
}

impl SyntaxAxiomPattern {
    /// Build a syntax axiom pattern from an axiom and syntax info.
    ///
    /// # Arguments
    ///
    /// * `axiom` - The syntax axiom to process
    /// * `db` - Database reference for symbol classification
    ///
    /// # Returns
    ///
    /// A pre-processed pattern with matching hints, or `None` if not a syntax axiom.
    pub fn from_axiom(axiom: &Axiom, db: &MetamathDatabase) -> Option<Self> {
        // Only process syntax axioms
        let syntax_info = axiom.syntax_info.as_ref()?;

        let type_code = axiom.type_code.clone();
        let statement = &axiom.core.statement;

        // Statement format: [`type_code`, ...symbols...]
        // Skip `type_code` (index 0), process the rest
        let sequence = &statement[1..];

        // Build pattern and hints
        let (pattern, hints) = Self::build_pattern_and_hints(sequence, syntax_info, db);

        Some(Self {
            label: axiom.core.label.clone(),
            type_code,
            pattern,
            hints,
        })
    }

    /// Build pattern elements and hints from a symbol sequence.
    fn build_pattern_and_hints(
        sequence: &[Arc<str>],
        syntax_info: &SyntaxInfo,
        db: &MetamathDatabase,
    ) -> (Vec<PatternElement>, PatternHints) {
        let mut pattern = Vec::new();
        let mut constants_in_order = Vec::new();
        let mut adjacent_constants = Vec::new();
        let mut first_constant = None;
        let mut last_constant = None;
        let mut prev_was_constant: Option<Arc<str>> = None;

        for (index, symbol) in sequence.iter().enumerate() {
            match db.symbol_kind(symbol) {
                Some(SymbolKind::Constant) => {
                    pattern.push(PatternElement::Constant(symbol.clone()));
                    constants_in_order.push(symbol.clone());

                    // `first_constant` is only set if the pattern STARTS with a constant
                    if first_constant.is_none() && index == 0 {
                        first_constant = Some(symbol.clone());
                    }
                    last_constant = Some(symbol.clone());

                    // Track adjacent constants
                    if let Some(prev_const) = prev_was_constant {
                        adjacent_constants.push((prev_const, symbol.clone()));
                    }
                    prev_was_constant = Some(symbol.clone());
                }
                Some(SymbolKind::Variable) => {
                    // Look up variable type from database
                    let var_type = db
                        .variable_type(symbol)
                        .unwrap_or_else(|| Arc::from("unknown"));

                    pattern.push(PatternElement::Variable {
                        name: symbol.clone(),
                        type_code: var_type,
                    });

                    // Pattern doesn't end with a constant if we see a variable
                    last_constant = None;
                    prev_was_constant = None;
                }
                None => {
                    // This shouldn't happen in well-formed databases
                    // but we'll treat it as a constant for robustness
                    pattern.push(PatternElement::Constant(symbol.clone()));
                    constants_in_order.push(symbol.clone());
                    prev_was_constant = Some(symbol.clone());
                }
            }
        }

        let hints = PatternHints {
            first_constant,
            last_constant,
            constants_in_order,
            adjacent_constants,
            arity: syntax_info.arity(),
        };

        (pattern, hints)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::metamath::{AssertionCore, Label, TypeMapping};
    use crate::DistinctnessGraph;
    use std::collections::HashSet;

    #[test]
    fn pattern_from_implication_axiom() {
        // Create a database with set.mm type mapping
        let db = Arc::new(MetamathDatabase::new(TypeMapping::set_mm()));

        // Register symbols
        db.register_constant_symbol(Arc::from("wff")).unwrap();
        db.register_constant_symbol(Arc::from("(")).unwrap();
        db.register_constant_symbol(Arc::from("->")).unwrap();
        db.register_constant_symbol(Arc::from(")")).unwrap();
        db.register_variable_symbol(Arc::from("ph")).unwrap();
        db.register_variable_symbol(Arc::from("ps")).unwrap();

        // Register variable types
        db.register_variable_type(Arc::from("wff"), Arc::from("ph"), 1)
            .unwrap();
        db.register_variable_type(Arc::from("wff"), Arc::from("ps"), 2)
            .unwrap();

        // Create implication syntax axiom: `wi $a wff ( ph -> ps ) $.`
        let statement = vec![
            Arc::from("wff"),
            Arc::from("("),
            Arc::from("ph"),
            Arc::from("->"),
            Arc::from("ps"),
            Arc::from(")"),
        ];

        let active_vars: HashSet<Arc<str>> =
            vec![Arc::from("ph"), Arc::from("ps")].into_iter().collect();

        let syntax_info = SyntaxInfo::from_statement(&statement, &active_vars, db.type_mapping())
            .expect("Should be a syntax axiom");

        let axiom = Axiom {
            core: AssertionCore {
                label: Label::new("wi").unwrap(),
                statement,
                line: 1,
                hypotheses: (Vec::new(), Vec::new()),
                comment: None,
                distinctness: DistinctnessGraph::new(),
            },
            type_code: Arc::from("wff"),
            syntax_info: Some(syntax_info),
        };

        // Build pattern
        let pattern = SyntaxAxiomPattern::from_axiom(&axiom, &db).unwrap();

        // Verify pattern
        assert_eq!(pattern.label.as_str(), "wi");
        assert_eq!(pattern.type_code.as_ref(), "wff");
        assert_eq!(pattern.pattern.len(), 5); // (, ph, ->, ps, )
        assert_eq!(pattern.hints.arity, 2);
        assert_eq!(pattern.hints.first_constant, Some(Arc::from("(")));
        assert_eq!(pattern.hints.last_constant, Some(Arc::from(")")));
        assert_eq!(pattern.hints.constants_in_order.len(), 3); // (, ->, )

        // Check pattern elements
        assert!(matches!(pattern.pattern[0], PatternElement::Constant(_)));
        assert!(matches!(
            pattern.pattern[1],
            PatternElement::Variable { .. }
        ));
        assert!(matches!(pattern.pattern[2], PatternElement::Constant(_)));
        assert!(matches!(
            pattern.pattern[3],
            PatternElement::Variable { .. }
        ));
        assert!(matches!(pattern.pattern[4], PatternElement::Constant(_)));
    }
}
