//! A library to explore the *most general unifier* of mathematical
//! formulas.
//!
#![cfg_attr(doc, doc = include_str!("Epigram.md"))]
//!
#![cfg_attr(doc, doc = include_str!("Purpose.md"))]
//!
#![cfg_attr(doc, doc = include_str!("SystemOverview.md"))]
//!
#![cfg_attr(doc, doc = include_str!("FormalSpec.md"))]
//!
#![cfg_attr(doc, doc = include_str!("../docs/SCHOLARLY_CONTEXT.md"))]
//!
#![cfg_attr(doc, doc = include_str!("Hyperlinks.md"))]
#![cfg_attr(nightly, feature(doc_cfg))]
#![allow(unknown_lints)]
#![warn(
    missing_docs,
    unnameable_test_items,
    unused_doc_comments,
    clippy::cfg_not_test,
    clippy::doc_comment_double_space_linebreaks,
    clippy::doc_include_without_cfg,
    clippy::doc_lazy_continuation,
    clippy::doc_link_code,
    clippy::doc_link_with_quotes,
    clippy::doc_markdown,
    clippy::doc_nested_refdefs,
    clippy::doc_overindented_list_items,
    clippy::doc_suspicious_footnotes,
    clippy::empty_docs,
    clippy::empty_line_after_doc_comments,
    clippy::empty_line_after_outer_attr,
    clippy::items_after_test_module,
    clippy::missing_docs_in_private_items,
    clippy::missing_errors_doc,
    clippy::missing_panics_doc,
    clippy::missing_safety_doc,
    clippy::needless_doctest_main,
    clippy::redundant_test_prefix,
    clippy::suspicious_doc_comments,
    clippy::tabs_in_doc_comments,
    clippy::test_attr_in_doctest,
    clippy::tests_outside_test_module,
    clippy::too_long_first_doc_paragraph,
    clippy::undocumented_unsafe_blocks,
    clippy::unicode_not_nfc,
    clippy::unnecessary_safety_doc,
    rustdoc::all,
    rustdoc::missing_doc_code_examples
)]
#![deny(invalid_doc_attributes)]
#![allow(rustdoc::private_doc_tests)]

pub mod bool_eval;
pub(crate) mod distinct;
pub(crate) mod error;
pub(crate) mod formatter;
pub mod logic;
pub(crate) mod macros;
pub mod metamath;
pub(crate) mod metavariable;
pub(crate) mod mgutype;
pub(crate) mod node;
pub mod search;
pub(crate) mod statement;
pub(crate) mod term;

pub use distinct::pair::Pair;
pub use distinct::simple_graph::check_clique;
pub use distinct::simple_graph::check_decomposition;
pub use distinct::simple_graph::Clique;
pub use distinct::simple_graph::Decomposition;
pub use distinct::simple_graph::SimpleGraph;
pub use distinct::DistinctnessGraph;
pub use error::base::MguError;
pub use error::MguErrorType;
pub use formatter::{
    get_formatter, get_type_color, get_type_color_from_trait, register_formatter,
    register_type_color, Color, OutputFormatter,
};
pub use metavariable::charset::WideCharSet;
pub use metavariable::decorator::{Decorator, Prime};
pub use metavariable::enums::AsciiMetaVar;
pub use metavariable::factory::MetavariableFactory;
pub use metavariable::meta_byte::MetaByte;
pub use metavariable::meta_byte::MetaByteFactory;
pub use metavariable::parametric::ParametricMetavariable;
pub use metavariable::wide::WideMetavariable;
pub use metavariable::wide::WIDE_BOOLEANS;
pub use metavariable::wide::WIDE_BOOLEANS_ASCII;
pub use metavariable::wide::WIDE_CLASSES;
pub use metavariable::wide::WIDE_CLASSES_ASCII;
pub use metavariable::wide::WIDE_SETVARS;
pub use metavariable::wide::WIDE_SETVARS_ASCII;
pub use metavariable::wide_factory::WideMetavariableFactory;
pub use metavariable::Metavariable;
pub use mgutype::base::SimpleType;
pub use mgutype::type_trait::Type;
pub use mgutype::type_trait::TypeCore;
pub use node::base::Node;
pub use node::factory::NodeFactory;
pub use node::node_byte::base::NodeByte;
pub use node::node_byte::factory::NodeByteFactory;
pub use statement::Statement;
pub use term::base::Term;
pub use term::factory::TermFactory;
pub use term::simple::EnumTerm;
pub use term::simple::EnumTermFactory;
pub use term::substitution::apply_substitution;
pub use term::substitution::occurs_check;
pub use term::substitution::unify;
pub use term::substitution::NormalizingSubstitution;
pub use term::substitution::Substitution;

#[cfg(test)]
mod tests {
    #[test]
    fn it_works() {
        assert_eq!(2 + 2, 4);
    }
}
