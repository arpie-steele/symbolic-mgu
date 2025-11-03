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

pub mod bool_eval;
// pub mod color;
pub(crate) mod distinct;
pub(crate) mod error;
pub mod logic;
pub(crate) mod macros;
pub(crate) mod metavariable;
pub(crate) mod mgutype;
pub(crate) mod node;
pub mod search;
pub(crate) mod statement;
// pub mod svg;
pub(crate) mod term;
// #[cfg(feature = "video")]
// #[cfg_attr(docsrs, doc(cfg(feature = "video")))]
// pub mod video;

pub use bool_eval::generated_enum::BooleanSimpleOp;
pub use distinct::pair::Pair;
pub use distinct::simple_graph::check_clique;
pub use distinct::simple_graph::check_decomposition;
pub use distinct::simple_graph::Clique;
pub use distinct::simple_graph::Decomposition;
pub use distinct::simple_graph::SimpleGraph;
pub use distinct::DistinctnessGraph;
pub use error::base::MguError;
pub use error::err_type::MguErrorType;
// pub use metavariable::InfallibleMetavariable;
pub use metavariable::enums::AsciiMetaVar;
pub use metavariable::factory::MetavariableFactory;
pub use metavariable::meta_byte::MetaByte;
pub use metavariable::meta_byte::MetaByteFactory;
pub use metavariable::Metavariable;
// pub use metavariable::wide::WideMetavariable;
pub use mgutype::base::SimpleType;
pub use node::base::Node;
pub use node::factory::NodeFactory;
// pub use node::dbnode::DbNode;
// pub use node::dbnode::NodeDatabase;
// pub use node::dbnode::SimpleNodeDatabase;
// pub use node::dbnode::register_database;
pub use node::node_byte::base::NodeByte;
pub use node::node_byte::factory::NodeByteFactory;
// pub use node::traits::CopyableNode;
// pub use node::traits::EnumerableNode;
// pub use node::traits::IndexableNode;
// pub use node::traits::InfallibleNodeCore;
// pub use node::traits::NodeCore;
// pub use node::traits::StaticSlotNode;
pub use mgutype::type_trait::Type;
pub use mgutype::type_trait::TypeCore;
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
// pub use term::dbterm::DbTerm;
// pub use term::veryfinite::TinyTerm;

#[cfg(test)]
mod tests {
    #[test]
    fn it_works() {
        assert_eq!(2 + 2, 4);
    }
}
