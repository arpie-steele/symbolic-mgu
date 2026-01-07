//! Introduce an implementation of [`Node`] that can fit in a [`u8`] and not collide with a legal value for [`AsciiMetaVar`].
//!
//! See docs for [`NodeByte`] to seen how the 222 values are represented.
//!
//! [`Node`]: `crate::Node`
//! [`AsciiMetaVar`]: `crate::AsciiMetaVar`

use crate::bool_eval::BooleanSimpleOp;
use crate::{enum0, MguError, Node, OutputFormatter, SimpleType};
use strum::{
    Display, EnumCount, EnumDiscriminants, EnumString, FromRepr, VariantArray, VariantNames,
};

enum0! {
/// Selected 222 Node types.
///
/// # Design Notes
///
/// **Toy Implementation**: This is a concrete toy implementation of the [`Node`] trait,
/// intended for testing and examples. Production code should use trait-based abstractions
/// as described in the project architectural principles.
///
/// **Discriminant Values**: The `u8` discriminant values for these 222 variants have been
/// carefully hand-picked to avoid collisions with [`MetaByte`] and [`AsciiMetaVar`] values.
/// This allows Polish notation byte-strings to represent complete terms by interleaving
/// node operators and metavariables without ambiguity.
///
/// [`MetaByte`]: `crate::MetaByte`
/// [`Node`]: `crate::Node`
/// [`AsciiMetaVar`]: `crate::AsciiMetaVar`
///
#[cfg_attr(doc, doc = include_str!("NodeByteTable.md"))]
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord, Display, EnumCount, EnumDiscriminants, EnumString, FromRepr, VariantArray, VariantNames)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
#[repr(u8)]
#[allow(clippy::doc_markdown)]
pub enum NodeByte {
{"Restricted For All."; "wff ∀𝑥 ∈ 𝐴 𝜑"; "⊢ (∀𝑥 ∈ 𝐴 𝜑 ↔ ∀𝑥(𝑥 ∈ 𝐴 → 𝜑))"; ResForAll = 0x00},
{"Logical And (3-arity)."; "wff (𝜑 ∧ 𝜓 ∧ 𝜒)"; "⊢ ((𝜑 ∧ 𝜓 ∧ 𝜒) ↔ ((𝜑 ∧ 𝜓) ∧ 𝜒))"; And3},
{"Conditional Equality."; "wff CondEq(𝑥 = 𝑦 → 𝜑)"; "⊢ (CondEq(𝑥 = 𝑦 → 𝜑) ↔ (𝑥 = 𝑦 → 𝜑))"; CondEq},
{"Carry output for a full adder.", "", "It is true when at least two arguments are true, so it is equal to the \"majority\" function on three variables."; "wff cadd(𝜑, 𝜓, 𝜒)"; "⊢ (cadd(𝜑, 𝜓, 𝜒) ↔ ((𝜑 ∧ 𝜓) ∨ (𝜒 ∧ (𝜑 ⊻ 𝜓))))"; CarryFromAdder},
{"Substitution of class for setvar in class expression."; "class ⦋𝐴 / 𝑥⦌𝐵"; "⊢ ⦋𝐴 / 𝑥⦌𝐵 = {𝑦 ∣ [𝐴 / 𝑥]𝑦 ∈ 𝐵}"; SubClassInCls},
{"Not Element Of."; "wff 𝐴 ∉ 𝐵"; "⊢ (𝐴 ∉ 𝐵 ↔ ¬ 𝐴 ∈ 𝐵)"; NotElementOf},
{"Class Subset Connective."; "wff 𝐴 ⊆ 𝐵"; "⊢ (𝐴 ⊆ 𝐵 ↔ ∀𝑥(𝑥 ∈ 𝐴 → 𝑥 ∈ 𝐵))"; Subset},
{"Class Proper Subset Connective."; "wff 𝐴 ⊊ 𝐵"; "⊢ (𝐴 ⊊ 𝐵 ↔ (𝐴 ⊆ 𝐵 ∧ 𝐴 ≠ 𝐵))"; ProperSubset},
{"Half-adder, \"sum\" output of the full adder.", "Triple exclusive disjunction (XOR3).", "", "True when an odd number of its inputs are true."; "wff hadd(𝜑, 𝜓, 𝜒)"; "⊢ (hadd(𝜑, 𝜓, 𝜒) ↔ ((𝜑 ⊻ 𝜓) ⊻ 𝜒))"; SumFromAdder},
{"Conditional Operator for Propositions."; "wff if-(𝜑, 𝜓, 𝜒)"; "⊢ (if-(𝜑, 𝜓, 𝜒) ↔ ((𝜑 ∧ 𝜓) ∨ (¬ 𝜑 ∧ 𝜒)))"; LogicalIf},
{"Class Difference Operator."; "class (𝐴 ∖ 𝐵)"; "⊢ (𝐴 ∖ 𝐵) = {𝑥 ∣ (𝑥 ∈ 𝐴 ∧ ¬ 𝑥 ∈ 𝐵)}"; DiffOp},
{"Class Union Binary Operator."; "class (𝐴 ∪ 𝐵)"; "⊢ (𝐴 ∪ 𝐵) = {𝑥 ∣ (𝑥 ∈ 𝐴 ∨ 𝑥 ∈ 𝐵)}"; UnionOp},
{"Class Intersection Binary Operator."; "class (𝐴 ∩ 𝐵)"; "⊢ (𝐴 ∩ 𝐵) = {𝑥 ∣ (𝑥 ∈ 𝐴 ∧ 𝑥 ∈ 𝐵)}"; IntersectionOp},
{"Restricted There Exists at Most One."; "wff ∃*𝑥 ∈ 𝐴 𝜑"; "⊢ (∃*𝑥 ∈ 𝐴 𝜑 ↔ ∃*𝑥(𝑥 ∈ 𝐴 ∧ 𝜑))"; ResExAtMostOne},
{"Class Symmetric Difference Operator."; "class (𝐴 △ 𝐵)"; "⊢ (𝐴 △ 𝐵) = ((𝐴 ∖ 𝐵) ∪ (𝐵 ∖ 𝐴))"; SymDiffOp},
{"Logical Or (3-arity)."; "wff (𝜑 ∨ 𝜓 ∨ 𝜒)"; "⊢ ((𝜑 ∨ 𝜓 ∨ 𝜒) ↔ ((𝜑 ∨ 𝜓) ∨ 𝜒))"; Or3},
{"Power Class."; "class 𝒫 𝐴"; "⊢ 𝒫 𝐴 = {𝑥 ∣ 𝑥 ⊆ 𝐴}"; PowerCls = 0x10},
{"Not Equals."; "wff 𝐴 ≠ 𝐵"; "⊢ (𝐴 ≠ 𝐵 ↔ ¬ 𝐴 = 𝐵)"; NotEquals},
{"Universal Class."; "class V"; "⊢ V = {𝑥 ∣ 𝑥 = 𝑥}"; UniversalCls},
{"Restricted There Uniquely Exists."; "wff ∃!𝑥 ∈ 𝐴 𝜑"; "⊢ (∃!𝑥 ∈ 𝐴 𝜑 ↔ ∃!𝑥(𝑥 ∈ 𝐴 ∧ 𝜑))"; ResExExactlyOne},
{"Tranistive Class Predicate."; "wff Tr 𝐴"; "⊢ (Tr 𝐴 ↔ ∪ 𝐴 ⊆ 𝐴)"; TransCls},
{"Singleton."; "class {𝐴}"; "⊢ {𝐴} = {𝑥 ∣ 𝑥 = 𝐴}"; Singleton},
{"Unordered Pair."; "class {𝐴, 𝐵}"; "⊢ {𝐴, 𝐵} = ({𝐴} ∪ {𝐵})"; UnorderdPair},
{"Unordered Triple."; "class {𝐴, 𝐵, 𝐶}"; "⊢ {𝐴, 𝐵, 𝐶} = ({𝐴, 𝐵} ∪ {𝐶})"; UnorderdTriple},
{"Class Union."; "class ∪ 𝐴"; "⊢ ∪ 𝐴 = {𝑥 ∣ ∃𝑦(𝑥 ∈ 𝑦 ∧ 𝑦 ∈ 𝐴)}"; ClassUnion},
{"Class Intersection."; "class ∩ 𝐴"; "⊢ ∩ 𝐴 = {𝑥 ∣ ∀𝑦(𝑦 ∈ 𝐴 → 𝑥 ∈ 𝑦)}"; ClassIntersection},
{"Indexed Union."; "class ∪ 𝑥 ∈ 𝐴 𝐵"; "⊢ ∪ 𝑥 ∈ 𝐴 𝐵 = {𝑦 ∣ ∃𝑥 ∈ 𝐴 𝑦 ∈ 𝐵}"; IndexedUnion},
{"Substitution is primitive."; "wff [𝑦 / 𝑥]𝜑"; "⊢ ([𝑡 / 𝑥]𝜑 ↔ ∀𝑦(𝑦 = 𝑡 → ∀𝑥(𝑥 = 𝑦 → 𝜑)))", "𝑥-𝑦, 𝑦-𝑡, 𝜑-𝑦"; SubSetInWff},
{"Substitution of class for setvar in boolean expression."; "wff [𝐴 / 𝑥]𝜑"; "⊢ ([𝐴 / 𝑥]𝜑 ↔ 𝐴 ∈ {𝑥 ∣ 𝜑})", ""; SubClassInWff},
{"Restricted There Exists."; "wff ∃𝑥 ∈ 𝐴 𝜑"; "⊢ (∃𝑥 ∈ 𝐴 𝜑 ↔ ∃𝑥(𝑥 ∈ 𝐴 ∧ 𝜑))"; ResExists},
{"Setvar not free in formula."; "wff Ⅎ𝑥𝜑"; "⊢ (Ⅎ𝑥𝜑 ↔ (∃𝑥𝜑 → ∀𝑥𝜑))"; SetNotFreeInWff},
{"Setvar not free in class."; "wff Ⅎ𝑥𝐴"; "⊢ (Ⅎ𝑥𝐴 ↔ ∀𝑦Ⅎ𝑥 𝑦 ∈ 𝐴)"; SetNotFreeInCls},
{"Binary Relation."; "wff 𝐴𝑅𝐵"; "⊢ (𝐴𝑅𝐵 ↔ ⟨𝐴, 𝐵⟩ ∈ 𝑅)"; BinaryRelation = 0x20},
{"Logical Negation is primitive."; "wff ¬ 𝜑"; "Transp ⊢ ((¬ 𝜑 → ¬ 𝜓) → (𝜓 → 𝜑))"; Not},
{"Indexed Intersection."; "class ∩ 𝑥 ∈ 𝐴 𝐵"; "⊢ ∩ 𝑥 ∈ 𝐴 𝐵 = {𝑦 ∣ ∀𝑥 ∈ 𝐴 𝑦 ∈ 𝐵}"; IndexedIntersection},
{"Disjoint Family."; "wff Disj 𝑥 ∈ 𝐴 𝐵"; "⊢ (Disj 𝑥 ∈ 𝐴 𝐵 ↔ ∀𝑦∃*𝑥 ∈ 𝐴 𝑦 ∈ 𝐵)"; DisjointFamily},
{"Binary operator which returns a function's support."; "class supp"; "⊢ supp = (𝑥 ∈ V, 𝑧 ∈ V ↦ {𝑖 ∈ dom 𝑥 ∣ (𝑥 “ {𝑖}) ≠ {𝑧}})"; SupportOperator},
{"Convert a binary operator over a class into a binary operator on functions", "with a codomain in that class."; "class ∘f 𝑅"; "⊢ ∘f 𝑅 = (𝑓 ∈ V, 𝑔 ∈ V ↦ (𝑥 ∈ (dom 𝑓 ∩ dom 𝑔) ↦ ((𝑓‘𝑥)𝑅(𝑔‘𝑥))))"; OperatorToFuns},
{"Logical And (2-arity)."; "wff (𝜑 ∧ 𝜓)"; "⊢ ((𝜑 ∧ 𝜓) ↔ ¬ (𝜑 → ¬ 𝜓))"; And},
{"Convert a relation on a class into a relation on functions which have codomains in that class."; "class ∘r 𝑅"; "⊢ ∘r 𝑅 = {⟨𝑓, 𝑔⟩ ∣ ∀𝑥 ∈ (dom 𝑓 ∩ dom 𝑔)(𝑓‘𝑥)𝑅(𝑔‘𝑥)}"; RelationToFuns},
{"A relation which is equivalent to the proper subset connective."; "class [⊊]"; "⊢ [⊊] = {⟨𝑥, 𝑦⟩ ∣ 𝑥 ⊊ 𝑦}"; ProperSubsetRel},
{"Apply Class Binary Operator."; "class (𝐴𝐹𝐵)"; "⊢ (𝐴𝐹𝐵) = (𝐹‘⟨𝐴, 𝐵⟩)"; ApplyOperator},
{"Define the multiplication operation for complex numbers."; "class ·"; "⊢ · = {⟨⟨𝑥, 𝑦⟩, 𝑧⟩ ∣ ((𝑥 ∈ ℂ ∧ 𝑦 ∈ ℂ) ∧ ∃𝑤∃𝑣∃𝑢∃𝑓((𝑥 = ⟨𝑤, 𝑣⟩ ∧ 𝑦 = ⟨𝑢, 𝑓⟩) ∧ 𝑧 = ⟨((𝑤 ·R 𝑢) +R (-1R ·R (𝑣 ·R 𝑓))), ((𝑣 ·R 𝑢) +R (𝑤 ·R 𝑓))⟩))}"; Multiplication},
{"Define the addition operation for complex numbers."; "class +"; "⊢ + = {⟨⟨𝑥, 𝑦⟩, 𝑧⟩ ∣ ((𝑥 ∈ ℂ ∧ 𝑦 ∈ ℂ) ∧ ∃𝑤∃𝑣∃𝑢∃𝑓((𝑥 = ⟨𝑤, 𝑣⟩ ∧ 𝑦 = ⟨𝑢, 𝑓⟩) ∧ 𝑧 = ⟨(𝑤 +R 𝑢), (𝑣 +R 𝑓)⟩))}"; Addition},
{"Ordered Pair Class Builder."; "class {⟨𝑥, 𝑦⟩ ∣ 𝜑}"; "⊢ {⟨𝑥, 𝑦⟩ ∣ 𝜑} = {𝑧 ∣ ∃𝑥∃𝑦(𝑧 = ⟨𝑥, 𝑦⟩ ∧ 𝜑)}"; OrdPairsBuilder},
{"Define the subtraction operation for complex numbers."; "class −"; "⊢ − = (𝑥 ∈ ℂ, 𝑦 ∈ ℂ ↦ (℩𝑧 ∈ ℂ (𝑦 + 𝑧) = 𝑥))"; Subtraction},
{"The disjoint union of two classes."; "class (𝐴 ⊔ 𝐵)"; "⊢ (𝐴 ⊔ 𝐵) = (({∅} × 𝐴) ∪ ({1o} × 𝐵))"; DisjointUnion},
{"Define the division operation for complex numbers."; "class /"; "⊢ / = (𝑥 ∈ ℂ, 𝑦 ∈ (ℂ ∖ {0}) ↦ (℩𝑧 ∈ ℂ (𝑦 · 𝑧) = 𝑥))"; Division},
{"Logically False."; "wff ⊥"; "⊢ (⊥ ↔ ¬ ⊤)"; False = 0x30},
{"Logically True."; "wff ⊤"; "⊢ (⊤ ↔ (∀𝑥 𝑥 = 𝑥 → ∀𝑥 𝑥 = 𝑥))"; True},
{"Ordered Pair."; "class ⟨𝐴, 𝐵⟩"; "⊢ ⟨𝐴, 𝐵⟩ = {𝑥 ∣ (𝐴 ∈ V ∧ 𝐵 ∈ V ∧ 𝑥 ∈ {{𝐴}, {𝐴, 𝐵}})}"; OrderedPair},
{"There Uniquely Exists."; "wff ∃!𝑥𝜑"; "⊢ (∃!𝑥𝜑 ↔ (∃𝑥𝜑 ∧ ∃*𝑥𝜑))"; ExistsExactlyOne},
{"Ordered Triple."; "class ⟨𝐴, 𝐵, 𝐶⟩"; "⊢ ⟨𝐴, 𝐵, 𝐶⟩ = ⟨⟨𝐴, 𝐵⟩, 𝐶⟩"; OrderedTriple},
{"One-to-one Function Predicate."; "wff 𝐹:𝐴–1-1→𝐵"; "⊢ (𝐹:𝐴–1-1→𝐵 ↔ (𝐹:𝐴⟶𝐵 ∧ Fun ◡𝐹))"; OneToOneFun},
{"Onto Function Predicate."; "wff 𝐹:𝐴–onto→𝐵"; "⊢ (𝐹:𝐴–onto→𝐵 ↔ (𝐹 Fn 𝐴 ∧ ran 𝐹 = 𝐵))"; OntoFun},
{"One-to-one Onto Function Predicate."; "wff 𝐹:𝐴–1-1-onto→𝐵"; "⊢ (𝐹:𝐴–1-1-onto→𝐵 ↔ (𝐹:𝐴–1-1→𝐵 ∧ 𝐹:𝐴–onto→𝐵))"; OneToOneOntoFun},
{"Omega, the smallest infinite ordinal."; "class ω"; "⊢ ω = {𝑥 ∈ On ∣ ∀𝑦(Lim 𝑦 → 𝑥 ∈ 𝑦)}"; Omega},
{"Binary Operator Maps-to."; "class (𝑥 ∈ 𝐴, 𝑦 ∈ 𝐵 ↦ 𝐶)"; "⊢ (𝑥 ∈ 𝐴, 𝑦 ∈ 𝐵 ↦ 𝐶) = {⟨⟨𝑥, 𝑦⟩, 𝑧⟩ ∣ ((𝑥 ∈ 𝐴 ∧ 𝑦 ∈ 𝐵) ∧ 𝑧 = 𝐶)}"; OperatorMapsTo},
{"Biimplication or Logical Equivalence.", "Used for definition of boolean-valued wffs.", "", "This is semi-primitive in that it is an expanded self-referential", "definition which otherwise could be written like:", "* ⊢ ((𝜑 ↔ 𝜓) ↔ ((𝜑 → 𝜓) ∧ (𝜓 → 𝜑)))"; "wff (𝜑 ↔ 𝜓)"; "⊢ ¬ (((𝜑 ↔ 𝜓) → ¬ ((𝜑 → 𝜓) → ¬ (𝜓 → 𝜑))) → ¬ (¬ ((𝜑 → 𝜓) → ¬ (𝜓 → 𝜑)) → (𝜑 ↔ 𝜓)))"; Biimp},
{"Build class of ordered triples."; "class {⟨⟨𝑥, 𝑦⟩, 𝑧⟩ ∣ 𝜑}"; "⊢ {⟨⟨𝑥, 𝑦⟩, 𝑧⟩ ∣ 𝜑} = {𝑤 ∣ ∃𝑥∃𝑦∃𝑧(𝑤 = ⟨⟨𝑥, 𝑦⟩, 𝑧⟩ ∧ 𝜑)}"; OperatorBuilder},
{"Define the less-than relation for the extended reals."; "class <"; "⊢ < = ({⟨𝑥, 𝑦⟩ ∣ (𝑥 ∈ ℝ ∧ 𝑦 ∈ ℝ ∧ 𝑥 <ℝ 𝑦)} ∪ (((ℝ ∪ {-∞}) × {+∞}) ∪ ({-∞} × ℝ)))"; LessThan},
{"Equals is primitive.", "Used for definition of boolean-valued wffs."; "wff 𝐴 = 𝐵"; "Assert: ⊢ (𝐴 = 𝐵 ↔ ∀𝑥(𝑥 ∈ 𝐴 ↔ 𝑥 ∈ 𝐵))", "Hypothesis: ⊢ (𝑦 = 𝑧 ↔ ∀𝑢(𝑢 ∈ 𝑦 ↔ 𝑢 ∈ 𝑧))", "Hypothesis: ⊢ (𝑡 = 𝑡 ↔ ∀𝑣(𝑣 ∈ 𝑡 ↔ 𝑣 ∈ 𝑡))", "Distinctness graph: 𝑥,𝑦,𝑧,𝑡,𝑢,𝑣,𝐴   𝑥,𝐵,𝑦,𝑧,𝑡,𝑢,𝑣"; Equals},
{"Material Implication is primitive."; "wff (𝜑 → 𝜓)"; "Assert:  ⊢ 𝜓", "Hypothesis: ⊢ 𝜑", "Hypothesis: ⊢ (𝜑 → 𝜓)", "Simp ⊢ (𝜑 → (𝜓 → 𝜑))", "Frege ⊢ ((𝜑 → (𝜓 → 𝜒)) → ((𝜑 → 𝜓) → (𝜑 → 𝜒)))"; Implies},
{"Conditional Class."; "class if(𝜑, 𝐴, 𝐵)"; "⊢ if(𝜑, 𝐴, 𝐵) = {𝑥 ∣ ((𝑥 ∈ 𝐴 ∧ 𝜑) ∨ (𝑥 ∈ 𝐵 ∧ ¬ 𝜑))}"; ClassIf},
{"For All is primitive."; "wff ∀𝑥𝜑"; "..."; ForAll = 0x40},
{"Membership Relation."; "class E"; "⊢ E = {⟨𝑥, 𝑦⟩ ∣ 𝑥 ∈ 𝑦}"; MembershipRelation = b'E'},
{"Identity Relation (a function)."; "class I"; "⊢ I = {⟨𝑥, 𝑦⟩ ∣ 𝑥 = 𝑦}"; IdentityRelation = b'I'},
{"Ordinal natural addition."; "class +no"; "⊢ +no = frecs({⟨𝑥, 𝑦⟩ ∣ (𝑥 ∈ (On × On) ∧ 𝑦 ∈ (On × On) ∧ (((1st ‘𝑥) E (1st ‘𝑦) ∨ (1st ‘𝑥) = (1st ‘𝑦)) ∧ ((2nd ‘𝑥) E (2nd ‘𝑦) ∨ (2nd ‘𝑥) = (2nd ‘𝑦)) ∧ 𝑥 ≠ 𝑦))}, (On × On), (𝑧 ∈ V, 𝑎 ∈ V ↦ ∩ {𝑤 ∈ On ∣ ((𝑎 “ ({(1st ‘𝑧)} × (2nd ‘𝑧))) ⊆ 𝑤 ∧ (𝑎 “ ((1st ‘𝑧) × {(2nd ‘𝑧)})) ⊆ 𝑤)}))"; OrdNaturalAdd = b'N'},
{"class +no"; "class ∅"; "⊢ ∅ = (V ∖ V)"; EmptyCls},
{"The equivalence class for an element."; r"class \[𝐴]𝑅"; r"⊢ \[𝐴]𝑅 = (𝑅 “ {𝐴})"; EquivalenceCls = b'['},
{"Define the non-negative integers as a subset of the complex numbers."; "class ℕ0"; "⊢ ℕ0 = (ℕ ∪ {0})"; NonnegativeIntegers},
{"There Exists."; "wff ∃𝑥𝜑"; "⊢ (∃𝑥𝜑 ↔ ¬ ∀𝑥 ¬ 𝜑)"; Exists},
{"Least upper bound if it exists."; "class sup(𝐴, 𝐵, 𝑅)"; "⊢ sup(𝐴, 𝐵, 𝑅) = ∪ {𝑥 ∈ 𝐵 ∣ (∀𝑦 ∈ 𝐴 ¬ 𝑥𝑅𝑦 ∧ ∀𝑦 ∈ 𝐵 (𝑦𝑅𝑥 → ∃𝑧 ∈ 𝐴 𝑦𝑅𝑧))}"; Supremum},
{"Greatest lower bound if it exists."; "class inf(𝐴, 𝐵, 𝑅)"; "⊢ inf(𝐴, 𝐵, 𝑅) = sup(𝐴, 𝐵, ◡𝑅)"; Infimum},
{"The value of an applied function."; "class (𝐹‘𝐴)"; "⊢ (𝐹‘𝐴) = (℩𝑥𝐴𝐹𝑥)";  ApplyFun = 0x60},
{"Is Element Of is primitive."; "wff 𝐴 ∈ 𝐵"; " Assert: ⊢ (𝐴 ∈ 𝐵 ↔ ∃𝑥(𝑥 = 𝐴 ∧ 𝑥 ∈ 𝐵))", "Hypothesis: ⊢ (𝑦 ∈ 𝑧 ↔ ∃𝑢(𝑢 = 𝑦 ∧ 𝑢 ∈ 𝑧))", "Hypothesis: ⊢ (𝑡 ∈ 𝑡 ↔ ∃𝑣(𝑣 = 𝑡 ∧ 𝑣 ∈ 𝑡))", "Distinctness graph: 𝑥,𝑦,𝑧,𝑡,𝑢,𝑣,𝐴   𝑥,𝐵,𝑦,𝑧,𝑡,𝑢,𝑣";  IsElementOf = b'e'},
{"Restricted iota."; "class (℩𝑥 ∈ 𝐴 𝜑)"; "⊢ (℩𝑥 ∈ 𝐴 𝜑) = (℩𝑥(𝑥 ∈ 𝐴 ∧ 𝜑))"; ResIota = b'h'},
{"Iota operator, Russell's definition description binder."; "class (℩𝑥𝜑)"; "⊢ (℩𝑥𝜑) = ∪ {𝑦 ∣ {𝑥 ∣ 𝜑} = {𝑦}}"; Iota},
{"A function which defines the cumulative hierarchy of sets.", "", "* ⊢ (𝑅1‘∅) = ∅", "* ⊢ (𝐴 ∈ dom 𝑅1 → (𝑅1‘suc 𝐴) = 𝒫 (𝑅1‘𝐴))", "* ⊢ ((𝐴 ∈ dom 𝑅1 ∧ Lim 𝐴) → (𝑅1‘𝐴) = ∪ 𝑥 ∈ 𝐴 (𝑅1‘𝑥))"; "class 𝑅1"; "⊢ 𝑅1 = rec((𝑥 ∈ V ↦ 𝒫 𝑥), ∅)"; CumulativeHierarchy},
{"A function between sets and all intersections of the finite subsets of that set."; "class fi"; "⊢ fi = (𝑥 ∈ V ↦ {𝑧 ∣ ∃𝑦 ∈ (𝒫 𝑥 ∩ Fin)𝑧 = ∩ 𝑦})"; FiniteIntersection},
{"Define the rank function, something like an inverse of the cumulative hierarchy of set."; "class rank"; "⊢ rank = (𝑥 ∈ V ↦ ∩ {𝑦 ∈ On ∣ 𝑥 ∈ (𝑅1‘suc 𝑦)})"; Rank},
{"There Exists at Most One."; "wff ∃*𝑥𝜑"; "Assert: ⊢ (∃*𝑥𝜑 ↔ ∃𝑦∀𝑥(𝜑 → 𝑥 = 𝑦))", "Distinctness graph: 𝑥-𝑦   𝜑-𝑦"; ExistsAtMostOne},
{"Logical NAND (Not-And)."; "wff (𝜑 ⊼ 𝜓)"; "⊢ ((𝜑 ⊼ 𝜓) ↔ ¬ (𝜑 ∧ 𝜓))"; NotAnd},
{"Logical XOR (Exclusive-Or)."; "wff (𝜑 ⊻ 𝜓)"; "⊢ ((𝜑 ⊻ 𝜓) ↔ ¬ (𝜑 ↔ 𝜓))"; ExclusiveOr},
{"Logical NOR (Not-Or)."; "wff (𝜑 ⊽ 𝜓)"; "⊢ ((𝜑 ⊽ 𝜓) ↔ ¬ (𝜑 ∨ 𝜓))"; NotOr = 0x70},
{"All sets of finite cardinality."; "class Fin"; "⊢ Fin = {𝑥 ∣ ∃𝑦 ∈ ω 𝑥 ≈ 𝑦}"; FiniteSets},
{"The recursive definition generator on the class of ordinal numbers with", "a characteristic function and an initial value."; "class rec(𝐹, 𝐼)"; "⊢ rec(𝐹, 𝐼) = recs((𝑔 ∈ V ↦ if(𝑔 = ∅, 𝐼, if(Lim dom 𝑔, ∪ ran 𝑔, (𝐹‘(𝑔‘∪ dom 𝑔))))))"; RecursiveGenerator},
{"Index-aware recursive definitions over the finite ordinals."; "class seqω(𝐹, 𝐼)"; "⊢ seqω(𝐹, 𝐼) = (rec((𝑖 ∈ ω, 𝑣 ∈ V ↦ ⟨suc 𝑖, (𝑖𝐹𝑣)⟩), ⟨∅, ( I ‘𝐼)⟩) “ ω)"; IndexAwareRecGen},
{"Transpose a binary operation."; "class tpos 𝐹"; "⊢ tpos 𝐹 = (𝐹 ∘ (𝑥 ∈ (◡dom 𝐹 ∪ {∅}) ↦ ∪ ◡{𝑥}))"; FunTranspose},
{"Class Builder."; "class {𝑥 ∣ 𝜑}"; "⊢ (𝑥 ∈ {𝑦 ∣ 𝜑} ↔ [𝑥 / 𝑦]𝜑)"; ClassBuilder = b'{'},
{"Logical Or (2-arity)."; "wff (𝜑 ∨ 𝜓)"; "⊢ ((𝜑 ∨ 𝜓) ↔ (¬ 𝜑 → 𝜓))"; Or},
{"Define the positive integers as a subset of the complex numbers."; "class ℕ"; "⊢ ℕ = (rec((𝑥 ∈ V ↦ (𝑥 + 1)), 1) “ ω)"; PositiveIntegers},
{"Relationship isometry predicate."; "wff 𝐻 Isom 𝑅, 𝑆 (𝐴, 𝐵)"; "⊢ (𝐻 Isom 𝑅, 𝑆 (𝐴, 𝐵) ↔ (𝐻:𝐴–1-1-onto→𝐵 ∧ ∀𝑥 ∈ 𝐴 ∀𝑦 ∈ 𝐴 (𝑥𝑅𝑦 ↔ (𝐻‘𝑥)𝑆(𝐻‘𝑦))))"; RelationIsometry},
{"A boolean which is true if the Axiom of Choice holds."; "wff CHOICE"; "⊢ (CHOICE ↔ ∀𝑥∃𝑓(𝑓 ⊆ 𝑥 ∧ 𝑓 Fn dom 𝑥))"; ChoiceAxiomHolds},
{"A function from the ordinals to all inifinite cardinalities."; "class ℵ"; "⊢ ℵ = rec(har, ω)"; AlephFun = 0x80},
{"Function to extract the first element of an ordered pair."; "class 1st"; "⊢ 1st = (𝑥 ∈ V ↦ ∪ dom {𝑥})"; ExtractFirst},
{"Function to extract the second element of an ordered pair."; "class 2nd"; "⊢ 2nd = (𝑥 ∈ V ↦ ∪ ran {𝑥})"; ExtractSecond},
{"An opeerator which returns a function which expands ordinals less than the first", "raised to the power of the second in terms of a sum of weighted powers of the first."; "class CNF"; "⊢ CNF = (𝑥 ∈ On, 𝑦 ∈ On ↦ (𝑓 ∈ {𝑔 ∈ (𝑥 ↑m 𝑦) ∣ 𝑔 finSupp ∅} ↦ ⦋OrdIso( E , (𝑓 supp ∅)) / ℎ⦌(seqω((𝑘 ∈ V, 𝑧 ∈ V ↦ (((𝑥 ↑o (ℎ‘𝑘)) ·o (𝑓‘(ℎ‘𝑘))) +o 𝑧)), ∅)‘dom ℎ)))"; CantorNormalForm},
{"The class of all Tarski classes."; "class Tarski"; "⊢ Tarski = {𝑦 ∣ (∀𝑧 ∈ 𝑦 (𝒫 𝑧 ⊆ 𝑦 ∧ ∃𝑤 ∈ 𝑦 𝒫 𝑧 ⊆ 𝑤) ∧ ∀𝑧 ∈ 𝒫 𝑦(𝑧 ≈ 𝑦 ∨ 𝑧 ∈ 𝑦))}"; TarskiClasses},
{"Test if a relation is an equivalence relation on a class."; "wff 𝑅 Er 𝐴"; "⊢ (𝑅 Er 𝐴 ↔ (Rel 𝑅 ∧ dom 𝑅 = 𝐴 ∧ (◡𝑅 ∪ (𝑅 ∘ 𝑅)) ⊆ 𝑅))"; EquivalenceRelPred},
{"Well-Founded Relation Predicate."; "wff 𝑅 Fr 𝐴"; "⊢ (𝑅 Fr 𝐴 ↔ ∀𝑥((𝑥 ⊆ 𝐴 ∧ 𝑥 ≠ ∅) → ∃𝑦 ∈ 𝑥 ∀𝑧 ∈ 𝑥 ¬ 𝑧𝑅𝑦))"; WellFounded},
{"All sets for which the Generalized Continuum Hypothesis holds,", "i.e. for every set there is no set which strictly dominates it", "and is in turn strictly dominated by the powerset of the original set."; "class GCH"; "⊢ GCH = (Fin ∪ {𝑥 ∣ ∀𝑦 ¬ (𝑥 ≺ 𝑦 ∧ 𝑦 ≺ 𝒫 𝑥)})"; GenContinuumHyp},
{"The Hartogs function which maps a set to the smallest ordinal which has a larger cardinality."; "class har"; "⊢ har = (𝑥 ∈ V ↦ {𝑦 ∈ On ∣ 𝑦 ≼ 𝑥})"; HartogsFun},
{"When a relation is a well-order and set-like, return a function from", "initial ordinals to its range such that it is isomorphic to those ordinals."; "class OrdIso(𝑅, 𝐴)"; "⊢ OrdIso(𝑅, 𝐴) = if((𝑅 We 𝐴 ∧ 𝑅 Se 𝐴), (recs((ℎ ∈ V ↦ (℩𝑣 ∈ {𝑤 ∈ 𝐴 ∣ ∀𝑗 ∈ ran ℎ 𝑗𝑅𝑤}∀𝑢 ∈ {𝑤 ∈ 𝐴 ∣ ∀𝑗 ∈ ran ℎ 𝑗𝑅𝑤} ¬ 𝑢𝑅𝑣))) ↾ {𝑥 ∈ On ∣ ∃𝑡 ∈ 𝐴 ∀𝑧 ∈ (recs((ℎ ∈ V ↦ (℩𝑣 ∈ {𝑤 ∈ 𝐴 ∣ ∀𝑗 ∈ ran ℎ 𝑗𝑅𝑤}∀𝑢 ∈ {𝑤 ∈ 𝐴 ∣ ∀𝑗 ∈ ran ℎ 𝑗𝑅𝑤} ¬ 𝑢𝑅𝑣))) “ 𝑥)𝑧𝑅𝑡}), ∅)"; OrdinalIsomorphism},
{"An injection from the left set to the disjoint union of two classes."; "class inl"; "⊢ inl = (𝑥 ∈ V ↦ ⟨∅, 𝑥⟩)"; LeftInjection},
{"An injection from the right set to the disjoint union of two classes."; "class inr"; "⊢ inr = (𝑥 ∈ V ↦ ⟨1o, 𝑥⟩)"; RightInjection},
{"Weakly Inaccessible Cardinals. Infinite ordinals which are fixed points of", "cofinality and have no element which is not strictly dominated by another element.", "The class of regular limit cardinals, including omega."; "class Inaccw"; "⊢ Inaccw = {𝑥 ∣ (𝑥 ≠ ∅ ∧ (cf‘𝑥) = 𝑥 ∧ ∀𝑦 ∈ 𝑥 ∃𝑧 ∈ 𝑥 𝑦 ≺ 𝑧)}"; WeakInaccessibles},
{"Strongly Inaccessible Cardinals. Infinite ordinals which are fixed points of", "cofinality which strictly dominate the powerset of every smaller ordinal.", "The class of regular strong limit cardinals, including omega."; "class Inacc"; "⊢ Inacc = {𝑥 ∣ (𝑥 ≠ ∅ ∧ (cf‘𝑥) = 𝑥 ∧ ∀𝑦 ∈ 𝑥 𝒫 𝑦 ≺ 𝑥)}"; StrongInaccessibles},
{"The class of all Grothendieck Universes.", "", "A Grothendieck universe is a set that is closed with respect to all the operations that are common in set theory: pairs, powersets, unions, intersections, Cartesian products etc."; "class Univ"; "⊢ Univ = {𝑢 ∣ (Tr 𝑢 ∧ ∀𝑥 ∈ 𝑢 (𝒫 𝑥 ∈ 𝑢 ∧ ∀𝑦 ∈ 𝑢 {𝑥, 𝑦} ∈ 𝑢 ∧ ∀𝑦 ∈ (𝑢 ↑m 𝑥)∪ ran 𝑦 ∈ 𝑢))}"; GrothendieckUnis},
{"Strict Complete Order Relation Predicate."; "wff 𝑅 Or 𝐴"; "⊢ (𝑅 Or 𝐴 ↔ (𝑅 Po 𝐴 ∧ ∀𝑥 ∈ 𝐴 ∀𝑦 ∈ 𝐴 (𝑥𝑅𝑦 ∨ 𝑥 = 𝑦 ∨ 𝑦𝑅𝑥)))"; CompleteOrder},
{"Strict Partial Order Relation Predicate."; "wff 𝑅 Po 𝐴"; "⊢ (𝑅 Po 𝐴 ↔ ∀𝑥 ∈ 𝐴 ∀𝑦 ∈ 𝐴 ∀𝑧 ∈ 𝐴 (¬ 𝑥𝑅𝑥 ∧ ((𝑥𝑅𝑦 ∧ 𝑦𝑅𝑧) → 𝑥𝑅𝑧)))"; PartialOrder = 0x90},
{"A relation between functions and elements when only a finite portion of the", "domain doesn't map to that element."; "class finSupp"; "⊢ finSupp = {⟨𝑟, 𝑧⟩ ∣ (Fun 𝑟 ∧ (𝑟 supp 𝑧) ∈ Fin)}"; FiniteSupport},
{"Define a recursive function on the ordinal numbers."; "class recs(𝐹)"; "⊢ recs(𝐹) = wrecs( E , On, 𝐹)"; StrongTfinRecGen},
{"Set-like Relation Predicate."; "wff 𝑅 Se 𝐴"; "⊢ (𝑅 Se 𝐴 ↔ ∀𝑥 ∈ 𝐴 {𝑦 ∈ 𝐴 ∣ 𝑦𝑅𝑥} ∈ V)"; SetLike},
{"The transitive closure of a relation."; "class t++𝑅"; "⊢ t++𝑅 = {⟨𝑥, 𝑦⟩ ∣ ∃𝑛 ∈ (ω ∖ 1o)∃𝑓(𝑓 Fn suc 𝑛 ∧ ((𝑓‘∅) = 𝑥 ∧ (𝑓‘𝑛) = 𝑦) ∧ ∀𝑚 ∈ 𝑛 (𝑓‘𝑚)𝑅(𝑓‘suc 𝑚))}"; TransClassClosure},
{"A function which maps sets to a value which isn't an element."; "class Undef"; "⊢ Undef = (𝑠 ∈ V ↦ 𝒫 ∪ 𝑠)"; UndefinedFun},
{"A function which returns the transitive closure of a set."; "class TC"; "⊢ TC = (𝑥 ∈ V ↦ ∩ {𝑦 ∣ (𝑥 ⊆ 𝑦 ∧ Tr 𝑦)})"; TransClosureFun},
{"Well-ordering Relation Predicate."; "wff 𝑅 We 𝐴"; "⊢ (𝑅 We 𝐴 ↔ (𝑅 Fr 𝐴 ∧ 𝑅 Or 𝐴))"; WellOrdering},
{"All functions from a set to elements of the classes indexed by elements of that set."; "class X𝑥 ∈ 𝐴 𝐵"; "⊢ X𝑥 ∈ 𝐴 𝐵 = {𝑓 ∣ (𝑓 Fn {𝑥 ∣ 𝑥 ∈ 𝐴} ∧ ∀𝑥 ∈ 𝐴 (𝑓‘𝑥) ∈ 𝐵)}"; IndexedCartProduct},
{"The class of all weak universes. A weak universe is a nonempty transitive class", "closed under union, pairing, and powerset."; "class WUni"; "⊢ WUni = {𝑢 ∣ (Tr 𝑢 ∧ 𝑢 ≠ ∅ ∧ ∀𝑥 ∈ 𝑢 (∪ 𝑥 ∈ 𝑢 ∧ 𝒫 𝑥 ∈ 𝑢 ∧ ∀𝑦 ∈ 𝑢 {𝑥, 𝑦} ∈ 𝑢))}"; WeakUnis},
{"A function that maps a set to the smallest weak universe that is a superset."; "class wUniCl"; "⊢ wUniCl = (𝑥 ∈ V ↦ ∩ {𝑢 ∈ WUni ∣ 𝑥 ⊆ 𝑢})"; WeakUniClosure},
{"A relation between a set and the sets which can be mapped onto it."; "class ≼*"; "⊢ ≼* = {⟨𝑥, 𝑦⟩ ∣ (𝑥 = ∅ ∨ ∃𝑧 𝑧:𝑦–onto→𝑥)}"; WeakDominance},
{"Construction of the Complex Numbers:", "Define a set of positive integers."; "class N"; "⊢ N = (ω ∖ {∅})"; SetPosInts},
{"Construction of the Complex Numbers:", "Define the addition operator for positive integers."; "class +N"; "⊢ +N = ( +o ↾ (N × N))"; AddPosInts},
{"Construction of the Complex Numbers:", "Define the multiplication operator for positive integers."; "class ·N"; "⊢ ·N = ( ·o ↾ (N × N))"; MulPosInts},
{"Construction of the Complex Numbers:", "Define the less-than relation for positive integers."; "class <N"; "⊢ <N = ( E ∩ (N × N))"; LtPosInts},
{"Construction of the Complex Numbers:", "Define the addition operator for positive fractions."; "class +pQ"; "⊢ +pQ = (𝑥 ∈ (N × N), 𝑦 ∈ (N × N) ↦ ⟨(((1st ‘𝑥) ·N (2nd ‘𝑦)) +N ((1st ‘𝑦) ·N (2nd ‘𝑥))), ((2nd ‘𝑥) ·N (2nd ‘𝑦))⟩)"; AddPosFracs = 0xA0},
{"Construction of the Complex Numbers:", "Define the multiplication operator for positive fractions."; "class ·pQ"; "⊢ ·pQ = (𝑥 ∈ (N × N), 𝑦 ∈ (N × N) ↦ ⟨((1st ‘𝑥) ·N (1st ‘𝑦)), ((2nd ‘𝑥) ·N (2nd ‘𝑦))⟩)"; MulPosFracs},
{"Image of a relation."; "class (𝐴 “ 𝐵)"; "⊢ (𝐴 “ 𝐵) = ran (𝐴 ↾ 𝐵)"; Image},
{"A function from a set to its cardinality, an ordinal."; "class card"; "⊢ card = (𝑥 ∈ V ↦ ∩ {𝑦 ∈ On ∣ 𝑦 ≈ 𝑥})"; Cardinality},
{"A function that maps a set to the smallest Tarski class that contains the set."; "class tarskiMap"; "⊢ tarskiMap = (𝑥 ∈ V ↦ ∩ {𝑦 ∈ Tarski ∣ 𝑥 ∈ 𝑦})"; TarskiClassClosure},
{"Construction of the Complex Numbers:", "Define the less-than relation for positive fractions."; "class <pQ"; "⊢ <pQ = {⟨𝑥, 𝑦⟩ ∣ ((𝑥 ∈ (N × N) ∧ 𝑦 ∈ (N × N)) ∧ ((1st ‘𝑥) ·N (2nd ‘𝑦)) <N ((1st ‘𝑦) ·N (2nd ‘𝑥)))}"; LtPosFracs},
{"Define the positive reals as a subset of the complex numbers."; "class ℝ+"; "⊢ ℝ+ = {𝑥 ∈ ℝ ∣ 0 < 𝑥}"; PositiveReals},
{"Construction of the Complex Numbers:", "Define an equivalence relation on the postive fractions,", "setting up the positive rationals."; "class ~Q"; "⊢ ~Q = {⟨𝑥, 𝑦⟩ ∣ ((𝑥 ∈ (N × N) ∧ 𝑦 ∈ (N × N)) ∧ ∃𝑧∃𝑤∃𝑣∃𝑢((𝑥 = ⟨𝑧, 𝑤⟩ ∧ 𝑦 = ⟨𝑣, 𝑢⟩) ∧ (𝑧 ·N 𝑢) = (𝑤 ·N 𝑣)))}"; EqPosFracs},
{"A relation between a set and a set of equal or greater cardinality."; "class ≼"; "⊢ ≼ = {⟨𝑥, 𝑦⟩ ∣ ∃𝑓 𝑓:𝑥–1-1→𝑦}"; Dominance},
{"Define the set of extended reals."; "class ℝ*"; "⊢ ℝ* = (ℝ ∪ {+∞, -∞})"; ExtendedReals},
{"Ordinal multiplication."; "class ·o"; "⊢ ·o = (𝑥 ∈ On, 𝑦 ∈ On ↦ (rec((𝑧 ∈ V ↦ (𝑧 +o 𝑥)), ∅)‘𝑦))"; OrdMult},
{"Ordinal addition."; "class +o"; "⊢ +o = (𝑥 ∈ On, 𝑦 ∈ On ↦ (rec((𝑧 ∈ V ↦ suc 𝑧), 𝑥)‘𝑦))"; OrdAdd},
{"Define the extended non-negative integers as a subset of the extended reals."; "class ℕ0*"; "⊢ ℕ0* = (ℕ0 ∪ {+∞})"; ExtendedNonnegInts},
{"Define the additive inverse for complex numbers."; "class -𝐴"; "⊢ -𝐴 = (0 − 𝐴)"; UnaryMinus},
{"Define the construction of decimal integers from digits."; "class ;𝐴𝐵"; "⊢ ;𝐴𝐵 = (((9 + 1) · 𝐴) + 𝐵)"; DecimalConstructor},
{"The quotient sets of a relation."; "class (𝐴 / 𝑅)"; r"⊢ (𝐴 / 𝑅) = {𝑦 ∣ ∃𝑥 ∈ 𝐴 𝑦 = \[𝑥]𝑅}"; QuotientSets},
{"Define zero as a complex number."; "class 0"; "⊢ 0 = ⟨0R, 0R⟩"; Zero = 0xB0},
{"Define one as a complex number."; "class 1"; "⊢ 1 = ⟨1R, 0R⟩"; One},
{"Define two as a complex number."; "class 2"; "⊢ 2 = (1 + 1)"; Two},
{"Define three as a complex number."; "class 3"; "⊢ 3 = (2 + 1)"; Three},
{"Define four as a complex number."; "class 4"; "⊢ 4 = (3 + 1)"; Four},
{"Define five as a complex number."; "class 5"; "⊢ 5 = (4 + 1)"; Five},
{"Define six as a complex number."; "class 6"; "⊢ 6 = (5 + 1)"; Six},
{"Define seven as a complex number."; "class 7"; "⊢ 7 = (6 + 1)"; Seven},
{"Define eight as a complex number."; "class 8"; "⊢ 8 = (7 + 1)"; Eight},
{"Define nine as a complex number."; "class 9"; "⊢ 9 = (8 + 1)"; Nine},
{"Function Predicate with Domain and Codomain."; "wff 𝐹:𝐴⟶𝐵"; "⊢ (𝐹:𝐴⟶𝐵 ↔ (𝐹 Fn 𝐴 ∧ ran 𝐹 ⊆ 𝐵))"; FunWDomAndCodom},
{"Define the square root of minus one, i, as a complex number."; "class i"; "⊢ i = ⟨0R, 1R⟩"; SqrtMinusOne},
{"A relation between a set and a set of strictly greater cardinality."; "class ≺"; "⊢ ≺ = ( ≼ ∖ ≈ )"; StrictDominance},
{"Define negative infinity as a second element also not in the complex numbers."; "class -∞"; "⊢ -∞ = 𝒫 +∞"; NegInfinity},
{"Maps-to function definition."; "class (𝑥 ∈ 𝐴 ↦ 𝐵)"; "⊢ (𝑥 ∈ 𝐴 ↦ 𝐵) = {⟨𝑥, 𝑦⟩ ∣ (𝑥 ∈ 𝐴 ∧ 𝑦 = 𝐵)}"; MapsTo},
{"Define the a function giving the upper integers."; "class ℤ≥"; "⊢ ℤ≥ = (𝑗 ∈ ℤ ↦ {𝑘 ∈ ℤ ∣ 𝑗 ≤ 𝑘})"; UpperIntegers},
{"Construction of the Complex Numbers:", "Define a set of positive rationals."; "class Q"; "⊢ Q = {𝑥 ∈ (N × N) ∣ ∀𝑦 ∈ (N × N)(𝑥 ~Q 𝑦 → ¬ (2nd ‘𝑦) <N (2nd ‘𝑥))}"; SetPosRats = 0xC0},
{"Construction of the Complex Numbers:", "Define one for the positive rationals."; "class 1Q"; "⊢ 1Q = ⟨1o, 1o⟩"; OnePosRats},
{"Construction of the Complex Numbers:", "Define a function between positive fractions", "and corresponding positive rationals as a subset."; r"class \[Q]"; r"⊢ \[Q] = ( ~Q ∩ ((N × N) × Q))"; ReducePosRats},
{"Split a function of two arguments into a function of the first argument,", "producing a function over the second argument."; "class curry 𝐴"; "⊢ curry 𝐹 = (𝑥 ∈ dom dom 𝐹 ↦ {⟨𝑦, 𝑧⟩ ∣ ⟨𝑥, 𝑦⟩𝐹𝑧})"; Curry},
{"Domain of a class."; "class dom 𝐴"; "⊢ dom 𝐴 = {𝑥 ∣ ∃𝑦 𝑥𝐴𝑦}"; Domain},
{"Construction of the Complex Numbers:", "Define the addition operator for positive rationals."; "class +Q"; r"⊢ +Q = ((\[Q] ∘ +pQ ) ↾ (Q × Q))"; AddPosRats},
{"Function Predicate."; "wff Fun 𝐴"; "⊢ (Fun 𝐴 ↔ (Rel 𝐴 ∧ (𝐴 ∘ ◡𝐴) ⊆ I ))"; FunPred},
{"Construction of the Complex Numbers:", "Define the multiplication operator for positive rationals."; "class ·Q"; r"⊢ ·Q = ((\[Q] ∘ ·pQ ) ↾ (Q × Q))"; MulPosRats},
{"Ordinal one."; "class 1o"; "⊢ 1o = suc ∅"; OrdOne},
{"Ordinal two."; "class 2o"; "⊢ 2o = suc 1o"; OrdTwo},
{"Ordinal three."; "class 3o"; "⊢ 3o = suc 2o"; OrdThree},
{"Ordinal four."; "class 4o"; "⊢ 4o = suc 3o"; OrdFour},
{"Limit Ordinal predicate."; "wff Lim 𝐴"; "⊢ (Lim 𝐴 ↔ (Ord 𝐴 ∧ 𝐴 ≠ ∅ ∧ 𝐴 = ∪ 𝐴))"; LimitOrdinalPred},
{"Operator which returns all functions from the set on the right to the set on the left."; "class ↑m"; "⊢ ↑m = (𝑥 ∈ V, 𝑦 ∈ V ↦ {𝑓 ∣ 𝑓:𝑦⟶𝑥})"; MappingOp},
{"Class of Ordinals."; "class On"; "⊢ On = {𝑥 ∣ Ord 𝑥}"; Ordinals},
{"Ordinal predicate."; "wff Ord 𝐴"; "⊢ (Ord 𝐴 ↔ (Tr 𝐴 ∧ E We 𝐴))"; OrdinalPred},
{"Operator which returns all functions from a subset of the set on the right", "to the set on the left."; "class ↑pm"; "⊢ ↑pm = (𝑥 ∈ V, 𝑦 ∈ V ↦ {𝑓 ∈ 𝒫 (𝑦 × 𝑥) ∣ Fun 𝑓})"; PartialMappingOp = 0xD0},
{"Construction of the Complex Numbers:", "Define inverse function for the positive rationals."; "class *Q"; "⊢ *Q = (◡ ·Q “ {1Q})"; InvPosRats},
{"Range of a class."; "class ran 𝐴"; "⊢ ran 𝐴 = dom ◡𝐴"; Range},
{"Strictly monotonic ordinal function predicate."; "wff Smo 𝐴"; "⊢ (Smo 𝐴 ↔ (𝐴:dom 𝐴⟶On ∧ Ord dom 𝐴 ∧ ∀𝑥 ∈ dom 𝐴∀𝑦 ∈ dom 𝐴(𝑥 ∈ 𝑦 → (𝐴‘𝑥) ∈ (𝐴‘𝑦))))"; SmoFunPred},
{"Define the less-than relation for positive rationals."; "class <Q"; "⊢ <Q = ( <pQ ∩ (Q × Q))"; LtPosRats},
{"Takes a function producing functions, and transforms it into a two-argument function."; "class uncurry 𝐴"; "⊢ uncurry 𝐹 = {⟨⟨𝑥, 𝑦⟩, 𝑧⟩ ∣ 𝑦(𝐹‘𝑥)𝑧}"; Uncurry},
{"Construction of the Complex Numbers:", "Define a set of positive reals."; "class P"; "⊢ P = {𝑥 ∣ ((∅ ⊊ 𝑥 ∧ 𝑥 ⊊ Q) ∧ ∀𝑦 ∈ 𝑥 (∀𝑧(𝑧 <Q 𝑦 → 𝑧 ∈ 𝑥) ∧ ∃𝑧 ∈ 𝑥 𝑦 <Q 𝑧))}"; SetPosReals},
{"Construction of the Complex Numbers:", "Define one for the positive reals."; "class 1P"; "⊢ 1P = {𝑥 ∣ 𝑥 <Q 1Q}"; OnePosReals},
{"Cartesian Product of two classes."; "class (𝐴 × 𝐵)"; "⊢ (𝐴 × 𝐵) = {⟨𝑥, 𝑦⟩ ∣ (𝑥 ∈ 𝐴 ∧ 𝑦 ∈ 𝐵)}"; CartesianProduct},
{"Construction of the Complex Numbers:", "Define the addition operator for positive reals."; "class +P"; "⊢ +P = (𝑥 ∈ P, 𝑦 ∈ P ↦ {𝑤 ∣ ∃𝑣 ∈ 𝑥 ∃𝑢 ∈ 𝑦 𝑤 = (𝑣 +Q 𝑢)})"; AddPosReals},
{"Construction of the Complex Numbers:", "Define the multiplication operator for positive reals."; "class ·P"; "⊢ ·P = (𝑥 ∈ P, 𝑦 ∈ P ↦ {𝑤 ∣ ∃𝑣 ∈ 𝑥 ∃𝑢 ∈ 𝑦 𝑤 = (𝑣 ·Q 𝑢)})"; MulPosReals},
{"Define the set of complex numbers as ordered pairs of temporary reals."; "class ℂ"; "⊢ ℂ = (R × R)"; ComplexNumbers},
{"Define the integers as a subset of the complex numbers."; "class ℤ"; "⊢ ℤ = {𝑛 ∈ ℝ ∣ (𝑛 = 0 ∨ 𝑛 ∈ ℕ ∨ -𝑛 ∈ ℕ)}"; Integers},
{"Define the set of real numbers as a subset of complex numbers."; "class ℝ"; "⊢ ℝ = (R × {0R})"; RealNumbers},
{"Restriction of a relation."; "class (𝐴 ↾ 𝐵)"; "⊢ (𝐴 ↾ 𝐵) = (𝐴 ∩ (𝐵 × V))"; Restriction},
{"Define the less-than relation for real numbers."; "class <ℝ"; "⊢ <ℝ = {⟨𝑥, 𝑦⟩ ∣ ((𝑥 ∈ ℝ ∧ 𝑦 ∈ ℝ) ∧ ∃𝑧∃𝑤((𝑥 = ⟨𝑧, 0R⟩ ∧ 𝑦 = ⟨𝑤, 0R⟩) ∧ 𝑧 <R 𝑤))}"; LtReals},
{"Converse relation of a class."; "class ◡𝐴"; "⊢ ◡𝐴 = {⟨𝑥, 𝑦⟩ ∣ 𝑦𝐴𝑥}"; Converse = 0xE0},
{"The class of all sets such that for all families of non-empty subsets of that set and", "indexed by the given class there is a function from the given class that selects", "an element from each set in that family."; "class AC 𝐴"; "⊢ AC 𝐴 = {𝑥 ∣ (𝐴 ∈ V ∧ ∀𝑓 ∈ ((𝒫 𝑥 ∖ {∅}) ↑m 𝐴)∃𝑔∀𝑦 ∈ 𝐴 (𝑔‘𝑦) ∈ (𝑓‘𝑦))}"; LocalAxiomChoice},
{"Construction of the Complex Numbers:", "Define the less-than relation for positive reals."; "class <P"; "⊢ <P = {⟨𝑥, 𝑦⟩ ∣ ((𝑥 ∈ P ∧ 𝑦 ∈ P) ∧ 𝑥 ⊊ 𝑦)}"; LtPosReals},
{"A function from an ordinal to cardinality of the smallest", "unbounded subset of the ordinal number.", "", "Unbounded means that for every member of the ordinal number,", "there is a member of the subset of ordinal that is at least as large.", "Cofinality is a measure of how \"reachable from below\" an ordinal is."; "class cf"; "⊢ cf = (𝑥 ∈ On ↦ ∩ {𝑦 ∣ ∃𝑧(𝑦 = (card‘𝑧) ∧ (𝑧 ⊆ 𝑥 ∧ ∀𝑣 ∈ 𝑥 ∃𝑢 ∈ 𝑧 𝑣 ⊆ 𝑢))})"; Cofinality},
{"Construction of the Complex Numbers:", "Define an equivalence relation on the postive reals,", "setting up the temporary reals."; "class ~R"; "⊢ ~R = {⟨𝑥, 𝑦⟩ ∣ ((𝑥 ∈ (P × P) ∧ 𝑦 ∈ (P × P)) ∧ ∃𝑧∃𝑤∃𝑣∃𝑢((𝑥 = ⟨𝑧, 𝑤⟩ ∧ 𝑦 = ⟨𝑣, 𝑢⟩) ∧ (𝑧 +P 𝑢) = (𝑤 +P 𝑣)))}"; EqTmpReals},
{"Ordinal exponentiation."; "class ↑o"; "⊢ ↑o = (𝑥 ∈ On, 𝑦 ∈ On ↦ if(𝑥 = ∅, (1o ∖ 𝑦), (rec((𝑧 ∈ V ↦ (𝑧 ·o 𝑥)), 1o)‘𝑦)))"; OrdExp},
{"The well-founded recursion generator.  We want 𝑅 to be well-founded and set-like."; "class frecs(𝑅, 𝐴, 𝐹)"; "⊢ frecs(𝑅, 𝐴, 𝐹) = ∪ {𝑓 ∣ ∃𝑥(𝑓 Fn 𝑥 ∧ (𝑥 ⊆ 𝐴 ∧ ∀𝑦 ∈ 𝑥 Pred(𝑅, 𝐴, 𝑦) ⊆ 𝑥) ∧ ∀𝑦 ∈ 𝑥 (𝑓‘𝑦) = (𝑦𝐹(𝑓 ↾ Pred(𝑅, 𝐴, 𝑦))))}"; WellFoundRecGen},
{"Sets which are not the union of two sets which are not equinumerous to", "finite ordinals.", "", "One of eight definitions due to Lévy, 1958, which are", "all equivalent if the Axiom of Choice holds."; "class FinIa"; "⊢ FinIa = {𝑥 ∣ ∀𝑦 ∈ 𝒫 𝑥(𝑦 ∈ Fin ∨ (𝑥 ∖ 𝑦) ∈ Fin)}"; Finite1a},
{"Sets for which every nonempty chain of subsets has a maximum element. Tarski finite sets."; "class FinII"; "⊢ FinII = {𝑥 ∣ ∀𝑦 ∈ 𝒫 𝒫 𝑥((𝑦 ≠ ∅ ∧ [⊊] Or 𝑦) → ∪ 𝑦 ∈ 𝑦)}"; Finite2},
{"Sets which are not equinumerous to any proper subset. Dedekind finite sets."; "class FinIV"; "⊢ FinIV = {𝑥 ∣ ¬ ∃𝑦(𝑦 ⊊ 𝑥 ∧ 𝑦 ≈ 𝑥)}"; Finite4},
{"Sets which have a power set which is Dedekind finite. Weakly Dedekind finite sets."; "class FinIII"; "⊢ FinIII = {𝑥 ∣ 𝒫 𝑥 ∈ FinIV}"; Finite3},
{"Sets which are empty or strictly dominated by the disjoint union with themselves."; "class FinV"; "⊢ FinV = {𝑥 ∣ (𝑥 = ∅ ∨ 𝑥 ≺ (𝑥 ⊔ 𝑥))}"; Finite5},
{"Sets which are empty, singletons, or strictly dominated by the Cartesian product with themselves."; "class FinVI"; "⊢ FinVI = {𝑥 ∣ (𝑥 ≺ 2o ∨ 𝑥 ≺ (𝑥 × 𝑥))}"; Finite6},
{"Sets which cannot be infinitely well-ordered."; "class FinVII"; "⊢ FinVII = {𝑥 ∣ ¬ ∃𝑦 ∈ (On ∖ ω)𝑥 ≈ 𝑦}"; Finite7},
{"Function Predicate with a Domain."; "wff 𝐴 Fn 𝐵"; "⊢ (𝐴 Fn 𝐵 ↔ (Fun 𝐴 ∧ dom 𝐴 = 𝐵))"; FunWDom},
{"Composition of relations."; "class (𝐴 ∘ 𝐵)"; "⊢ (𝐴 ∘ 𝐵) = {⟨𝑥, 𝑦⟩ ∣ ∃𝑧(𝑥𝐵𝑧 ∧ 𝑧𝐴𝑦)}"; Compose},
{"Predecessor class."; "class Pred(𝑅, 𝐴, 𝑋)"; "⊢ Pred(𝑅, 𝐴, 𝑋) = (𝐴 ∩ (◡𝑅 “ {𝑋}))"; PredecessorCls = 0xF0},
{"Construction of the Complex Numbers:", "Define a set of reals."; "class R"; "⊢ R = ((P × P) / ~R )"; SetTmpReals},
{"Relation predicate."; "wff Rel 𝐴"; "⊢ (Rel 𝐴 ↔ 𝐴 ⊆ (V × V))"; RelationPred},
{"Successor class."; "class suc 𝐴"; "⊢ suc 𝐴 = (𝐴 ∪ {𝐴})"; Successor},
{"Construction of the Complex Numbers:", "Define zero for the temporary reals."; "class 0R"; r"⊢ 0R = \[⟨1P, 1P⟩] ~R"; ZeroTmpReals},
{"Construction of the Complex Numbers:", "Define one for the temporary reals."; "class 1R"; r"⊢ 1R = \[⟨(1P +P 1P), 1P⟩] ~R"; OneTmpReals},
{"Construction of the Complex Numbers:", "Define minus one for the temporary reals."; "class -1R"; r"⊢ -1R = \[⟨1P, (1P +P 1P)⟩] ~R"; MinusOneTmpReals},
{"The well-ordered recursive function generator.", "", "We want 𝑅 to be well-ordered and set-like."; "class wrecs(𝑅, 𝐴, 𝐹)"; "⊢ wrecs(𝑅, 𝐴, 𝐹) = frecs(𝑅, 𝐴, (𝐹 ∘ 2nd ))"; WellOrderRecGen},
{"Construction of the Complex Numbers:", "Define the addition operator for temporary reals."; "class +R"; r"⊢ +R = {⟨⟨𝑥, 𝑦⟩, 𝑧⟩ ∣ ((𝑥 ∈ R ∧ 𝑦 ∈ R) ∧ ∃𝑤∃𝑣∃𝑢∃𝑓((𝑥 = \[⟨𝑤, 𝑣⟩] ~R ∧ 𝑦 = \[⟨𝑢, 𝑓⟩] ~R ) ∧ 𝑧 = \[⟨(𝑤 +P 𝑢), (𝑣 +P 𝑓)⟩] ~R ))}"; AddTmpReals},
{"Construction of the Complex Numbers:", "Define the multiplication operator for temporary reals."; "class ·R"; r"⊢ ·R = {⟨⟨𝑥, 𝑦⟩, 𝑧⟩ ∣ ((𝑥 ∈ R ∧ 𝑦 ∈ R) ∧ ∃𝑤∃𝑣∃𝑢∃𝑓((𝑥 = \[⟨𝑤, 𝑣⟩] ~R ∧ 𝑦 = \[⟨𝑢, 𝑓⟩] ~R ) ∧ 𝑧 = \[⟨((𝑤 ·P 𝑢) +P (𝑣 ·P 𝑓)), ((𝑤 ·P 𝑓) +P (𝑣 ·P 𝑢))⟩] ~R ))}"; MulTmpReals},
{"Construction of the Complex Numbers:", "Define the less-than relation for temporary reals."; "class <R"; r"⊢ <R = {⟨𝑥, 𝑦⟩ ∣ ((𝑥 ∈ R ∧ 𝑦 ∈ R) ∧ ∃𝑧∃𝑤∃𝑣∃𝑢((𝑥 = \[⟨𝑧, 𝑤⟩] ~R ∧ 𝑦 = \[⟨𝑣, 𝑢⟩] ~R ) ∧ (𝑧 +P 𝑢)<P (𝑤 +P 𝑣)))}"; LtTmpReals},
{"Restricted Class Builder."; "class {𝑥 ∈ 𝐴 ∣ 𝜑}"; "⊢ {𝑥 ∈ 𝐴 ∣ 𝜑} = {𝑥 ∣ (𝑥 ∈ 𝐴 ∧ 𝜑)}"; ResClassBuilder},
{"Define positive infinity as an element not in the complex numbers."; "class +∞"; "⊢ +∞ = 𝒫 ∪ ℂ"; PosInfinity},
{"Define the less-than-or-equal relation for the extended reals."; "class ≤"; "⊢ ≤ = ((ℝ* × ℝ*) ∖ ◡ < )"; LessOrEqual},
{"An equivalence relation between sets of the same cardinality."; "class ≈"; "⊢ ≈ = {⟨𝑥, 𝑦⟩ ∣ ∃𝑓 𝑓:𝑥–1-1-onto→𝑦}"; Equinumerous},
{"Define the rationals as a subset of the complex numbers."; "class ℚ"; "⊢ ℚ = ( / “ (ℤ × ℕ))"; Rationals}
}
}

impl NodeByte {
    /// All defined nodes, as enum values.
    ///
    /// # Design Notes
    ///
    /// **Semantic Ordering**: The variants in this array are ordered by their type signatures
    /// and logical relationships, NOT by source code declaration order. This ordering groups
    /// related operations together (e.g., all Boolean nullary operators, then Boolean unary
    /// operators, then Boolean binary operators, etc.).
    ///
    /// **Why Not `strum::VariantArray::VARIANTS`?**: While strum's `VariantArray` derive provides
    /// a `VARIANTS` constant automatically, it uses source declaration order. The [`to_order()`]
    /// method returns indices into this semantically-ordered `ALL_NODES` array, which is essential
    /// for maintaining the mathematical grouping of operations.
    ///
    /// **Complementary Use**: This hand-written array complements strum's `FromRepr` derive,
    /// which we use for O(1) discriminant → enum lookups via [`from_repr()`].
    ///
    /// [`to_order()`]: Self::to_order
    /// [`from_repr()`]: Self::from_repr
    pub const ALL_NODES: [Self; 222] = [
        Self::True,
        Self::False,
        Self::ChoiceAxiomHolds,
        Self::Not,
        Self::TransCls,
        Self::RelationPred,
        Self::OrdinalPred,
        Self::LimitOrdinalPred,
        Self::FunPred,
        Self::SmoFunPred,
        Self::Implies,
        Self::Biimp,
        Self::And,
        Self::Or,
        Self::NotAnd,
        Self::ExclusiveOr,
        Self::NotOr,
        Self::ForAll,
        Self::Exists,
        Self::ExistsAtMostOne,
        Self::ExistsExactlyOne,
        Self::SetNotFreeInWff,
        Self::SetNotFreeInCls,
        Self::Equals,
        Self::IsElementOf,
        Self::NotEquals,
        Self::NotElementOf,
        Self::Subset,
        Self::ProperSubset,
        Self::PartialOrder,
        Self::CompleteOrder,
        Self::WellFounded,
        Self::SetLike,
        Self::WellOrdering,
        Self::FunWDom,
        Self::EquivalenceRelPred,
        Self::And3,
        Self::Or3,
        Self::SumFromAdder,
        Self::CarryFromAdder,
        Self::LogicalIf,
        Self::SubSetInWff,
        Self::CondEq,
        Self::ResForAll,
        Self::ResExists,
        Self::ResExAtMostOne,
        Self::ResExExactlyOne,
        Self::DisjointFamily,
        Self::SubClassInWff,
        Self::BinaryRelation,
        Self::FunWDomAndCodom,
        Self::OneToOneFun,
        Self::OntoFun,
        Self::OneToOneOntoFun,
        Self::RelationIsometry,
        Self::UniversalCls,
        Self::EmptyCls,
        Self::IdentityRelation,
        Self::MembershipRelation,
        Self::Ordinals,
        Self::ProperSubsetRel,
        Self::Omega,
        Self::ExtractFirst,
        Self::ExtractSecond,
        Self::SupportOperator,
        Self::UndefinedFun,
        Self::OrdOne,
        Self::OrdTwo,
        Self::OrdThree,
        Self::OrdFour,
        Self::OrdAdd,
        Self::OrdMult,
        Self::OrdExp,
        Self::OrdNaturalAdd,
        Self::MappingOp,
        Self::PartialMappingOp,
        Self::Equinumerous,
        Self::Dominance,
        Self::StrictDominance,
        Self::FiniteSets,
        Self::FiniteSupport,
        Self::FiniteIntersection,
        Self::HartogsFun,
        Self::WeakDominance,
        Self::CantorNormalForm,
        Self::TransClosureFun,
        Self::CumulativeHierarchy,
        Self::Rank,
        Self::LeftInjection,
        Self::RightInjection,
        Self::Cardinality,
        Self::AlephFun,
        Self::Cofinality,
        Self::Finite1a,
        Self::Finite2,
        Self::Finite4,
        Self::Finite3,
        Self::Finite5,
        Self::Finite6,
        Self::Finite7,
        Self::GenContinuumHyp,
        Self::WeakInaccessibles,
        Self::StrongInaccessibles,
        Self::WeakUnis,
        Self::WeakUniClosure,
        Self::TarskiClasses,
        Self::GrothendieckUnis,
        Self::TarskiClassClosure,
        Self::SetPosInts,
        Self::AddPosInts,
        Self::MulPosInts,
        Self::LtPosInts,
        Self::AddPosFracs,
        Self::MulPosFracs,
        Self::LtPosFracs,
        Self::EqPosFracs,
        Self::SetPosRats,
        Self::OnePosRats,
        Self::ReducePosRats,
        Self::AddPosRats,
        Self::MulPosRats,
        Self::InvPosRats,
        Self::LtPosRats,
        Self::SetPosReals,
        Self::OnePosReals,
        Self::AddPosReals,
        Self::MulPosReals,
        Self::LtPosReals,
        Self::EqTmpReals,
        Self::SetTmpReals,
        Self::ZeroTmpReals,
        Self::OneTmpReals,
        Self::MinusOneTmpReals,
        Self::AddTmpReals,
        Self::MulTmpReals,
        Self::LtTmpReals,
        Self::ComplexNumbers,
        Self::RealNumbers,
        Self::Zero,
        Self::One,
        Self::SqrtMinusOne,
        Self::Addition,
        Self::LtReals,
        Self::Multiplication,
        Self::PosInfinity,
        Self::NegInfinity,
        Self::ExtendedReals,
        Self::LessThan,
        Self::LessOrEqual,
        Self::Subtraction,
        Self::Division,
        Self::PositiveIntegers,
        Self::Two,
        Self::Three,
        Self::Four,
        Self::Five,
        Self::Six,
        Self::Seven,
        Self::Eight,
        Self::Nine,
        Self::NonnegativeIntegers,
        Self::ExtendedNonnegInts,
        Self::Integers,
        Self::UpperIntegers,
        Self::Rationals,
        Self::PositiveReals,
        Self::PowerCls,
        Self::Singleton,
        Self::ClassUnion,
        Self::ClassIntersection,
        Self::Converse,
        Self::Domain,
        Self::Range,
        Self::Successor,
        Self::OperatorToFuns,
        Self::RelationToFuns,
        Self::FunTranspose,
        Self::Curry,
        Self::Uncurry,
        Self::StrongTfinRecGen,
        Self::TransClassClosure,
        Self::LocalAxiomChoice,
        Self::UnaryMinus,
        Self::ClassBuilder,
        Self::Iota,
        Self::DiffOp,
        Self::UnionOp,
        Self::IntersectionOp,
        Self::SymDiffOp,
        Self::UnorderdPair,
        Self::OrderedPair,
        Self::CartesianProduct,
        Self::Restriction,
        Self::Image,
        Self::Compose,
        Self::ApplyFun,
        Self::RecursiveGenerator,
        Self::IndexAwareRecGen,
        Self::EquivalenceCls,
        Self::QuotientSets,
        Self::OrdinalIsomorphism,
        Self::DisjointUnion,
        Self::DecimalConstructor,
        Self::ClassIf,
        Self::OrdPairsBuilder,
        Self::ResClassBuilder,
        Self::ResIota,
        Self::IndexedUnion,
        Self::IndexedIntersection,
        Self::MapsTo,
        Self::IndexedCartProduct,
        Self::SubClassInCls,
        Self::UnorderdTriple,
        Self::OrderedTriple,
        Self::PredecessorCls,
        Self::ApplyOperator,
        Self::WellFoundRecGen,
        Self::WellOrderRecGen,
        Self::Supremum,
        Self::Infimum,
        Self::OperatorBuilder,
        Self::OperatorMapsTo,
    ];

    /// All defined nodes, as bytes.
    pub const ALL_NODE_BYTES: [u8; 222] = [
        Self::True as u8,
        Self::False as u8,
        Self::ChoiceAxiomHolds as u8,
        Self::Not as u8,
        Self::TransCls as u8,
        Self::RelationPred as u8,
        Self::OrdinalPred as u8,
        Self::LimitOrdinalPred as u8,
        Self::FunPred as u8,
        Self::SmoFunPred as u8,
        Self::Implies as u8,
        Self::Biimp as u8,
        Self::And as u8,
        Self::Or as u8,
        Self::NotAnd as u8,
        Self::ExclusiveOr as u8,
        Self::NotOr as u8,
        Self::ForAll as u8,
        Self::Exists as u8,
        Self::ExistsAtMostOne as u8,
        Self::ExistsExactlyOne as u8,
        Self::SetNotFreeInWff as u8,
        Self::SetNotFreeInCls as u8,
        Self::Equals as u8,
        Self::IsElementOf as u8,
        Self::NotEquals as u8,
        Self::NotElementOf as u8,
        Self::Subset as u8,
        Self::ProperSubset as u8,
        Self::PartialOrder as u8,
        Self::CompleteOrder as u8,
        Self::WellFounded as u8,
        Self::SetLike as u8,
        Self::WellOrdering as u8,
        Self::FunWDom as u8,
        Self::EquivalenceRelPred as u8,
        Self::And3 as u8,
        Self::Or3 as u8,
        Self::SumFromAdder as u8,
        Self::CarryFromAdder as u8,
        Self::LogicalIf as u8,
        Self::SubSetInWff as u8,
        Self::CondEq as u8,
        Self::ResForAll as u8,
        Self::ResExists as u8,
        Self::ResExAtMostOne as u8,
        Self::ResExExactlyOne as u8,
        Self::DisjointFamily as u8,
        Self::SubClassInWff as u8,
        Self::BinaryRelation as u8,
        Self::FunWDomAndCodom as u8,
        Self::OneToOneFun as u8,
        Self::OntoFun as u8,
        Self::OneToOneOntoFun as u8,
        Self::RelationIsometry as u8,
        Self::UniversalCls as u8,
        Self::EmptyCls as u8,
        Self::IdentityRelation as u8,
        Self::MembershipRelation as u8,
        Self::Ordinals as u8,
        Self::ProperSubsetRel as u8,
        Self::Omega as u8,
        Self::ExtractFirst as u8,
        Self::ExtractSecond as u8,
        Self::SupportOperator as u8,
        Self::UndefinedFun as u8,
        Self::OrdOne as u8,
        Self::OrdTwo as u8,
        Self::OrdThree as u8,
        Self::OrdFour as u8,
        Self::OrdAdd as u8,
        Self::OrdMult as u8,
        Self::OrdExp as u8,
        Self::OrdNaturalAdd as u8,
        Self::MappingOp as u8,
        Self::PartialMappingOp as u8,
        Self::Equinumerous as u8,
        Self::Dominance as u8,
        Self::StrictDominance as u8,
        Self::FiniteSets as u8,
        Self::FiniteSupport as u8,
        Self::FiniteIntersection as u8,
        Self::HartogsFun as u8,
        Self::WeakDominance as u8,
        Self::CantorNormalForm as u8,
        Self::TransClosureFun as u8,
        Self::CumulativeHierarchy as u8,
        Self::Rank as u8,
        Self::LeftInjection as u8,
        Self::RightInjection as u8,
        Self::Cardinality as u8,
        Self::AlephFun as u8,
        Self::Cofinality as u8,
        Self::Finite1a as u8,
        Self::Finite2 as u8,
        Self::Finite4 as u8,
        Self::Finite3 as u8,
        Self::Finite5 as u8,
        Self::Finite6 as u8,
        Self::Finite7 as u8,
        Self::GenContinuumHyp as u8,
        Self::WeakInaccessibles as u8,
        Self::StrongInaccessibles as u8,
        Self::WeakUnis as u8,
        Self::WeakUniClosure as u8,
        Self::TarskiClasses as u8,
        Self::GrothendieckUnis as u8,
        Self::TarskiClassClosure as u8,
        Self::SetPosInts as u8,
        Self::AddPosInts as u8,
        Self::MulPosInts as u8,
        Self::LtPosInts as u8,
        Self::AddPosFracs as u8,
        Self::MulPosFracs as u8,
        Self::LtPosFracs as u8,
        Self::EqPosFracs as u8,
        Self::SetPosRats as u8,
        Self::OnePosRats as u8,
        Self::ReducePosRats as u8,
        Self::AddPosRats as u8,
        Self::MulPosRats as u8,
        Self::InvPosRats as u8,
        Self::LtPosRats as u8,
        Self::SetPosReals as u8,
        Self::OnePosReals as u8,
        Self::AddPosReals as u8,
        Self::MulPosReals as u8,
        Self::LtPosReals as u8,
        Self::EqTmpReals as u8,
        Self::SetTmpReals as u8,
        Self::ZeroTmpReals as u8,
        Self::OneTmpReals as u8,
        Self::MinusOneTmpReals as u8,
        Self::AddTmpReals as u8,
        Self::MulTmpReals as u8,
        Self::LtTmpReals as u8,
        Self::ComplexNumbers as u8,
        Self::RealNumbers as u8,
        Self::Zero as u8,
        Self::One as u8,
        Self::SqrtMinusOne as u8,
        Self::Addition as u8,
        Self::LtReals as u8,
        Self::Multiplication as u8,
        Self::PosInfinity as u8,
        Self::NegInfinity as u8,
        Self::ExtendedReals as u8,
        Self::LessThan as u8,
        Self::LessOrEqual as u8,
        Self::Subtraction as u8,
        Self::Division as u8,
        Self::PositiveIntegers as u8,
        Self::Two as u8,
        Self::Three as u8,
        Self::Four as u8,
        Self::Five as u8,
        Self::Six as u8,
        Self::Seven as u8,
        Self::Eight as u8,
        Self::Nine as u8,
        Self::NonnegativeIntegers as u8,
        Self::ExtendedNonnegInts as u8,
        Self::Integers as u8,
        Self::UpperIntegers as u8,
        Self::Rationals as u8,
        Self::PositiveReals as u8,
        Self::PowerCls as u8,
        Self::Singleton as u8,
        Self::ClassUnion as u8,
        Self::ClassIntersection as u8,
        Self::Converse as u8,
        Self::Domain as u8,
        Self::Range as u8,
        Self::Successor as u8,
        Self::OperatorToFuns as u8,
        Self::RelationToFuns as u8,
        Self::FunTranspose as u8,
        Self::Curry as u8,
        Self::Uncurry as u8,
        Self::StrongTfinRecGen as u8,
        Self::TransClassClosure as u8,
        Self::LocalAxiomChoice as u8,
        Self::UnaryMinus as u8,
        Self::ClassBuilder as u8,
        Self::Iota as u8,
        Self::DiffOp as u8,
        Self::UnionOp as u8,
        Self::IntersectionOp as u8,
        Self::SymDiffOp as u8,
        Self::UnorderdPair as u8,
        Self::OrderedPair as u8,
        Self::CartesianProduct as u8,
        Self::Restriction as u8,
        Self::Image as u8,
        Self::Compose as u8,
        Self::ApplyFun as u8,
        Self::RecursiveGenerator as u8,
        Self::IndexAwareRecGen as u8,
        Self::EquivalenceCls as u8,
        Self::QuotientSets as u8,
        Self::OrdinalIsomorphism as u8,
        Self::DisjointUnion as u8,
        Self::DecimalConstructor as u8,
        Self::ClassIf as u8,
        Self::OrdPairsBuilder as u8,
        Self::ResClassBuilder as u8,
        Self::ResIota as u8,
        Self::IndexedUnion as u8,
        Self::IndexedIntersection as u8,
        Self::MapsTo as u8,
        Self::IndexedCartProduct as u8,
        Self::SubClassInCls as u8,
        Self::UnorderdTriple as u8,
        Self::OrderedTriple as u8,
        Self::PredecessorCls as u8,
        Self::ApplyOperator as u8,
        Self::WellFoundRecGen as u8,
        Self::WellOrderRecGen as u8,
        Self::Supremum as u8,
        Self::Infimum as u8,
        Self::OperatorBuilder as u8,
        Self::OperatorMapsTo as u8,
    ];

    /// Return index of this value in [`ALL_NODES`].
    ///
    /// [`ALL_NODES`]: Self::ALL_NODES
    #[must_use]
    pub fn to_order(self) -> u8 {
        use NodeByte::*;
        match self {
            True => 0,
            False => 1,
            ChoiceAxiomHolds => 2,
            Not => 3,
            TransCls => 4,
            RelationPred => 5,
            OrdinalPred => 6,
            LimitOrdinalPred => 7,
            FunPred => 8,
            SmoFunPred => 9,
            Implies => 10,
            Biimp => 11,
            And => 12,
            Or => 13,
            NotAnd => 14,
            ExclusiveOr => 15,
            NotOr => 16,
            ForAll => 17,
            Exists => 18,
            ExistsAtMostOne => 19,
            ExistsExactlyOne => 20,
            SetNotFreeInWff => 21,
            SetNotFreeInCls => 22,
            Equals => 23,
            IsElementOf => 24,
            NotEquals => 25,
            NotElementOf => 26,
            Subset => 27,
            ProperSubset => 28,
            PartialOrder => 29,
            CompleteOrder => 30,
            WellFounded => 31,
            SetLike => 32,
            WellOrdering => 33,
            FunWDom => 34,
            EquivalenceRelPred => 35,
            And3 => 36,
            Or3 => 37,
            SumFromAdder => 38,
            CarryFromAdder => 39,
            LogicalIf => 40,
            SubSetInWff => 41,
            CondEq => 42,
            ResForAll => 43,
            ResExists => 44,
            ResExAtMostOne => 45,
            ResExExactlyOne => 46,
            DisjointFamily => 47,
            SubClassInWff => 48,
            BinaryRelation => 49,
            FunWDomAndCodom => 50,
            OneToOneFun => 51,
            OntoFun => 52,
            OneToOneOntoFun => 53,
            RelationIsometry => 54,
            UniversalCls => 55,
            EmptyCls => 56,
            IdentityRelation => 57,
            MembershipRelation => 58,
            Ordinals => 59,
            ProperSubsetRel => 60,
            Omega => 61,
            ExtractFirst => 62,
            ExtractSecond => 63,
            SupportOperator => 64,
            UndefinedFun => 65,
            OrdOne => 66,
            OrdTwo => 67,
            OrdThree => 68,
            OrdFour => 69,
            OrdAdd => 70,
            OrdMult => 71,
            OrdExp => 72,
            OrdNaturalAdd => 73,
            MappingOp => 74,
            PartialMappingOp => 75,
            Equinumerous => 76,
            Dominance => 77,
            StrictDominance => 78,
            FiniteSets => 79,
            FiniteSupport => 80,
            FiniteIntersection => 81,
            HartogsFun => 82,
            WeakDominance => 83,
            CantorNormalForm => 84,
            TransClosureFun => 85,
            CumulativeHierarchy => 86,
            Rank => 87,
            LeftInjection => 88,
            RightInjection => 89,
            Cardinality => 90,
            AlephFun => 91,
            Cofinality => 92,
            Finite1a => 93,
            Finite2 => 94,
            Finite4 => 95,
            Finite3 => 96,
            Finite5 => 97,
            Finite6 => 98,
            Finite7 => 99,
            GenContinuumHyp => 100,
            WeakInaccessibles => 101,
            StrongInaccessibles => 102,
            WeakUnis => 103,
            WeakUniClosure => 104,
            TarskiClasses => 105,
            GrothendieckUnis => 106,
            TarskiClassClosure => 107,
            SetPosInts => 108,
            AddPosInts => 109,
            MulPosInts => 110,
            LtPosInts => 111,
            AddPosFracs => 112,
            MulPosFracs => 113,
            LtPosFracs => 114,
            EqPosFracs => 115,
            SetPosRats => 116,
            OnePosRats => 117,
            ReducePosRats => 118,
            AddPosRats => 119,
            MulPosRats => 120,
            InvPosRats => 121,
            LtPosRats => 122,
            SetPosReals => 123,
            OnePosReals => 124,
            AddPosReals => 125,
            MulPosReals => 126,
            LtPosReals => 127,
            EqTmpReals => 128,
            SetTmpReals => 129,
            ZeroTmpReals => 130,
            OneTmpReals => 131,
            MinusOneTmpReals => 132,
            AddTmpReals => 133,
            MulTmpReals => 134,
            LtTmpReals => 135,
            ComplexNumbers => 136,
            RealNumbers => 137,
            Zero => 138,
            One => 139,
            SqrtMinusOne => 140,
            Addition => 141,
            LtReals => 142,
            Multiplication => 143,
            PosInfinity => 144,
            NegInfinity => 145,
            ExtendedReals => 146,
            LessThan => 147,
            LessOrEqual => 148,
            Subtraction => 149,
            Division => 150,
            PositiveIntegers => 151,
            Two => 152,
            Three => 153,
            Four => 154,
            Five => 155,
            Six => 156,
            Seven => 157,
            Eight => 158,
            Nine => 159,
            NonnegativeIntegers => 160,
            ExtendedNonnegInts => 161,
            Integers => 162,
            UpperIntegers => 163,
            Rationals => 164,
            PositiveReals => 165,
            PowerCls => 166,
            Singleton => 167,
            ClassUnion => 168,
            ClassIntersection => 169,
            Converse => 170,
            Domain => 171,
            Range => 172,
            Successor => 173,
            OperatorToFuns => 174,
            RelationToFuns => 175,
            FunTranspose => 176,
            Curry => 177,
            Uncurry => 178,
            StrongTfinRecGen => 179,
            TransClassClosure => 180,
            LocalAxiomChoice => 181,
            UnaryMinus => 182,
            ClassBuilder => 183,
            Iota => 184,
            DiffOp => 185,
            UnionOp => 186,
            IntersectionOp => 187,
            SymDiffOp => 188,
            UnorderdPair => 189,
            OrderedPair => 190,
            CartesianProduct => 191,
            Restriction => 192,
            Image => 193,
            Compose => 194,
            ApplyFun => 195,
            RecursiveGenerator => 196,
            IndexAwareRecGen => 197,
            EquivalenceCls => 198,
            QuotientSets => 199,
            OrdinalIsomorphism => 200,
            DisjointUnion => 201,
            DecimalConstructor => 202,
            ClassIf => 203,
            OrdPairsBuilder => 204,
            ResClassBuilder => 205,
            ResIota => 206,
            IndexedUnion => 207,
            IndexedIntersection => 208,
            MapsTo => 209,
            IndexedCartProduct => 210,
            SubClassInCls => 211,
            UnorderdTriple => 212,
            OrderedTriple => 213,
            PredecessorCls => 214,
            ApplyOperator => 215,
            WellFoundRecGen => 216,
            WellOrderRecGen => 217,
            Supremum => 218,
            Infimum => 219,
            OperatorBuilder => 220,
            OperatorMapsTo => 221,
        }
    }

    /// Convenience method to extract just the type from the value of [`NodeByte`].
    #[must_use]
    pub fn to_type(self) -> SimpleType {
        use NodeByte::*;
        use SimpleType::*;
        match self {
            True | False | ChoiceAxiomHolds | Not | TransCls | RelationPred | OrdinalPred
            | LimitOrdinalPred | FunPred | SmoFunPred | Implies | Biimp | And | Or | NotAnd
            | ExclusiveOr | NotOr | ForAll | Exists | ExistsAtMostOne | ExistsExactlyOne
            | SetNotFreeInWff | SetNotFreeInCls | Equals | IsElementOf | NotEquals
            | NotElementOf | Subset | ProperSubset | PartialOrder | CompleteOrder | WellFounded
            | SetLike | WellOrdering | FunWDom | EquivalenceRelPred | And3 | Or3 | SumFromAdder
            | CarryFromAdder | LogicalIf | SubSetInWff | CondEq | ResForAll | ResExists
            | ResExAtMostOne | ResExExactlyOne | DisjointFamily | SubClassInWff
            | BinaryRelation | FunWDomAndCodom | OneToOneFun | OntoFun | OneToOneOntoFun
            | RelationIsometry => Boolean,

            UniversalCls | EmptyCls | IdentityRelation | MembershipRelation | Ordinals
            | ProperSubsetRel | Omega | ExtractFirst | ExtractSecond | SupportOperator
            | UndefinedFun | OrdOne | OrdTwo | OrdThree | OrdFour | OrdAdd | OrdMult | OrdExp
            | OrdNaturalAdd | MappingOp | PartialMappingOp | Equinumerous | Dominance
            | StrictDominance | FiniteSets | FiniteSupport | FiniteIntersection | HartogsFun
            | WeakDominance | CantorNormalForm | TransClosureFun | CumulativeHierarchy | Rank
            | LeftInjection | RightInjection | Cardinality | AlephFun | Cofinality | Finite1a
            | Finite2 | Finite4 | Finite3 | Finite5 | Finite6 | Finite7 | GenContinuumHyp
            | WeakInaccessibles | StrongInaccessibles | WeakUnis | WeakUniClosure
            | TarskiClasses | GrothendieckUnis | TarskiClassClosure | SetPosInts | AddPosInts
            | MulPosInts | LtPosInts | AddPosFracs | MulPosFracs | LtPosFracs | EqPosFracs
            | SetPosRats | OnePosRats | ReducePosRats | AddPosRats | MulPosRats | InvPosRats
            | LtPosRats | SetPosReals | OnePosReals | AddPosReals | MulPosReals | LtPosReals
            | EqTmpReals | SetTmpReals | ZeroTmpReals | OneTmpReals | MinusOneTmpReals
            | AddTmpReals | MulTmpReals | LtTmpReals | ComplexNumbers | RealNumbers | Zero
            | One | SqrtMinusOne | Addition | LtReals | Multiplication | PosInfinity
            | NegInfinity | ExtendedReals | LessThan | LessOrEqual | Subtraction | Division
            | PositiveIntegers | Two | Three | Four | Five | Six | Seven | Eight | Nine
            | NonnegativeIntegers | ExtendedNonnegInts | Integers | UpperIntegers | Rationals
            | PositiveReals | PowerCls | Singleton | ClassUnion | ClassIntersection | Converse
            | Domain | Range | Successor | OperatorToFuns | RelationToFuns | FunTranspose
            | Curry | Uncurry | StrongTfinRecGen | TransClassClosure | LocalAxiomChoice
            | UnaryMinus | ClassBuilder | Iota | DiffOp | UnionOp | IntersectionOp | SymDiffOp
            | UnorderdPair | OrderedPair | CartesianProduct | Restriction | Image | Compose
            | ApplyFun | RecursiveGenerator | IndexAwareRecGen | EquivalenceCls | QuotientSets
            | OrdinalIsomorphism | DisjointUnion | DecimalConstructor | ClassIf
            | OrdPairsBuilder | ResClassBuilder | ResIota | IndexedUnion | IndexedIntersection
            | MapsTo | IndexedCartProduct | SubClassInCls | UnorderdTriple | OrderedTriple
            | PredecessorCls | ApplyOperator | WellFoundRecGen | WellOrderRecGen | Supremum
            | Infimum | OperatorBuilder | OperatorMapsTo => Class,
        }
    }

    /// Convenience method to extract an arbitrary number of slot TYPEs from the value of [`NodeByte`].
    #[must_use]
    pub fn to_slots(self) -> &'static [SimpleType] {
        use NodeByte::*;
        use SimpleType::*;
        match self {
            True | False | ChoiceAxiomHolds | UniversalCls | EmptyCls | IdentityRelation
            | MembershipRelation | Ordinals | ProperSubsetRel | Omega | ExtractFirst
            | ExtractSecond | SupportOperator | UndefinedFun | OrdOne | OrdTwo | OrdThree
            | OrdFour | OrdAdd | OrdMult | OrdExp | OrdNaturalAdd | MappingOp
            | PartialMappingOp | Equinumerous | Dominance | StrictDominance | FiniteSets
            | FiniteSupport | FiniteIntersection | HartogsFun | WeakDominance
            | CantorNormalForm | TransClosureFun | CumulativeHierarchy | Rank | LeftInjection
            | RightInjection | Cardinality | AlephFun | Cofinality | Finite1a | Finite2
            | Finite4 | Finite3 | Finite5 | Finite6 | Finite7 | GenContinuumHyp
            | WeakInaccessibles | StrongInaccessibles | WeakUnis | WeakUniClosure
            | TarskiClasses | GrothendieckUnis | TarskiClassClosure | SetPosInts | AddPosInts
            | MulPosInts | LtPosInts | AddPosFracs | MulPosFracs | LtPosFracs | EqPosFracs
            | SetPosRats | OnePosRats | ReducePosRats | AddPosRats | MulPosRats | InvPosRats
            | LtPosRats | SetPosReals | OnePosReals | AddPosReals | MulPosReals | LtPosReals
            | EqTmpReals | SetTmpReals | ZeroTmpReals | OneTmpReals | MinusOneTmpReals
            | AddTmpReals | MulTmpReals | LtTmpReals | ComplexNumbers | RealNumbers | Zero
            | One | SqrtMinusOne | Addition | LtReals | Multiplication | PosInfinity
            | NegInfinity | ExtendedReals | LessThan | LessOrEqual | Subtraction | Division
            | PositiveIntegers | Two | Three | Four | Five | Six | Seven | Eight | Nine
            | NonnegativeIntegers | ExtendedNonnegInts | Integers | UpperIntegers | Rationals
            | PositiveReals => &[],

            Not => &[Boolean],

            TransCls | RelationPred | OrdinalPred | LimitOrdinalPred | FunPred | SmoFunPred
            | PowerCls | Singleton | ClassUnion | ClassIntersection | Converse | Domain | Range
            | Successor | OperatorToFuns | RelationToFuns | FunTranspose | Curry | Uncurry
            | StrongTfinRecGen | TransClassClosure | LocalAxiomChoice | UnaryMinus => &[Class],

            Implies | Biimp | And | Or | NotAnd | ExclusiveOr | NotOr => &[Boolean, Boolean],

            ForAll | Exists | ExistsAtMostOne | ExistsExactlyOne | SetNotFreeInWff
            | ClassBuilder | Iota => &[Setvar, Boolean],

            SetNotFreeInCls => &[Setvar, Class],

            Equals | IsElementOf | NotEquals | NotElementOf | Subset | ProperSubset
            | PartialOrder | CompleteOrder | WellFounded | SetLike | WellOrdering | FunWDom
            | EquivalenceRelPred | DiffOp | UnionOp | IntersectionOp | SymDiffOp | UnorderdPair
            | OrderedPair | CartesianProduct | Restriction | Image | Compose | ApplyFun
            | RecursiveGenerator | IndexAwareRecGen | EquivalenceCls | QuotientSets
            | OrdinalIsomorphism | DisjointUnion | DecimalConstructor => &[Class, Class],

            And3 | Or3 | SumFromAdder | CarryFromAdder | LogicalIf => &[Boolean, Boolean, Boolean],

            ClassIf => &[Boolean, Class, Class],

            SubSetInWff | CondEq | OrdPairsBuilder => &[Setvar, Setvar, Boolean],

            ResForAll | ResExists | ResExAtMostOne | ResExExactlyOne | ResClassBuilder
            | ResIota => &[Setvar, Class, Boolean],

            DisjointFamily | IndexedUnion | IndexedIntersection | MapsTo | IndexedCartProduct => {
                &[Setvar, Class, Class]
            }

            SubClassInWff => &[Class, Setvar, Boolean],

            SubClassInCls => &[Class, Setvar, Class],

            BinaryRelation | FunWDomAndCodom | OneToOneFun | OntoFun | OneToOneOntoFun
            | UnorderdTriple | OrderedTriple | PredecessorCls | ApplyOperator | WellFoundRecGen
            | WellOrderRecGen | Supremum | Infimum => &[Class, Class, Class],

            OperatorBuilder => &[Setvar, Setvar, Setvar, Boolean],

            OperatorMapsTo => &[Setvar, Class, Setvar, Class, Class],

            RelationIsometry => &[Class, Class, Class, Class, Class],
        }
    }

    /// Return the display symbol/operator for this node.
    ///
    /// This returns the core symbol or operator name used when displaying the node.
    /// The actual formatting pattern is determined by the number and types of children.
    ///
    /// For nodes that don't have a simple symbol representation, returns `None`.
    #[must_use]
    pub const fn display_symbol(self) -> Option<&'static str> {
        use NodeByte::*;
        match self {
            // Nullary constants
            True => Some("⊤"),
            False => Some("⊥"),
            ChoiceAxiomHolds => Some("CHOICE"),
            UniversalCls => Some("V"),
            EmptyCls => Some("∅"),
            IdentityRelation => Some("I"),
            MembershipRelation => Some("E"),
            Ordinals => Some("On"),
            ProperSubsetRel => Some("[⊊]"),
            Omega => Some("ω"),
            ExtractFirst => Some("1st"),
            ExtractSecond => Some("2nd"),
            SupportOperator => Some("supp"),
            UndefinedFun => Some("Undef"),
            OrdOne => Some("1o"),
            OrdTwo => Some("2o"),
            OrdThree => Some("3o"),
            OrdFour => Some("4o"),
            OrdAdd => Some("+o"),
            OrdMult => Some("·o"),
            OrdExp => Some("↑o"),
            OrdNaturalAdd => Some("+no"),
            MappingOp => Some("↑m"),
            PartialMappingOp => Some("↑pm"),
            Equinumerous => Some("≈"),
            Dominance => Some("≼"),
            StrictDominance => Some("≺"),
            FiniteSets => Some("Fin"),
            FiniteSupport => Some("finSupp"),
            FiniteIntersection => Some("fi"),
            HartogsFun => Some("har"),
            WeakDominance => Some("≼*"),
            CantorNormalForm => Some("CNF"),
            TransClosureFun => Some("TC"),
            CumulativeHierarchy => Some("𝑅1"),
            Rank => Some("rank"),
            LeftInjection => Some("inl"),
            RightInjection => Some("inr"),
            Cardinality => Some("card"),
            AlephFun => Some("ℵ"),
            Cofinality => Some("cf"),
            Finite1a => Some("FinIa"),
            Finite2 => Some("FinII"),
            Finite4 => Some("FinIV"),
            Finite3 => Some("FinIII"),
            Finite5 => Some("FinV"),
            Finite6 => Some("FinVI"),
            Finite7 => Some("FinVII"),
            GenContinuumHyp => Some("GCH"),
            WeakInaccessibles => Some("Inaccw"),
            StrongInaccessibles => Some("Inacc"),
            WeakUnis => Some("WUni"),
            WeakUniClosure => Some("wUniCl"),
            TarskiClasses => Some("Tarski"),
            GrothendieckUnis => Some("Univ"),
            TarskiClassClosure => Some("tarskiMap"),
            SetPosInts => Some("N"),
            AddPosInts => Some("+N"),
            MulPosInts => Some("·N"),
            LtPosInts => Some("<N"),
            AddPosFracs => Some("+pQ"),
            MulPosFracs => Some("·pQ"),
            LtPosFracs => Some("<pQ"),
            EqPosFracs => Some("~Q"),
            SetPosRats => Some("Q"),
            OnePosRats => Some("1Q"),
            ReducePosRats => Some("[Q]"),
            AddPosRats => Some("+Q"),
            MulPosRats => Some("·Q"),
            InvPosRats => Some("*Q"),
            LtPosRats => Some("<Q"),
            SetPosReals => Some("P"),
            OnePosReals => Some("1P"),
            AddPosReals => Some("+P"),
            MulPosReals => Some("·P"),
            LtPosReals => Some("<P"),
            EqTmpReals => Some("~R"),
            SetTmpReals => Some("R"),
            ZeroTmpReals => Some("0R"),
            OneTmpReals => Some("1R"),
            MinusOneTmpReals => Some("-1R"),
            AddTmpReals => Some("+R"),
            MulTmpReals => Some("·R"),
            LtTmpReals => Some("<R"),
            ComplexNumbers => Some("ℂ"),
            RealNumbers => Some("ℝ"),
            Zero => Some("0"),
            One => Some("1"),
            SqrtMinusOne => Some("i"),
            Addition => Some("+"),
            LtReals => Some("<ℝ"),
            Multiplication => Some("·"),
            PosInfinity => Some("+∞"),
            NegInfinity => Some("-∞"),
            ExtendedReals => Some("ℝ*"),
            LessThan => Some("<"),
            LessOrEqual => Some("≤"),
            Subtraction => Some("−"),
            Division => Some("/"),
            PositiveIntegers => Some("ℕ"),
            Two => Some("2"),
            Three => Some("3"),
            Four => Some("4"),
            Five => Some("5"),
            Six => Some("6"),
            Seven => Some("7"),
            Eight => Some("8"),
            Nine => Some("9"),
            NonnegativeIntegers => Some("ℕ0"),
            ExtendedNonnegInts => Some("ℕ0*"),
            Integers => Some("ℤ"),
            UpperIntegers => Some("ℤ≥"),
            Rationals => Some("ℚ"),
            PositiveReals => Some("ℝ+"),

            // Unary operators
            Not => Some("¬"),
            TransCls => Some("Tr"),
            RelationPred => Some("Rel"),
            OrdinalPred => Some("Ord"),
            LimitOrdinalPred => Some("Lim"),
            FunPred => Some("Fun"),
            SmoFunPred => Some("Smo"),
            PowerCls => Some("𝒫"),
            ClassUnion => Some("∪"),
            ClassIntersection => Some("∩"),
            Converse => Some("◡"),
            Domain => Some("dom"),
            Range => Some("ran"),
            Successor => Some("suc"),
            OperatorToFuns => Some("∘f"),
            RelationToFuns => Some("∘r"),
            FunTranspose => Some("tpos"),
            Curry => Some("curry"),
            Uncurry => Some("uncurry"),
            StrongTfinRecGen => Some("recs"),
            TransClassClosure => Some("t++"),
            LocalAxiomChoice => Some("AC"),
            UnaryMinus => Some("-"),

            // Binary operators (infix or function-like)
            Implies => Some("→"),
            Biimp => Some("↔"),
            And => Some("∧"),
            Or => Some("∨"),
            NotAnd => Some("⊼"),
            ExclusiveOr => Some("⊻"),
            NotOr => Some("⊽"),
            Equals => Some("="),
            IsElementOf => Some("∈"),
            NotEquals => Some("≠"),
            NotElementOf => Some("∉"),
            Subset => Some("⊆"),
            ProperSubset => Some("⊊"),
            PartialOrder => Some("Po"),
            CompleteOrder => Some("Or"),
            WellFounded => Some("Fr"),
            SetLike => Some("Se"),
            WellOrdering => Some("We"),
            FunWDom => Some("Fn"),
            EquivalenceRelPred => Some("Er"),
            DiffOp => Some("∖"),
            UnionOp => Some("∪"),
            IntersectionOp => Some("∩"),
            SymDiffOp => Some("△"),
            CartesianProduct => Some("×"),
            Restriction => Some("↾"),
            Compose => Some("∘"),
            DisjointUnion => Some("⊔"),
            RecursiveGenerator => Some("rec"),
            IndexAwareRecGen => Some("seqω"),
            OrdinalIsomorphism => Some("OrdIso"),

            // Quantifiers
            ForAll => Some("∀"),
            Exists => Some("∃"),
            ExistsAtMostOne => Some("∃*"),
            ExistsExactlyOne => Some("∃!"),
            SetNotFreeInWff => Some("Ⅎ"),
            SetNotFreeInCls => Some("Ⅎ"),
            Iota => Some("℩"),
            ResForAll => Some("∀"),
            ResExists => Some("∃"),
            ResExAtMostOne => Some("∃*"),
            ResExExactlyOne => Some("∃!"),
            ResIota => Some("℩"),

            // Ternary and higher operators
            And3 => Some("∧"),
            Or3 => Some("∨"),
            SumFromAdder => Some("hadd"),
            CarryFromAdder => Some("cadd"),
            LogicalIf => Some("if-"),
            CondEq => Some("CondEq"),
            DisjointFamily => Some("Disj"),
            IndexedUnion => Some("∪"),
            IndexedIntersection => Some("∩"),
            IndexedCartProduct => Some("X"),
            PredecessorCls => Some("Pred"),
            WellFoundRecGen => Some("frecs"),
            WellOrderRecGen => Some("wrecs"),
            Supremum => Some("sup"),
            Infimum => Some("inf"),
            ClassIf => Some("if"),
            RelationIsometry => Some("Isom"),

            // Special cases that need custom formatting - return None
            Singleton | UnorderdPair | UnorderdTriple => None,
            OrderedPair | OrderedTriple => None,
            Image | ApplyFun | EquivalenceCls | QuotientSets | DecimalConstructor => None,
            ClassBuilder | OrdPairsBuilder | ResClassBuilder | OperatorBuilder => None,
            SubSetInWff | SubClassInWff | SubClassInCls => None,
            BinaryRelation | FunWDomAndCodom | OneToOneFun | OntoFun | OneToOneOntoFun => None,
            ApplyOperator | MapsTo | OperatorMapsTo => None,
        }
    }

    /// Return an iterator over legal value of [`NodeByte`].
    pub fn enumerate() -> impl Iterator<Item = Self> {
        Self::ALL_NODES.iter().copied()
    }

    /// NODEs are effectively ordered triples of an index, a TYPE, and
    /// an arbitrary number of slot TYPEs.
    ///
    /// # Errors
    ///
    /// None, as enums can't be malformed.
    pub fn get_index_type_and_slots(&self) -> Result<(usize, SimpleType, &[SimpleType]), MguError> {
        let code = *self as u8 as usize;
        let my_type = self.to_type();
        let slots = self.to_slots();
        Ok((code, my_type, slots))
    }
}

impl Node for NodeByte {
    type Type = SimpleType;

    fn get_type_and_index(&self) -> Result<(Self::Type, usize), MguError> {
        Ok((self.to_type(), self.to_order() as usize))
    }

    fn get_arity(&self) -> Result<usize, MguError> {
        Ok(self.to_slots().len())
    }

    fn get_slot_type(&self, index: usize) -> Result<Self::Type, MguError> {
        let slice = self.to_slots();
        let n = slice.len();
        if index < n {
            Ok(slice[index])
        } else {
            Err(MguError::from_index_and_len(index, n))
        }
    }

    fn to_boolean_op(&self) -> Option<BooleanSimpleOp> {
        use BooleanSimpleOp::*;
        match self {
            // Nullary (0-arity) Boolean operations
            NodeByte::False => Some(False0),
            NodeByte::True => Some(True0),

            // Unary (1-arity) Boolean operations
            NodeByte::Not => Some(NotA1),

            // Binary (2-arity) Boolean operations
            NodeByte::And => Some(AndAB2),
            NodeByte::Or => Some(OrAB2),
            NodeByte::Implies => Some(ImpliesAB2),
            NodeByte::Biimp => Some(BiimpAB2),
            NodeByte::ExclusiveOr => Some(XorAB2),
            NodeByte::NotAnd => Some(NotAndAB2),
            NodeByte::NotOr => Some(NotOrAB2),

            // Ternary (3-arity) Boolean operations
            NodeByte::And3 => Some(And3ABC3),
            NodeByte::Or3 => Some(Or3ABC3),
            NodeByte::LogicalIf => Some(IfABC3),
            NodeByte::CarryFromAdder => Some(Majority3ABC3),
            NodeByte::SumFromAdder => Some(Xor3ABC3),

            // All other nodes are not Boolean operations
            _ => None,
        }
    }

    fn format_with(&self, formatter: &dyn OutputFormatter) -> String {
        match formatter.name() {
            "ascii" => self.to_ascii_symbol().to_string(),
            "latex" => self.to_latex_symbol().to_string(),
            "html" | "html-color" => {
                let sym = self.to_utf8_symbol();
                format!("<span class='op'>{}</span>", sym)
            }
            "utf8-color" => {
                let sym = self.to_utf8_symbol();
                // Operators get fixed orange color
                format!("\x1b[38;5;208m{}\x1b[0m", sym)
            }
            _ => self.to_utf8_symbol().to_string(), // Default: UTF-8
        }
    }

    fn to_ascii_symbol(&self) -> &str {
        match self {
            // Basic logical operators
            NodeByte::Not => "-.",
            NodeByte::Implies => "->",
            NodeByte::Biimp => "<->",
            NodeByte::And => "/\\",
            NodeByte::Or => "\\/",
            NodeByte::ExclusiveOr => "(+)",
            NodeByte::NotAnd => "-./\\",
            NodeByte::NotOr => "-.\\/",

            // Set operations
            NodeByte::IsElementOf => " e. ",
            NodeByte::NotElementOf => " e/. ",
            NodeByte::Equals => " = ",
            NodeByte::NotEquals => " =/= ",
            NodeByte::Subset => " C_ ",
            NodeByte::ProperSubset => " C. ",

            // Quantifiers
            NodeByte::ForAll => "A.",
            NodeByte::Exists => "E.",
            NodeByte::ExistsAtMostOne => "E*",
            NodeByte::ExistsExactlyOne => "E!",

            // Ternary operators
            NodeByte::And3 => "/\\3",
            NodeByte::Or3 => "\\/3",
            NodeByte::LogicalIf => "if-",

            // Constants
            NodeByte::True => "T.",
            NodeByte::False => "F.",

            // Default: use Display
            _ => "?",
        }
    }

    fn to_utf8_symbol(&self) -> &str {
        match self {
            // Basic logical operators
            NodeByte::Not => "¬",
            NodeByte::Implies => "→",
            NodeByte::Biimp => "↔",
            NodeByte::And => "∧",
            NodeByte::Or => "∨",
            NodeByte::ExclusiveOr => "⊻",
            NodeByte::NotAnd => "⊼",
            NodeByte::NotOr => "⊽",

            // Set operations
            NodeByte::IsElementOf => " ∈ ",
            NodeByte::NotElementOf => " ∉ ",
            NodeByte::Equals => " = ",
            NodeByte::NotEquals => " ≠ ",
            NodeByte::Subset => " ⊆ ",
            NodeByte::ProperSubset => " ⊊ ",

            // Quantifiers
            NodeByte::ForAll => "∀",
            NodeByte::Exists => "∃",
            NodeByte::ExistsAtMostOne => "∃*",
            NodeByte::ExistsExactlyOne => "∃!",

            // Ternary operators
            NodeByte::And3 => "∧₃",
            NodeByte::Or3 => "∨₃",
            NodeByte::LogicalIf => "if",

            // Constants
            NodeByte::True => "⊤",
            NodeByte::False => "⊥",

            // Class operations
            NodeByte::UnionOp => " ∪ ",
            NodeByte::IntersectionOp => " ∩ ",
            NodeByte::DiffOp => " ∖ ",
            NodeByte::SymDiffOp => " △ ",

            // Default: use Display
            _ => "?",
        }
    }

    fn to_latex_symbol(&self) -> &str {
        match self {
            // Basic logical operators
            NodeByte::Not => r"\neg ",
            NodeByte::Implies => r"\to ",
            NodeByte::Biimp => r"\leftrightarrow ",
            NodeByte::And => r"\land ",
            NodeByte::Or => r"\lor ",
            NodeByte::ExclusiveOr => r"\oplus ",
            NodeByte::NotAnd => r"\barwedge ",
            NodeByte::NotOr => r"\veebar ",

            // Set operations
            NodeByte::IsElementOf => r"\in ",
            NodeByte::NotElementOf => r"\notin ",
            NodeByte::Equals => " = ",
            NodeByte::NotEquals => r"\neq ",
            NodeByte::Subset => r"\subseteq ",
            NodeByte::ProperSubset => r"\subset ",

            // Quantifiers
            NodeByte::ForAll => r"\forall ",
            NodeByte::Exists => r"\exists ",
            NodeByte::ExistsAtMostOne => r"\exists^{*}",
            NodeByte::ExistsExactlyOne => r"\exists!",

            // Ternary operators
            NodeByte::And3 => r"\land_{3}",
            NodeByte::Or3 => r"\lor_{3}",
            NodeByte::LogicalIf => r"\text{if}",

            // Constants
            NodeByte::True => r"\top ",
            NodeByte::False => r"\bot ",

            // Class operations
            NodeByte::UnionOp => r"\cup ",
            NodeByte::IntersectionOp => r"\cap ",
            NodeByte::DiffOp => r"\setminus ",
            NodeByte::SymDiffOp => r"\triangle ",

            // Default: use Display
            _ => "?",
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{NodeByteFactory, SimpleType};
    use SimpleType::*;

    #[test]
    fn node_u8() {
        let mut max_len = 0;
        let factory: NodeByteFactory<SimpleType> = NodeByteFactory::default();
        for (index, nb) in NodeByte::enumerate().enumerate() {
            assert_eq!(nb.to_order() as usize, index);

            let unsigned_byte = nb as u8;

            let our_enum: Result<NodeByte, _> = factory.lookup_by_discriminant(unsigned_byte);
            assert!(our_enum.is_ok());
            let our_enum = our_enum.unwrap();
            assert_eq!(our_enum as u8, unsigned_byte);
            let our_type = our_enum.to_type();
            let goal_type = match index {
                0..=54 => Boolean,
                55 => {
                    max_len = 0;
                    Class
                }
                _ => Class,
            };
            assert_eq!(
                our_type, goal_type,
                "We are testing {our_type:?} from {our_enum:?} vs {goal_type:?} from index {index}.",
            );
            assert_eq!(our_enum.to_order() as usize, index);
            let n_slots = our_enum.to_slots().len();
            assert!(
                n_slots >= max_len,
                "For {0:?} we have {1} which does not increase monotonically froom {2}.",
                our_enum,
                n_slots,
                max_len
            );
            max_len = n_slots;
        }
    }

    #[test]
    fn factory_rejects_metabyte_discriminant() {
        let factory: NodeByteFactory<SimpleType> = NodeByteFactory::default();

        // MetaByte uses ASCII letters. Test with 'A' (65) which is a valid MetaByte
        // but should NOT be a valid NodeByte discriminant.
        let result = factory.lookup_by_discriminant(65);
        assert!(
            result.is_err(),
            "lookup_by_discriminant should reject MetaByte discriminant 65 ('A')"
        );

        // Also test a few other ASCII letters to verify the contract
        for discriminant in [b'A', b'Z', b'a', b'z', b'x', b'P'] {
            let result = factory.lookup_by_discriminant(discriminant);
            assert!(
                result.is_err(),
                "lookup_by_discriminant should reject MetaByte discriminant {} ('{}')",
                discriminant,
                discriminant as char
            );
        }
    }
}
