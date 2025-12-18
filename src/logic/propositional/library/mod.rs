//! Propositional logic — Library of Polish notation.
//!
//! ## The system of Principia Mathematica (A–N) (1910).
//!
//! - Axioms: [`PM_1_2_AC`], [`PM_1_3_AC`], [`PM_1_4_AC`], [`PM_1_5_AC`], [`PM_1_6_AC`]
//! - Definitions: [`DEF_C_AN`], [`DEF_K_AN`], [`DEF_E_CK`]
//! - Rules: Substitution, Detachment
//!
//! ## Hilbert and Ackermann (A–N) (1928).
//!
//! - Axioms: [`PM_1_2_AC`], [`PM_2_2_AC`], [`PM_1_4_AC`], [`PM_1_5_AC`], [`PM_1_6_AC`]
//! - Definitions: [`DEF_C_AN`], [`DEF_K_AN`], [`DEF_E_CK`]
//! - Rules: Substitution, Detachment
//!
//! ## Three-Axiom A–N System (Meredith, 1951).
//! - Axioms: [`PM_1_2_AC`], [`CURRYS_AXIOM_AC`], [`M1951_3_AC`]
//! - Definitions: [`DEF_C_AN`], [`DEF_K_AN`], [`DEF_E_CK`]
//! - Rules: Substitution, Detachment
//!
//! ## Single-Axiom A–N System (Meredith, 1953).
//! - Axiom: [`M1953_1_AC`], [`M1953_2_AC`], or [`M1953_3_AC`]
//! - Definitions: [`DEF_C_AN`], [`DEF_K_AN`], [`DEF_E_CK`]
//! - Rules: Substitution, Detachment

use crate::logic::build_boolean_statement_from_polish;
use crate::{Metavariable, MguError, Node, Statement, Term, TermFactory, Type};
use strum::{Display, EnumCount, EnumString, FromRepr, VariantArray, VariantNames};

/// Historical formula of propositional calculus.
///
/// Takes a parameter: `S`
/// - `S` = `&str` makes sense for static constants.
/// - `S` = `String` makes sense for run-time values.
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct LibraryFormula<S> {
    /// Polish notation for creation of axiom, definition, or rule.
    pub polish: S,
    /// Name from Principia Mathematica by Whitehead and Russell (1910).
    pub pm_name: Option<S>,
    /// Name from `set.mm` of the Metamath project.
    pub set_mm_name: Option<S>,
    /// Name from `iset.mm` of the Metamath project (if different than `set.mm`).
    pub iset_mm_name: Option<S>,
    /// Description or notes.
    pub description: Option<S>,
    /// Citation of a significant source.
    pub source: Option<S>,
}

/// Well-known sources for retrieving the name of a [`LibraryFormula`].
#[derive(
    Clone,
    Copy,
    Debug,
    PartialEq,
    Eq,
    Hash,
    Display,
    EnumCount,
    EnumString,
    FromRepr,
    VariantArray,
    VariantNames,
)]
pub enum LibrarySource {
    /// Whitehead and Russell (1910)
    PrincipiaMathematica,
    /// Metamath's `set.mm`
    MetamathSetMM,
    /// Metamath's `iset.mm`
    MetamathISetMM,
}

/// Common traits for accessing a `LibraryFormula`.
pub trait PolishFormula {
    /// Return source in Polish notation.
    fn get_polish_notation(&self) -> String;
    /// Return name from a significant source.
    fn get_name(&self, source: LibrarySource) -> Option<String>;
    /// Return description or notes.
    fn get_description(&self) -> Option<String>;
    /// Return citation of a significant source for this theorem.
    fn get_source(&self) -> Option<String>;
}

impl<S: AsRef<str>> PolishFormula for LibraryFormula<S> {
    fn get_polish_notation(&self) -> String {
        self.polish.as_ref().to_string()
    }

    fn get_name(&self, source: LibrarySource) -> Option<String> {
        let opt_ref = match source {
            LibrarySource::PrincipiaMathematica => &self.pm_name,
            LibrarySource::MetamathSetMM => &self.set_mm_name,
            LibrarySource::MetamathISetMM => &self.iset_mm_name,
        };
        opt_ref.as_ref().map(|s| s.as_ref().to_string())
    }

    fn get_description(&self) -> Option<String> {
        self.description.as_ref().map(|s| s.as_ref().to_string())
    }

    fn get_source(&self) -> Option<String> {
        self.source.as_ref().map(|s| s.as_ref().to_string())
    }
}

impl LibraryFormula<&'static str> {
    /// Convert a static `LibraryFormula` to an owned version.
    ///
    /// This is useful when you need to modify or store formulas dynamically.
    ///
    /// # Examples
    ///
    /// ```
    /// use symbolic_mgu::logic::propositional::library::DEF_C_AN;
    ///
    /// let owned = DEF_C_AN.to_owned();
    /// assert_eq!(owned.polish, "ECpqANpq");
    /// ```
    #[must_use]
    pub fn to_owned(&self) -> LibraryFormula<String> {
        LibraryFormula {
            polish: self.polish.to_string(),
            pm_name: self.pm_name.map(str::to_string),
            set_mm_name: self.set_mm_name.map(str::to_string),
            iset_mm_name: self.iset_mm_name.map(str::to_string),
            description: self.description.map(str::to_string),
            source: self.source.map(str::to_string),
        }
    }
}

impl<S: AsRef<str>> LibraryFormula<S> {
    /// Returns a borrowed reference to the Polish notation string.
    ///
    /// This is more efficient than [`PolishFormula::get_polish_notation`] as it
    /// does not allocate a new `String`.
    ///
    /// # Examples
    ///
    /// ```
    /// use symbolic_mgu::logic::propositional::library::DEF_C_AN;
    ///
    /// assert_eq!(DEF_C_AN.borrow_polish(), "ECpqANpq");
    /// ```
    #[must_use]
    pub fn borrow_polish(&self) -> &str {
        self.polish.as_ref()
    }

    /// Returns a borrowed reference to the Principia Mathematica name, if present.
    ///
    /// # Examples
    ///
    /// ```
    /// use symbolic_mgu::logic::propositional::library::{DEF_C_AN, DF_E_CK};
    ///
    /// assert_eq!(DEF_C_AN.borrow_pm_name(), Some("*1.01"));
    /// assert_eq!(DF_E_CK.borrow_pm_name(), None);
    /// ```
    #[must_use]
    pub fn borrow_pm_name(&self) -> Option<&str> {
        self.pm_name.as_ref().map(AsRef::as_ref)
    }

    /// Returns a borrowed reference to the `set.mm` name, if present.
    ///
    /// # Examples
    ///
    /// ```
    /// use symbolic_mgu::logic::propositional::library::DEF_C_AN;
    ///
    /// assert_eq!(DEF_C_AN.borrow_set_mm_name(), Some("imor"));
    /// ```
    #[must_use]
    pub fn borrow_set_mm_name(&self) -> Option<&str> {
        self.set_mm_name.as_ref().map(AsRef::as_ref)
    }

    /// Returns a borrowed reference to the `iset.mm` name, if present.
    ///
    /// # Examples
    ///
    /// ```
    /// use symbolic_mgu::logic::propositional::library::DEF_C_AN;
    ///
    /// assert_eq!(DEF_C_AN.borrow_iset_mm_name(), None);
    /// ```
    #[must_use]
    pub fn borrow_iset_mm_name(&self) -> Option<&str> {
        self.iset_mm_name.as_ref().map(AsRef::as_ref)
    }

    /// Returns a borrowed reference to the description, if present.
    ///
    /// # Examples
    ///
    /// ```
    /// use symbolic_mgu::logic::propositional::library::PM_1_2_AC;
    ///
    /// assert!(PM_1_2_AC.borrow_description().is_some());
    /// ```
    #[must_use]
    pub fn borrow_description(&self) -> Option<&str> {
        self.description.as_ref().map(AsRef::as_ref)
    }

    /// Returns a borrowed reference to the source citation, if present.
    ///
    /// # Examples
    ///
    /// ```
    /// use symbolic_mgu::logic::propositional::library::DEF_C_AN;
    ///
    /// assert_eq!(DEF_C_AN.borrow_source(), Some("Whitehead and Russell (1910)."));
    /// ```
    #[must_use]
    pub fn borrow_source(&self) -> Option<&str> {
        self.source.as_ref().map(AsRef::as_ref)
    }

    /// Returns the primary name for this formula, preferring PM over Metamath names.
    ///
    /// Falls back to Polish notation if no names are set.
    ///
    /// # Examples
    ///
    /// ```
    /// use symbolic_mgu::logic::propositional::library::DEF_C_AN;
    ///
    /// assert_eq!(DEF_C_AN.primary_name(), "*1.01");
    /// ```
    #[must_use]
    pub fn primary_name(&self) -> &str {
        self.pm_name
            .as_ref()
            .or(self.set_mm_name.as_ref())
            .or(self.iset_mm_name.as_ref())
            .map(|s| s.as_ref())
            .unwrap_or_else(|| self.polish.as_ref())
    }

    /// Returns true if this formula has a Principia Mathematica name.
    ///
    /// # Examples
    ///
    /// ```
    /// use symbolic_mgu::logic::propositional::library::{DEF_C_AN, DF_E_CK};
    ///
    /// assert!(DEF_C_AN.has_pm_name());
    /// assert!(!DF_E_CK.has_pm_name());
    /// ```
    #[must_use]
    pub fn has_pm_name(&self) -> bool {
        self.pm_name.is_some()
    }

    /// Build a `Statement` from this formula's Polish notation.
    ///
    /// # Arguments
    ///
    /// * `factory` - Term factory for building the statement
    /// * `vars` - Boolean metavariables to use (p, q, r, ...)
    /// * `nodes` - Boolean operators to use
    ///
    /// # Examples
    ///
    /// ```
    /// use symbolic_mgu::logic::propositional::library::PM_1_2_AC;
    /// use symbolic_mgu::{EnumTermFactory, WideMetavariableFactory, MetavariableFactory, SimpleType};
    /// use symbolic_mgu::bool_eval::{BooleanSimpleNode, BooleanSimpleOp};
    /// use SimpleType::*;
    /// use strum::VariantArray;
    ///
    /// let factory = EnumTermFactory::new();
    /// let var_factory = WideMetavariableFactory::new();
    /// let vars = var_factory
    ///     .list_metavariables_by_type(&Boolean)
    ///     .take(26)
    ///     .collect::<Vec<_>>();
    /// let nodes = <BooleanSimpleOp as VariantArray>::VARIANTS
    ///     .iter()
    ///     .cloned()
    ///     .map(BooleanSimpleNode::from_op)
    ///     .collect::<Vec<_>>();
    ///
    /// let statement = PM_1_2_AC.build_statement(&factory, &vars, &nodes);
    /// assert!(statement.is_ok());
    /// ```
    ///
    /// # Errors
    ///
    /// Returns an error if the Polish notation is invalid or if statement construction fails.
    pub fn build_statement<Ty, V, N, T, TF>(
        &self,
        factory: &TF,
        vars: &[V],
        nodes: &[N],
    ) -> Result<Statement<Ty, V, N, T>, MguError>
    where
        Ty: Type,
        V: Metavariable<Type = Ty>,
        N: Node<Type = Ty>,
        T: Term<Ty, V, N>,
        TF: TermFactory<T, Ty, V, N, TermType = Ty, Term = T, TermMetavariable = V, TermNode = N>,
    {
        build_boolean_statement_from_polish(self.polish.as_ref(), factory, vars, nodes)
    }
}

impl<S: AsRef<str>> std::fmt::Display for LibraryFormula<S> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        if let Some(name) = self
            .pm_name
            .as_ref()
            .or(self.set_mm_name.as_ref())
            .or(self.iset_mm_name.as_ref())
        {
            write!(f, "{} ({})", name.as_ref(), self.polish.as_ref())
        } else {
            write!(f, "{}", self.polish.as_ref())
        }
    }
}

/// Builder for creating `LibraryFormula<String>` instances at run-time.
///
/// # Examples
///
/// ```
/// use symbolic_mgu::logic::propositional::library::LibraryFormulaBuilder;
///
/// let formula = LibraryFormulaBuilder::new()
///     .polish("CpCqp")
///     .pm_name("*1.1")
///     .description("A simple axiom")
///     .build()
///     .unwrap();
///
/// assert_eq!(formula.polish, "CpCqp");
/// ```
#[derive(Default, Debug)]
pub struct LibraryFormulaBuilder {
    /// Polish notation for creation of axiom, definition, or rule.
    polish: Option<String>,
    /// Name from Principia Mathematica by Whitehead and Russell (1910).
    pm_name: Option<String>,
    /// Name from `set.mm` of the Metamath project.
    set_mm_name: Option<String>,
    /// Name from `iset.mm` of the Metamath project (if different than set.mm).
    iset_mm_name: Option<String>,
    /// Description or notes.
    description: Option<String>,
    /// Citation of a significant source.
    source: Option<String>,
}

impl LibraryFormulaBuilder {
    /// Create a new builder.
    #[must_use]
    pub fn new() -> Self {
        Self::default()
    }

    /// Set the Polish notation (required).
    #[must_use]
    pub fn polish(mut self, s: impl Into<String>) -> Self {
        self.polish = Some(s.into());
        self
    }

    /// Set the Principia Mathematica name (optional).
    #[must_use]
    pub fn pm_name(mut self, s: impl Into<String>) -> Self {
        self.pm_name = Some(s.into());
        self
    }

    /// Set the Metamath `set.mm` name (optional).
    #[must_use]
    pub fn set_mm_name(mut self, s: impl Into<String>) -> Self {
        self.set_mm_name = Some(s.into());
        self
    }

    /// Set the Metamath `iset.mm` name (optional).
    #[must_use]
    pub fn iset_mm_name(mut self, s: impl Into<String>) -> Self {
        self.iset_mm_name = Some(s.into());
        self
    }

    /// Set the description (optional).
    #[must_use]
    pub fn description(mut self, s: impl Into<String>) -> Self {
        self.description = Some(s.into());
        self
    }

    /// Set the source citation (optional).
    #[must_use]
    pub fn source(mut self, s: impl Into<String>) -> Self {
        self.source = Some(s.into());
        self
    }

    /// Build the `LibraryFormula`.
    ///
    /// # Errors
    ///
    /// Returns an error if the Polish notation was not set.
    pub fn build(self) -> Result<LibraryFormula<String>, MguError> {
        Ok(LibraryFormula {
            polish: self.polish.ok_or_else(|| {
                MguError::UnificationFailure("Polish notation is required".to_string())
            })?,
            pm_name: self.pm_name,
            set_mm_name: self.set_mm_name,
            iset_mm_name: self.iset_mm_name,
            description: self.description,
            source: self.source,
        })
    }
}

/// Registry of standard propositional logic formulas.
///
/// Provides lookup and iteration over the built-in library of formulas.
///
/// # Examples
///
/// ```
/// use symbolic_mgu::logic::propositional::library::FormulaLibrary;
///
/// let library = FormulaLibrary::standard();
/// let def_c_an = library.find_by_pm_name("*1.01");
/// assert!(def_c_an.is_some());
/// assert_eq!(def_c_an.unwrap().polish, "ECpqANpq");
///
/// let count = library.iter().count();
/// assert!(count >= 10);
/// ```
pub struct FormulaLibrary {
    /// Collection of library formulas.
    formulas: &'static [&'static LibraryFormula<&'static str>],
}

impl FormulaLibrary {
    /// Get the standard library of propositional formulas.
    #[must_use]
    pub const fn standard() -> Self {
        Self {
            formulas: &[
                &CURRYS_AXIOM_AC,
                &DEF_C_AN,
                &DEF_E_CK,
                &DF_E_CK,
                &DF_E_CN,
                &DEF_K_AN,
                &M1951_3_AC,
                &M1953_1_AC,
                &M1953_2_AC,
                &M1953_3_AC,
                &PM_1_2_AC,
                &PM_1_3_AC,
                &PM_1_4_AC,
                &PM_1_5_AC,
                &PM_1_6_AC,
                &PM_2_01_CN,
                &PM_2_02_C,
                &PM_2_2_AC,
            ],
        }
    }

    /// Find a formula by its Principia Mathematica name.
    ///
    /// # Examples
    ///
    /// ```
    /// use symbolic_mgu::logic::propositional::library::FormulaLibrary;
    ///
    /// let library = FormulaLibrary::standard();
    /// let pm_1_2 = library.find_by_pm_name("*1.2");
    /// assert!(pm_1_2.is_some());
    /// ```
    #[must_use]
    pub fn find_by_pm_name(&self, name: &str) -> Option<&'static LibraryFormula<&'static str>> {
        self.formulas
            .iter()
            .find(|f| f.pm_name == Some(name))
            .copied()
    }

    /// Find a formula by its Metamath `set.mm` name.
    ///
    /// # Examples
    ///
    /// ```
    /// use symbolic_mgu::logic::propositional::library::FormulaLibrary;
    ///
    /// let library = FormulaLibrary::standard();
    /// let imor = library.find_by_set_mm_name("imor");
    /// assert!(imor.is_some());
    /// ```
    #[must_use]
    pub fn find_by_set_mm_name(&self, name: &str) -> Option<&'static LibraryFormula<&'static str>> {
        self.formulas
            .iter()
            .find(|f| f.set_mm_name == Some(name))
            .copied()
    }

    /// Find a formula by its Polish notation.
    ///
    /// # Examples
    ///
    /// ```
    /// use symbolic_mgu::logic::propositional::library::FormulaLibrary;
    ///
    /// let library = FormulaLibrary::standard();
    /// let formula = library.find_by_polish("ECpqANpq");
    /// assert!(formula.is_some());
    /// ```
    #[must_use]
    pub fn find_by_polish(&self, polish: &str) -> Option<&'static LibraryFormula<&'static str>> {
        self.formulas.iter().find(|f| f.polish == polish).copied()
    }

    /// Iterate over all formulas in the library.
    pub fn iter(&self) -> impl Iterator<Item = &'static LibraryFormula<&'static str>> {
        self.formulas.iter().copied()
    }

    /// Get the number of formulas in the library.
    #[must_use]
    pub fn len(&self) -> usize {
        self.formulas.len()
    }

    /// Returns true if the library contains no formulas.
    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.formulas.is_empty()
    }
}

/// A `LibraryFormula` suitable for a constant declaration.
type Lfs = LibraryFormula<&'static str>;

/// Define implication in terms of disjunction and negation.
///
/// - Whitehead and Russell: `*1.01. p⊃q .=. ~p∨q Df.`
/// - Whitehead and Russell: `*4.6. ⊢: p⊃q .≡. ~p∨q`
/// - Metamath: `⊢ ((𝜑 → 𝜓) ↔ (¬ 𝜑 ∨ 𝜓))`
///
/// The particular structure of this theorem allows us to string-substitute `C` ↦ `AN` or the reverse, anywhere.
pub const DEF_C_AN: Lfs = Lfs {
    polish: "ECpqANpq",
    pm_name: Some("*1.01"),
    set_mm_name: Some("imor"),
    iset_mm_name: None,
    description: None,
    source: Some("Whitehead and Russell (1910)."),
};

/// Define equivalence in terms of conjunction and implication.
///
/// - Whitehead and Russell: `*4.01. p≡q .=. p⊃q.q⊃p Df. `
/// - Metamath: `⊢ ((𝜑 ↔ 𝜓) ↔ ((𝜑 → 𝜓) ∧ (𝜓 → 𝜑)))`
pub const DEF_E_CK: Lfs = Lfs {
    polish: "EEpqKCpqCqp",
    pm_name: Some("*4.01"),
    set_mm_name: Some("dfbi2"),
    iset_mm_name: None,
    description: None,
    source: Some("Whitehead and Russell (1910)."),
};

/// Define equivalence in terms of conjunction and implication.
///
/// Dropping requirement to parse a top level E common to all the `DEF_*` entries.
///
/// - Metamath: `⊢ (((𝜑 ↔ 𝜓) → ((𝜑 → 𝜓) ∧ (𝜓 → 𝜑))) ∧ (((𝜑 → 𝜓) ∧ (𝜓 → 𝜑)) → (𝜑 ↔ 𝜓)))`
pub const DF_E_CK: Lfs = Lfs {
    polish: "KCEpqKCpqCqpCKCpqCqpEpq",
    pm_name: None,
    set_mm_name: Some("dfbi"),
    iset_mm_name: None,
    description: None,
    source: Some("Metamath (2008)."),
};

/// Define equivalence in terms of implication and negation.
///
/// Dropping requirement to parse a top level E common to all the `DEF_*` entries.
///
/// - Metamath: `⊢ ¬ (((𝜑 ↔ 𝜓) → ¬ ((𝜑 → 𝜓) → ¬ (𝜓 → 𝜑))) → ¬ (¬ ((𝜑 → 𝜓) → ¬ (𝜓 → 𝜑)) → (𝜑 ↔ 𝜓)))`
pub const DF_E_CN: Lfs = Lfs {
    polish: "NCCEpqNCCpqNCqpNCNCCpqNCqpEpq",
    pm_name: None,
    set_mm_name: Some("dfbi"),
    iset_mm_name: None,
    description: None,
    source: Some("Metamath (1992)."),
};

/// Define conjunction in terms of disjunction and negation.
///
/// - Whitehead and Russell: `*3.01. p.q .=. ~(~p∨~q) Df.`
/// - Whitehead and Russell: `*4.5. p.q .≡. ~(~p∨~q)`
/// - Metamath: `⊢ ((𝜑 ∧ 𝜓) ↔ ¬ (¬ 𝜑 ∨ ¬ 𝜓))`
pub const DEF_K_AN: Lfs = Lfs {
    polish: "EKpqNANpNq",
    pm_name: Some("*3.01"),
    set_mm_name: Some("anor"),
    iset_mm_name: None,
    description: None,
    source: Some("Whitehead and Russell (1910)."),
};

/// The principle of tautology.
///
/// Abbreviated as "Taut." If either p is true or p is true, then p is true.
///
/// - Whitehead and Russell: `*1.2. ⊢: p ∨ p .⊃. p Pp.`
/// - Metamath: `⊢ ((𝜑 ∨ 𝜑) → 𝜑)`
pub const PM_1_2_AC: Lfs = Lfs {
    polish: "CAppp",
    pm_name: Some("*1.2"),
    set_mm_name: Some("pm1.2"),
    iset_mm_name: None,
    description: Some("If either p is true or p is true, then p is true."),
    source: Some("Whitehead and Russell (1910)."),
};

/// The principle of addition.
///
/// Abbreviated as "Add." Introduction of a disjunct.
/// If a proposition is true, any alternative may be added without making it false.
///
/// - Whitehead and Russell: `*1.3. ⊢: q .⊃. p∨q Pp.`
/// - Metamath: `⊢ (𝜑 → (𝜓 ∨ 𝜑))`
pub const PM_1_3_AC: Lfs = Lfs {
    polish: "CpAqp", // or `CqApq`
    pm_name: Some("*1.3"),
    set_mm_name: Some("olc"),
    iset_mm_name: None,
    description: Some(
        "If a proposition is true, any alternative may be added without making it false.",
    ),
    source: Some("Whitehead and Russell (1910)."),
};

/// The principle of permutation.
///
/// Abbreviated as "Perm." 'p or q' implies 'q or p.'
///
/// - Whitehead and Russell: `*1.4. ⊢: p ∨ q .⊃. q ∨ p Pp.`
/// - Metamath: `⊢ ((𝜑 ∨ 𝜓) → (𝜓 ∨ 𝜑))`
pub const PM_1_4_AC: Lfs = Lfs {
    polish: "CApqAqp",
    pm_name: Some("*1.4"),
    set_mm_name: Some("pm1.4"),
    iset_mm_name: None,
    description: Some("If either p is true or p is true, then p is true."),
    source: Some("Whitehead and Russell (1910)."),
};

/// The associative principle.
///
/// Abbreviated as "Assoc." If either p is true, or 'q or r' is true, then either q is true, or 'p or r' is true.
///
/// - Whitehead and Russell: `*1.5. ⊢: p∨(q∨r) .⊃. q∨(p∨r) Pp.`
/// - Metamath: `⊢ ((𝜑 ∨ (𝜓 ∨ 𝜒)) → (𝜓 ∨ (𝜑 ∨ 𝜒)))`
pub const PM_1_5_AC: Lfs = Lfs {
    polish: "CApAqrAqApr",
    pm_name: Some("*1.5"),
    set_mm_name: Some("pm1.5"),
    iset_mm_name: None,
    description: Some(
        "If either p is true, or 'q or r' is true, then either q is true, or 'p or r' is true.",
    ),
    source: Some("Whitehead and Russell (1910)."),
};

/// The principle of summation.
///
/// Abbreviated as "Sum." If q implies r, then p or q implies p or r.
///
/// - Whitehead and Russell: `*1.6. ⊢: q⊃r .⊃: p∨q .⊃. p∨r Pp.`
/// - Metamath: `⊢ ((𝜓 → 𝜒) → ((𝜑 ∨ 𝜓) → (𝜑 ∨ 𝜒)))`
pub const PM_1_6_AC: Lfs = Lfs {
    polish: "CCpqCArpArq", // or `CCqrCApqApr`
    pm_name: Some("*1.6"),
    set_mm_name: Some("orim2"),
    iset_mm_name: None,
    description: Some("If q implies r, then 'p or q' implies 'p or r'."),
    source: Some("Whitehead and Russell (1910)."),
};

/// The principle of <span lang="la-Latn">reductio ad absurdum</span>.
///
/// Weak Clavius law.
/// Abbreviated as "Abs." If p implies its own falsehood, then p is false.
///
/// - Whitehead and Russell: `*2.01. ⊢: p⊃~q .⊃. ~p`
/// - Metamath: `⊢ ((𝜑 → ¬ 𝜑) → ¬ 𝜑)`
pub const PM_2_01_CN: Lfs = Lfs {
    polish: "CCpNpNp",
    pm_name: Some("*2.01"),
    set_mm_name: Some("pm2.01"),
    iset_mm_name: None,
    description: Some("If p implies its own falsehood, then p is false."),
    source: Some("Whitehead and Russell (1910)."),
};

/// The principle of simplification.
///
/// Abbreviated as "Simp." q implies that p implies q.
///
/// - Whitehead and Russell: `*2.02. ⊢: q .⊃. p⊃q`
/// - Metamath: `⊢ (𝜑 → (𝜓 → 𝜑))`
pub const PM_2_02_C: Lfs = Lfs {
    polish: "CpCqp",
    pm_name: Some("*2.02"),
    set_mm_name: Some("ax-1"),
    iset_mm_name: None,
    description: Some("q implies that p implies q."),
    source: Some("Whitehead and Russell (1910)."),
};

/// Introduction of a disjunct.
///
/// If a proposition is true, any alternative may be added without making it false.
///
/// - Whitehead and Russell: `*2.2. ⊢: p .⊃. p∨q`
/// - Metamath: `⊢ (𝜑 → (𝜑 ∨ 𝜓))`
pub const PM_2_2_AC: Lfs = Lfs {
    polish: "CpApq", // or `CqApq`
    pm_name: Some("*2.2"),
    set_mm_name: Some("orc"),
    iset_mm_name: None,
    description: Some(
        "If a proposition is true, any alternative may be added without making it false.",
    ),
    source: Some("Whitehead and Russell (1910)."),
};

/// A non-intuitionistic positive statement, sometimes called a paradox of material implication.
///
/// Sometimes called Curry's axiom.
///
/// Formula (5) from Curry, H. B., **A Theory of Formal Deducibility**, (1950). p. 28.
/// Available at <https://projecteuclid.org/ebooks/notre-dame-mathematical-lectures/A-Theory-of-Formal-Deducibility/toc/ndml/1175197175>.
///
/// - Metamath `⊢ (𝜑 ∨ (𝜑 → 𝜓))`
pub const CURRYS_AXIOM_AC: Lfs = Lfs {
    polish: "ApCpq",
    pm_name: None,
    set_mm_name: Some("curryax"),
    iset_mm_name: None,
    description: Some("Either p or p implies q."),
    source: Some("Curry (1950)."),
};

/// Third axiom from Meredith (1951).
pub const M1951_3_AC: Lfs = Lfs {
    polish: "CApqCCqrApr",
    pm_name: None,
    set_mm_name: None,
    iset_mm_name: None,
    description: Some("If p or q then q implies r implies either p or r."),
    source: Some("Meredith (1951)."), // this was reported by A.N. Prior but exact citation still required
};

/// Single Axiom for Propositional Logic.
pub const M1953_1_AC: Lfs = Lfs {
    polish: "CCCpqArAstCCspArAtp",
    pm_name: None,
    set_mm_name: None,
    iset_mm_name: None,
    description: Some("Single Axiom for Propositional Logic"),
    source: Some("Meredith (1953)."),
};

/// Single Axiom for Propositional Logic.
pub const M1953_2_AC: Lfs = Lfs {
    polish: "CCCpqArAstCCtsArAps",
    pm_name: None,
    set_mm_name: None,
    iset_mm_name: None,
    description: Some("Single Axiom for Propositional Logic"),
    source: Some("Meredith (1953)."),
};

/// Single Axiom for Propositional Logic.
pub const M1953_3_AC: Lfs = Lfs {
    polish: "CCCpqArAstCCrpAtAsp",
    pm_name: None,
    set_mm_name: None,
    iset_mm_name: None,
    description: Some("Single Axiom for Propositional Logic"),
    source: Some("Meredith (1953)."),
};

/*

# 1. Classical Propositional Calculus: A–N, K–N, and D Systems

1.1. The system of Principia Mathematica (A–N) (1910).
• Axioms: (1) CAppp, (2) CqApq, (3) CApqAqp, (4) CApAqrAqApr, (5) CCqrCApqApr
• Definitions: (Df C) C:=AN, (Df K) Kpq:=NANpNq, (Df E) Epq:=KCpqCqp
• Rules: (1) Substitution, (2) Detachment (α, ANαβ→β)

1.2. Hilbert and Ackermann (A–N) (1928).
• Axioms: (1), (2), (3), (5), of 1.1, or same with (2) replaced by CpApq.
• Definitions and Rules as in 1.1.

1.3. Three-Axiom A–N System (Meredith, 1951).
• Axioms: (1) CAppp (cf. 1.1), (2) ApCpq, (3) CApqCCqrApr
• Definitions and Rules as in 1.1

1.4. Single-Axiom A–N System (Meredith, 1953).
• Axiom: CCCpqArAstCCspArAtp, or CCCpqArAstCCtsArAps, or CCCpqArAstCCrpAtAsp
• Definitions and Rules as in 1.1

1.5. K–N System (Sobociński, 1939).
• Axioms: (1) NKNKNprKNKNqrKNKpqr, (2) NKNpKpq, (3) NKNqKpKrq, (4) NKNKpqNNKpNNq
• Definitions: (Df C) Cpq:=NKpNq, (Df A) Apq:=NKNpNq, (Df E, as in 1.1) Epq:=KCpqCqp
• Rules: (1) Substitution, (2) Detachment (α, NKαNβ→β)

1.6. Single-Axiom Systems in D.
• Axiom: DDpDqrDDtDttDDsqDDpsDps (Nicod, 1918) or DDpDqrDDpDrpDDsqDDpsDps (Łukasiewicz, 1931)
• Definitions: (Df N) Np:=Dpp, (Df K) K:=ND, (Df C) Cpq:=DpNq, (Df A) Apq:=DNpNq
• Rules: (1) Substitution, (2) Detachment (α, DαDγβ→β)

# 2. Classical Propositional Calculus: C–N Systems

2.1. Łukasiewicz’s Standard C–N System (1929).
• Axioms: (1) CCpqCCqrCpr, (2) CCNppp, (3) CpCNpq
• Definitions: (Df A) A:=CN, (Df K) Kpq:=NCpNq, (Df E, as in 1.1) Epq:=KCpqCqp
• Rules: (1) Substitution, (2) Detachment (α, Cαβ→β)

2.2. Single-Axiom C–N System (Meredith, 1953).
• Axiom: CCCCCpqCNrNsrtCCtpCsp
• Definitions and Rules as in 2.1.

2.3. Axiomless C–N System (Suszko, 1948).
• Rules: (1) p,Cpq→q, (2) q→Cpq, (3) CCpqr→Cqr, (4) CpCqr→CCpqCpr, (5) Cpq→CCrpCCqsCrs, (6) CCpqr→CNPr, (7) Cpq,CNpq→q
• Definitions as in 2.1.

2.4. Trivially Axiomless Systems (Słupecki, 1949).
• To Rule (1) of 2.3 add any one of the following three sets:
    • (2) Ksp→p, (3) s→KsCCpqCCqrCpr, (4) s→KsCCNppp, (5) s→KsCpCNpq
    • (2)′ CCsqr→Cqr, (3)′ s→CCsCpqCCqrCpr, (4)′ s→CCsCNppp, (5)′ s→CCspCNpq
    • (2)″ s→CCspp, (3)″ CCpqr→Cqr, (4)″ Cpt→CCtqCCqrCpr, (5)″ Cpt→CCNppt, (6)″ Cpt→CpCNtq

As in 2.3, none of the initially given rules has a tautologous consequent. But by applying (2) to the result of applying (3)— (5)，or (2)′ to the result of applying (3)′—(5)′, or by deriving s→Cpp from (2)″ and (3)″ and combining this with (4)″—(6)″，the axioms of 2.1 are derivable from any arbitrary proposition s. Axiomless systems may be similarly constructed from any set of axioms.

# 3. Classical Propositional Calculus: C Fragment and C–0 Systems

3.1. Implicational Calculus (Tarski and Bernays, 1930).
• Axioms: (1) CCpqCCqrCpr, (2) CCCpqpp, (3) CpCqp
• Rules: Substitution and detachment as in 2.1.

3.2. Single-Axiom Implicational Calculus (Łukasiewicz, 1948)
• Axiom: CCCpqrCCrpCsp
• Rules as in 2.1.

3.3. Full Calculus in C and 0 (Wajsberg, 1937).
• Axioms: (1)–(3) as in 3.1, (4) C0p
• Definitions: (Df N) Np:= Cp0, (Df 1) 1:=N0, (Dff. A, K, E) as in 2.1.
• Rules as in 2.1.

3.4. Single-Axiom C–0 System (Meredith, 1953).
• Axiom: CCCCCpqCr0stCCtpCrp, or CCCpqCC0rsCCspCtCup
• Definitions and Rules as in 3.3.

# 4. Rules for Quantifiers

Where new types of variables are introduced, appropriate substitution rules are introduced along with them, and where there are quantifiers, substitutions must be made for free variables only, and only of variables which are not bound elsewhere in a formula. Of possible rules for introducing quantifiers, we list only those used in the text, which are so framed below as to allow for the appearance of ‘vacuous’ quantifications, i.e. expressions in which the variable bound by the quantifier either does not occur in the formula which follows, or is already bound in it (e.g. Πxρ, Πxφy, ΠxΣxφx). All such expressions may be proved equivalent to the corresponding expressions with the vacuous bindings omitted (ρ, φy, Σxφx). The rules are in all cases understood as adjoined to axioms, definitions, and rules for the propositional calculus; and the x occurring in the rule may be understood as a variable of any type, though the nature of the calculus will depend on the types of variables bound in it.

4.1. Π and Σ both undefined (Łukasiewicz).
• Π1: Cαβ → CΠxαβ
• Π2: Cαβ → CαΠxβ, for x not free in α
• Σ1: Cαβ → CΣxαβ, for x not free in β
• Σ2: Cαβ → CαΣxβ

4.2. With Π undefined.
• Definition: Df. Σ: Σx = NΠxN
• Rules: Π1, Π2, as in 4.1.

4.3. With Σ undefined.
• Definition: Df. Π: Πx = NΣxN
• Rules: Σ1, Σ2, as in 4.1.

# 5. Classical Propositional Calculus: C–Π, C–δ–N, C–δ–0, C–δ, and C–δ–Π Systems

5.1. The Theory of Implication (Russel’s term, 1906, for implicational calculus with quantifiers binding propositional variables, but without functorial variables).
• Axioms: As for implicational calculus (3.1 or 3.2)
• Definitions: (Df 0) 0:=Πpp, (Dff. N and 1) as in 3.3; (Dff. A, K, E) as in 2.1.
• Rules: Substitution; detachment as in 2.1; Π1, Π2, as in 4.1. (This system includes that of 3.3, since C0p is provable by applying Π1 to Cpp.)

5.2. C–N Calculus with Functorial Variables (Meredith, 1953).
• Axiom: CδpCδNpδq
• Definitions as in 2.1
• Rules: Substitution for both types of variables; detachment as in 2.1.

5.3. C–0 Calculus with Functorial Variables.
• Axiom: CδC00Cδ0δp (Łukasiewicz, 1951) or Cδδ0δp (Meredith, 1951)
• Definitions as in 3.3.
• Rules as in 5.2.

5.4. Implicational Fragment of Propositional Calculus with Functorial Variables (Meredith, 1951).
• Axiom: CδpCqδδq, or CpCδqδδp, or CδpδδCqq
• Rules as in 5.2.

5.5. Propositional Calculus with Functorial Variables and Quantifiers (Meredith, 1951).
• Axiom: As in 5.4; or CδδΠppδp
• Definitions: As in 5.1
• Rules: Substitution for both sorts of variable; detachment as in 2.1; Π1, Π2, as in 4.1.

# 6. Modal Systems

6.1. The Lewis (N–K–M) Systems (S3, 1918; others 1932; amended).
• (As the rules and definitions are the same in all these, we shall state them first)
• Definitions: (Df L) L:=NMN, (Df C′) C′pq:=NMKpNq, (Df E′) E′pq:=KC′pqC′qp
• Rules: (1) Substitution for propositional variables, (2) Adjunction (α,β→Kαβ), (3) Detachment (α,C′αβ→β), (4) Substitutability of strict equivalents
• Axioms for S1: (1) C′KpqKqp, (2) C′Kpqp, (3) C′pKpp, (4) C′KpKqrKqKpr, (5) C′KC′pqC′qrC′pr, (6) C′pMp
• Axioms for S2: (1)–(6) plus (7) C′MKpqMp
• Axioms for S3: (1)–(6) plus (8) C′C′pqC′mpMq
• Axioms for S4: (1)–(6) plus (9) C′MMpMp
• Axioms for S5: (1)–(6) plus (10) C′MpLMp
• Axioms for S6: (1)–(7), i.e. as for S2, plus (11) MMp
• Axioms for S7: (1)–(8), i.e. as for S3, plus (11) MMp
• Axioms for S8: (1)–(8), i.e. as for S3, plus (11) LMMp
• (Note: The Lewis systems are so framed that the unmodalized C and E do not occur in the axioms and rules; though they could be introduced by definition as in the K–N system 1.5. With these definitions, the full classical propositional calculus is provable in all the
systems.)

6.2. The Gõdel Systems (L undefined) (1933).
• (These are all understood as adjoined to some complete basis for the
classical propositional calculus, e.g. any from §1 or §2.)
• Definition: (Df M) M:=NLN
• Rule: α→Lα
• Axioms for Common Basis: (1) CLpp (2) CLCpqCLpLq
• Axioms for S4: (1) and (2), plus (3) CLpLLp
• Axioms for S5: (1) and (2), plus (4) CNLpLNLp
((1) and (2) alone, with the definition and rule, yield a system—Feys’s system T—equivalent to what we would obtain by adjoining the rule α→Lα to S2.)

6.3. The von Wright Systems (M undefined) (1951).
• (Again understood as adjoined to some complete basis for the classical propositional calculus)
• Definition: (Df L) L:=NMN
• Rules: (1) α→Lα, (2) Eαβ→EMαMβ
• Axioms for System M: (1) CpMp (2) EMApqAMpMq
• Axioms for System M′: (1) and (2), plus (3) CMMpMp
• Axioms for System M″: (1) and (2), plus (4) CMNMpNMp.
• (System M is equivalent to the system T of 6.2; M′ to S4; M″ to S5.)

6.4. Relations of the Lewis-von Wright Systems.
• (α→β means that in the system α we may prove whatever is provable in β, and more besides)
• S5 (M″) → S4 (M′); S8 → S7; S4 (M′) → T (M); S7 → S6; S7 → S3; S4 (M′) → S3; S6 → S2; S3 → S2; T (M) → S2; S2 → S1
• (T and S3 are independent; and T, S4, and S5 are inconsistent with S6–8.)

6.5. S5 without Added Axioms (Prior, 1953).
• Subjoin to the full classical propositional calculus the special rules (with L and M both undefined): (L1) Cαβ → CLαβ, (L2) Cαβ → CαLβ, if no propositional variable in β occurs unmodalized in α, (M1) Cαβ → CMαβ, if no propositional variable in α occurs unmodalized in β, (M2) Cαβ → CαMβ
• (p is modalized if and only if it is the whole or a part of a propositional formula prefixed by L or M)
• Or L1 and L2, with Df. M as in 6.2.
• Or M1 and M2, with Df. L as in 6.1.

6.6. The Ł-Modal System (Łukasiewicz, 1953).
(Understood as subjoined to 5.2, with M, L, etc., substitutable for δ as well as C, N, etc.; M undefined)
• Special Axiom: CφMp
• Axiomatic Rejections: (1) ∗CMpp, (2) ∗Mp
• Definition: Df. L as in 6.1
• Rules of Rejection: (1) Reject any formula with a rejected substitution, (2) ∗β, Cαβ → ∗α
• All formulae not provable are demonstrably rejected.

6.7. Alternative Basis for the Ł-Modal System (Prior, 1954).
• (Understood as subjoined to 5.2-with-rejection, i.e. with rules of rejection as in 6.6 and with the one axiomatic rejection ∗p. M, L, etc. substitutable for δ as well as C, N, etc.)
• Special Axiom: CδpCδCppδMp
• Definition: Df. L as in 6.1
• Special Rule: The substitutions M/′ and M/C″ may be performed in theses, provided that the same substitution is made throughout the formula.

# 7. Three-valued Systems

7.1. Wajsberg’s Axiomatization (1932) of the Three-valued Calculus in Łukasiewicz’s C and N.
• Matrices:
      C |  1   ½   0   |  N
      --+-------------+---
      1 |  1   ½   0   |  0
      ½ |  1   1   ½   |  ½
      0 |  1   1   1   |  1
• Axioms: (1) CCpqCCqrCpr, (2) CpCqp, (3) CCCpNppp, (4) CCNpNqCqp
• Definitions: (Df A) Apq := CCpqq, (Df K and E) as in 1.1; (Df M) Mp := CNpp
• Rules as in 2.1.
• This system is not strongly complete, but if we add the usual rules of rejection as in 6.6, and axiomatically reject CMpp (i.e. CCNppp) instead of the simple p, all formulae not provable are demonstrably rejected.

7.2. Słupecki’s Functionally and Strongly Complete Extension of Wajsberg’s System (1936).
• Matrices:
      C |  1   ½   0   |  N | T
      --+-------------+----+---
      1 |  1   ½   0   |  0 | ½
      ½ |  1   1   ½   |  ½ | ½
      0 |  1   1   1   |  1 | ½
• Axioms: (1)–(4) as in 7.1, (5) CTpNTp, (6) CNTpTp
• Definitions: (Df. (N)) (N)p := CTpNp, (Df. (C)) (C)pq := C(N)q(N)p
• Rules as in 2.1.
• (Axioms of the classical C–N system 2.1 provable for (C) and (N). Tzu-Hua Hoo, 1949.)


7.3. Słupecki’s Functionally and Strongly Complete System in C, N, and R (1946).
• Matrices:
      C |  1   ½   0   |  N | R
      --+-------------+----+---
      1 |  1   ½   0   |  0 | ½
      ½ |  1   1   1   |  ½ |  1
      0 |  1   1   1   |  1 |  0
• Axioms: (1)–(3) as in the classical C–N system 2.1, (4) CRpNp, (7) CRRpp, (5) CRCpqRq, (8) CpRRp, (6) CpCRqRCpq, (9) NRNp
• Rules as in 2.1.

# 8. Intuitionist Propositional Calculus and Sub-systems

8.1. Heyting’s Calculus of 1930 (Łukasiewicz’s Axioms, 1952).
• Axioms: (1) CpCqp, (2) CCpCqrCCpqCpr, (3) CKpqp, (4) CKpqq, (5) CpCqKpq, (6) CpApq, (7) CqApq, (8) CCprCCqrCApqr, (9) CCpNqCqNp, (10) CpCNpq
• Definitions: (Df. (C)) (C)pq := NKpNq
• Rules: Substitution and detachment as in 2.1.
• (The axioms and rules of the classical C–N system 2.1 are provable for (C) and N.)
• This system is not strongly complete; but Łukasiewicz has surmised
that if we have the usual axiomatic rejection *p, and add to the two
usual rules of rejection as stated in 6.6 the special rule (3) ∗α, ∗β → ∗Aαβ, then all formulae not provable are demonstrably rejected.

8.2. Johannsen’s Minimal Calculus of 1936 (Łukasiewicz’s Axioms).
• Axioms: (1)–(9) as in 8.1, or (1)–(8) as in 8.1, with (Df N) N:=Cpo
• Rules as in 2.1.

8.3. Kolmogorov’s Calculus (1925).
• Axioms: (1), (2), and (9) as in 8.1  or (1) and (2) as in 8.1, with Df. N: N = Cpo
• Rules as in 2.1.

8.4. Positive Logic.
• Axioms (Hilbert, 1928): (1) CCpCpqCpq, (2) CCqrCCpqCpr, (3) CCpCqrCqCpr, (4) CpCqp or (Łukasiewicz): (1) and (2) as in 7.1 or (Meredith, 1953): CCCpqrCsCqCrtCqt
• Rules as in 2.1.
• (With Df. N, or with (9) of 8.1, this gives 8.3.)

8.5. The Weak Positive Implicational Calculus (Church, 1951).
• Axioms: (1) CCpCpqCpq (cf. Hilbert, 8.4), (2) CCqrCCpqCpr (cf. Hilbert, 8.4), (3) CCpCqrCqCpr (cf. Hilbert, 8.4), (4) Cpp (contrast Hilbert, 8.4)
• Rules as in 2.1.
• (Note: In 8.2 and 8.3, or 8.4 with Df. N, CpCNpq is not provable, but CpCqp is. In 8.5, with or without Df. N, neither CpCNpq nor CpCqp is provable.)

# 9. Classical Propositional Calculus: E, E–N, and E–J Fragments

9.1. Two-axiom Equivalential Calculus (Leśniewski, 1929).
• Axioms: (1) EEpqEqp, (2) EEEpqrEpEqr
• Rules: (1) Substitution for propositional variables, (2) Detachment (α, Eαβ→β)

9.2. Single-Axiom Equivalential Calculus (Lukasiewicz, 1939).
• Axiom: EEpqEErqEpr, or EEpqEEprEErq, or EEpqEErpEEqr
• Rules as in 9.1.

9.3. Equivalential Calculus with Negation (Mihailescu, 1937).
• Axioms: (1) Any sufficient for E only, (2) EENpNqEpq
• Definition: (Df J) Jpq := EpNq (or NEpq)
• Rules as in 9.1.
• (Note: Though the pure E-calculi 9.1 and 9.2 are strongly complete, no E–N system can be so. In an E–N formula, either (i) no propositional variable occurs an odd number of times, and M does not occur an odd number of times; or (ii) at least one propositional variable occurs an odd nximber of times, or (iii) no propositional variable occurs an odd number of times, but N does. All E–N tautologies are of type (i), and all such are provable in 9.3; any formula of type (ii), if tried as an extra axiom, is disprovable by deriving the simple as a thesis; but those of type (iii) are neither provable nor thus disprovable. But if we axiomatically reject any one type (iii) formula, e.g. EpNp, and add the rules (1) Reject any formula with a rejected substitution, (2) ∗αβ, Eαβ → ∗β, then all formulae not provable, whether of type (ii) or type (iii), are demonstrably rejected.)

9.4. Equivalential Calculus with Exclusive Alternation (Mihăilescu, 1938).
• Axioms: (1) Any sufficient for E only, (2) EEJpqJrsEEpqErs
• Definition: (Df N) Np := EpJpp
• Rules as in 9.1.
• Metalogical remarks under 9.3 apply with N replaced by J.

9.5. Equivalential Calculus with Exclusive Alternation (Rasiowa, 1948).
• Axioms: (1) EEpqEErqEpr (cf. 9.2), (2) EEpqEJrqJpr
• Definition and Rules as in 9.4.

*/

#[cfg(test)]
mod tests {
    use super::*;
    use crate::bool_eval::{test_validity, BooleanSimpleNode, BooleanSimpleOp};
    use crate::{EnumTermFactory, MetavariableFactory, SimpleType, Type, WideMetavariableFactory};
    use strum::VariantArray;

    type TestNode = BooleanSimpleNode<SimpleType>;

    const LIBRARY_LEN: usize = 18;

    #[test]
    fn library_of_valid_statements() {
        let library = FormulaLibrary::standard();
        let var_factory = WideMetavariableFactory::new();
        let factory = EnumTermFactory::new();
        let vars = var_factory
            .list_metavariables_by_type(&SimpleType::try_boolean().unwrap())
            .take(26)
            .collect::<Vec<_>>();
        let nodes = <BooleanSimpleOp as VariantArray>::VARIANTS
            .iter()
            .cloned()
            .map(BooleanSimpleNode::from_op)
            .collect::<Vec<TestNode>>();
        let implies_node = Some(BooleanSimpleNode::from_op(BooleanSimpleOp::ImpliesAB2));

        for entry in library.iter() {
            let name = entry.primary_name();

            let statement = entry.build_statement(&factory, &vars, &nodes);
            assert!(statement.is_ok(), "'{}' is not ok.", name);
            let statement = statement.unwrap();

            let validity = test_validity(&statement, &factory, &implies_node);
            assert!(validity.is_ok(), "The validity of '{}' is not ok.", name);
            let validity = validity.unwrap();

            assert!(validity, "'{}' is invalid.", name);
        }
    }

    #[test]
    fn entry_to_owned() {
        let owned = DEF_C_AN.to_owned();
        assert_eq!(owned.polish, "ECpqANpq");
        assert_eq!(owned.pm_name, Some("*1.01".to_string()));
        assert_eq!(owned.set_mm_name, Some("imor".to_string()));
    }

    #[test]
    fn entry_primary_name() {
        assert_eq!(DEF_C_AN.primary_name(), "*1.01");
        assert_eq!(DF_E_CK.primary_name(), "dfbi");

        // Create a formula with no names - should return polish notation
        let nameless = LibraryFormula {
            polish: "CpCqp",
            pm_name: None,
            set_mm_name: None,
            iset_mm_name: None,
            description: None,
            source: None,
        };
        assert_eq!(nameless.primary_name(), "CpCqp");
    }

    #[test]
    fn entry_has_pm_name() {
        assert!(DEF_C_AN.has_pm_name());
        assert!(PM_1_2_AC.has_pm_name());
        assert!(!DF_E_CK.has_pm_name());
    }

    #[test]
    fn entry_display() {
        let display_str = format!("{}", DEF_C_AN);
        assert!(display_str.contains("*1.01"));
        assert!(display_str.contains("ECpqANpq"));

        let nameless = LibraryFormula {
            polish: "CpCqp",
            pm_name: None,
            set_mm_name: None,
            iset_mm_name: None,
            description: None,
            source: None,
        };
        assert_eq!(format!("{}", nameless), "CpCqp");
    }

    #[test]
    fn entry_builder() {
        let formula = LibraryFormulaBuilder::new()
            .polish("CpCqp")
            .pm_name("*1.1")
            .description("Simple axiom")
            .build()
            .unwrap();

        assert_eq!(formula.polish, "CpCqp");
        assert_eq!(formula.pm_name, Some("*1.1".to_string()));
        assert_eq!(formula.description, Some("Simple axiom".to_string()));

        // Test that builder fails without polish notation
        let result = LibraryFormulaBuilder::new().build();
        assert!(result.is_err());
    }

    #[test]
    fn formula_library() {
        let library = FormulaLibrary::standard();

        assert_eq!(library.len(), LIBRARY_LEN);
        assert!(!library.is_empty());

        // Test `find_by_pm_name`
        let def_c_an = library.find_by_pm_name("*1.01");
        assert!(def_c_an.is_some());
        assert_eq!(def_c_an.unwrap().polish, "ECpqANpq");

        // Test `find_by_set_mm_name`
        let imor = library.find_by_set_mm_name("imor");
        assert!(imor.is_some());
        assert_eq!(imor.unwrap().pm_name, Some("*1.01"));

        // Test `find_by_polish`
        let formula = library.find_by_polish("CAppp");
        assert!(formula.is_some());
        assert_eq!(formula.unwrap().pm_name, Some("*1.2"));

        // Test iteration
        let count = library.iter().count();
        assert_eq!(count, LIBRARY_LEN);
    }
}
