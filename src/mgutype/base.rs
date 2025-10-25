//! Introduce the enum [`Type`] and the associated rules for assignment of a [`Term`] to replace a [`Metavariable`].
//!
//! [`Term`]: `crate::Term`
//! [`Metavariable`]: `crate::Metavariable`

use crate::{byte_try_from_signed, byte_try_from_unsigned, MguError};
use std::collections::HashMap;
use std::convert::{TryFrom, TryInto};

/// The type of a [`Metavariable`], [`Node`], or [`Term`]. Said [`Type`] is a [`Boolean`],
/// [`Setvar`], or [`Class`].
///
/// # Formal Statement
///
/// A [`Type`] is one of three disjoint identifiers:
/// * [`Boolean`] (denoted 𝔹)
/// * [`Setvar`] (denoted 𝕊)
/// * [`Class`] (denoted ℂ)
///
/// There is a sub-type relation defined:
/// * Every element of 𝕊 is also valid wherever an element of ℂ is expected
///   (but not vice versa).
///
/// # Questions and Answers
///
/// > Can a [`Type`] simultaneously be a [`Boolean`], a [`Setvar`], and a [`Class`]?
/// > Or are these mutually exclusive categories?
///
/// A [`Type`] is exactly one of a [`Boolean`], a [`Setvar`], or a [`Class`].
///
/// > Are "set" and "class" defined formally anywhere else in your system?
/// > (Are you using set/class in the sense of ZFC/NBG? Or more like informal groupings?)
///
/// A "set" is meant to represent a set as is ZFC, NBG, or first order logic.
/// A [`Setvar`] is set-valued in universal and existential quantifiers and class-builder
/// expressions, but can only be substituted with [`Metavariables`] since no [`Node`] has
/// the [`Type`] of [`Setvar`].
/// A [`Class`] is meant to represent a collection of sets. Thus "Exists" is a
/// [`Boolean`]-valued node which has two slots, the first of which is a [`Setvar`],
/// and the second is a [`Boolean`], while "Equals" is a [`Boolean`]-valued node
/// which has two slots of type [`Class`].
/// A special rule allows a [`Setvar`] [`Metavariable`] to be substituted for a
/// [`Class`] [`Metavariable`], but not the reverse. If Greek letters are used for
/// [`Metavariables`] representing [`Booleans`], lowercase Latin letters should be
/// used for [`Setvars`] and uppercase Latin letters for [`Classes`], as per
/// [Metamath] conventions.
///
/// # Example
///
/// ```
/// use symbolic_mgu::Type;
///
/// let (B, S, C) = (Type::Boolean, Type::Setvar, Type::Class);
/// assert!(B.may_assign_tree_to_this_var(&B));
/// assert!(S.may_assign_tree_to_this_var(&S));
/// assert!(C.may_assign_tree_to_this_var(&C));
/// assert!(C.may_assign_tree_to_this_var(&S));
/// assert!(!S.may_assign_tree_to_this_var(&C));
/// println!("Tested {B:?}, {S:?}, and {C:?}.")
/// ```
///
/// [`Metavariable`]: `crate::Metavariable`
/// [`Metavariables`]: `crate::Metavariable`
/// [`Node`]: `crate::Node`
/// [`Term`]: `crate::Term`
/// [`Boolean`]: `Type::Boolean`
/// [`Booleans`]: `Type::Boolean`
/// [`Setvar`]: `Type::Setvar`
/// [`Setvars`]: `Type::Setvar`
/// [`Class`]: `Type::Class`
/// [`Classes`]: `Type::Class`
/// [MetaMath]: https://us.metamath.org/index.html
#[derive(Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub enum Type {
    /// The type for a metavariable or tree which conceptually is boolean-valued.
    Boolean,

    /// The type for a metavariable which conceptually is set-valued.
    ///
    /// Introduced in first-order logic, this is the type of the variable in
    /// Universal Quantification and Existential Quantification, since we can't
    /// sensibly talk about quantification over all propositions or classes.
    ///
    /// Thus, there are no trees of type `Setvar` except for bare [`Metavariables`].
    ///
    /// [`Metavariables`]: `crate::Metavariable`
    Setvar,

    /// The type for a metavariable or tree which conceptually is class-valued.
    Class,
}

/// Denotes Boolean.
const BLACKBOARD_B: &str = "\u{1d539}";
/// Denotes Boolean.
///
/// Abbreviation for Well-formed formula.
const BLACKBOARD_W: &str = "\u{1d551}";
/// Denotes `Setvar`.
const BLACKBOARD_S: &str = "\u{1d54a}";
/// Denotes Class.
const BLACKBOARD_C: &str = "\u{2102}";

/// Denotes Boolean.
const UC_BOOLEAN1: &str = "BOOLEAN";
/// Denotes Boolean.
///
/// Abbreviation for Well-formed formula.
const UC_BOOLEAN2: &str = "WFF";
/// Denotes Boolean.
const UC_BOOLEAN3: &str = "B";
/// Denotes Boolean.
///
/// Abbreviation for Well-formed formula.
const UC_BOOLEAN4: &str = "W";
/// Denotes `Setvar`.
const UC_SETVAR1: &str = "SETVAR";
/// Denotes `Setvar`.
const UC_SETVAR2: &str = "SET";
/// Denotes `Setvar`.
const UC_SETVAR3: &str = "S";
/// Denotes Class.
const UC_CLASS1: &str = "CLASS";
/// Denotes Class.
const UC_CLASS2: &str = "C";

impl Type {
    /// An array of all values of Type.
    pub const VALUES: [Self; 3] = [Type::Boolean, Type::Setvar, Type::Class];

    /// An array of all values meaningful to `uc_name_to_value()`.
    pub const UC_NAMES: [&'static str; 13] = [
        BLACKBOARD_B,
        BLACKBOARD_C,
        BLACKBOARD_S,
        BLACKBOARD_W,
        UC_BOOLEAN1,
        UC_BOOLEAN2,
        UC_BOOLEAN3,
        UC_BOOLEAN4,
        UC_CLASS1,
        UC_CLASS2,
        UC_SETVAR1,
        UC_SETVAR2,
        UC_SETVAR3,
    ];

    /// Convert `Type` to presentation.
    pub fn to_order(self) -> u8 {
        match self {
            Type::Boolean => 0,
            Type::Setvar => 1,
            Type::Class => 2,
        }
    }

    /// Create a hash map between uppercase strings and Type.
    ///
    /// This hash can be used much like `uc_name_to_value()`.
    ///
    /// # Panics
    ///
    /// If a name in [`UC_NAMES`] cannot be converted by `name_to_value()`.
    ///
    /// [`UC_NAMES`]: `Self::UC_NAMES`
    pub fn uc_name_to_value_map() -> HashMap<String, Type> {
        Self::UC_NAMES
            .to_vec()
            .iter()
            .map(|n| ((*n).to_string(), Self::name_to_value(n).unwrap()))
            .collect()
    }

    /// Convert uppercase string to Type when possible.
    ///
    /// ```
    /// use symbolic_mgu::Type;
    /// assert_eq!(Type::uc_name_to_value("𝔹"), Some(Type::Boolean));
    /// assert_eq!(Type::uc_name_to_value("𝕊"), Some(Type::Setvar));
    /// assert_eq!(Type::uc_name_to_value("ℂ"), Some(Type::Class));
    /// assert_eq!(Type::uc_name_to_value("BOOLEAN"), Some(Type::Boolean));
    /// assert_eq!(Type::uc_name_to_value("SETVAR"), Some(Type::Setvar));
    /// assert_eq!(Type::uc_name_to_value("CLASS"), Some(Type::Class));
    /// assert_eq!(Type::uc_name_to_value("class"), None);
    /// ```
    pub fn uc_name_to_value(value: &str) -> Option<Type> {
        match value {
            BLACKBOARD_B | BLACKBOARD_W | UC_BOOLEAN1 | UC_BOOLEAN2 | UC_BOOLEAN3 | UC_BOOLEAN4 => {
                Some(Type::Boolean)
            }
            BLACKBOARD_S | UC_SETVAR1 | UC_SETVAR2 | UC_SETVAR3 => Some(Type::Setvar),
            BLACKBOARD_C | UC_CLASS1 | UC_CLASS2 => Some(Type::Class),
            _ => None,
        }
    }

    /// Convert string to Type when possible.
    ///
    /// `uc_name_to_value()` is more efficient.
    ///
    /// ```
    /// use symbolic_mgu::Type;
    /// assert_eq!(Type::name_to_value("𝔹"), Some(Type::Boolean));
    /// assert_eq!(Type::name_to_value("𝕊"), Some(Type::Setvar));
    /// assert_eq!(Type::name_to_value("ℂ"), Some(Type::Class));
    /// assert_eq!(Type::name_to_value("booLEan"), Type::name_to_value("b"));
    /// assert_eq!(Type::name_to_value("Set"), Type::name_to_value("s"));
    /// assert_eq!(Type::name_to_value("class"), Type::name_to_value("c"));
    /// ```
    pub fn name_to_value(value: &str) -> Option<Type> {
        Self::uc_name_to_value(value.to_uppercase().as_str())
    }

    /// Short-form uppercase name.
    ///
    /// ```
    /// use symbolic_mgu::Type;
    /// assert_eq!(Type::as_short_str(&Type::Boolean), "𝔹");
    /// assert_eq!(Type::as_short_str(&Type::Setvar), "𝕊");
    /// assert_eq!(Type::as_short_str(&Type::Class), "ℂ");
    /// ```
    pub fn as_short_str(&self) -> &'static str {
        match self {
            Type::Boolean => BLACKBOARD_B,
            Type::Setvar => BLACKBOARD_S,
            Type::Class => BLACKBOARD_C,
        }
    }

    /// Short-form mixed-case ASCII name.
    ///
    /// ```
    /// use symbolic_mgu::Type;
    /// assert_eq!(Type::as_long_str(&Type::Boolean), "Boolean");
    /// assert_eq!(Type::as_long_str(&Type::Setvar), "Setvar");
    /// assert_eq!(Type::as_long_str(&Type::Class), "Class");
    /// ```
    pub fn as_long_str(&self) -> &'static str {
        match self {
            Type::Boolean => stringify!(Boolean),
            Type::Setvar => stringify!(Setvar),
            Type::Class => stringify!(Class),
        }
    }

    /// Implement matching test between [`Metavariables`] and trees.
    ///
    /// There is a sub-type relation defined:
    /// * Every element of 𝕊 is also valid wherever an element of ℂ is expected
    ///   (but not vice versa).
    ///
    /// # Questions and Answers
    ///
    /// > You allow [`Setvar`] [`Metavariables`] to substitute for [`Class`] [`Metavariables`].
    /// > Suppose A and B are [`Class`] [`Metavariables`] with an common edge in the DISTINCTNESS
    /// > graph. If both are substituted with the same [`Setvar`] [`Metavariable`] x, is that
    /// > an error - even though x is a [`Setvar`]?
    ///
    /// Yes.
    ///
    /// > Should TYPE-lowering substitution from [`Setvar`] to [`Class`] carry any implicit renaming
    /// > or cloning semantics to prevent invalid shared structure?
    ///
    /// No, because every [`Setvar`] actually is identical to a [`Class`]. So [`Class`] [`Metavariable`] A
    /// can be safely replaced with [`Setvar`] [`Metavariable`] x everywhere. While even a [`Class`] expression which
    /// is guaranteed to be set-valued in actuality, like "iota(y,P)" cannot be safely
    /// substituted for x in expressions like "Exists(x, ...)".
    ///
    /// [`Metavariable`]: `crate::Metavariable`
    /// [`Metavariables`]: `crate::Metavariable`
    /// [`Node`]: `crate::Node`
    /// [`Nodes`]: `crate::Node`
    /// [`Boolean`]: `Type::Boolean`
    /// [`Setvar`]: `Type::Setvar`
    /// [`Class`]: `Type::Class`
    pub fn may_assign_tree_to_this_var(&self, tree_type: &Self) -> bool {
        *self == *tree_type || (*self == Type::Class && *tree_type == Type::Setvar)
    }

    /// Return associated HTML color, based on [Metamath] conventions.
    ///
    /// [MetaMath]: https://us.metamath.org/
    pub const fn to_html_color(&self) -> &'static str {
        match *self {
            // CMYK (100): 88.07, 67.70, 0, 0
            // La*b* (100): 32, 79, -108
            // La*b* (100, D65): 29.64, 92.53, -130.87
            // Close to Pantone "Dark Blue C", "2736 CP", "P 106-8 C"
            Type::Boolean => "blue",
            // CMYK (100): 0.32, 83.54, 93.92, 0.92
            // La*b* (100): 53, 80, 67
            // La*b* (100, D65): 54.13, 76.46, 64.94
            // Close to Pantone "Bright Red C", "2347 CP", "P 57-8 C"
            Type::Setvar => "red",
            // CMYK (100): 36.27, 67.60, 0, 0
            // La*b* (100): 51, 75, -47
            // La*b* (100, D65): 51.14, 76.18, -62.62
            // Close to Pantone "Purple C", "Purple CP", "P 83-6 C"
            Type::Class => "#C3C",
        }
    }
}

impl TryFrom<u8> for Type {
    type Error = MguError;

    /// Performs the conversion.
    ///
    /// Converts ASCII display value back to [`Type`] enum value.
    fn try_from(value: u8) -> Result<Self, Self::Error> {
        match value {
            0 | b'B' | b'W' | b'b' | b'w' => Ok(Type::Boolean),
            2 | b'C' | b'c' => Ok(Type::Class),
            1 | b'S' | b's' => Ok(Type::Setvar),
            _ => Err(MguError::UnsignedValueUnsupported(
                value as u128,
                stringify!(Type),
            )),
        }
    }
}

impl TryFrom<i8> for Type {
    type Error = MguError;

    /// Performs the conversion.
    ///
    /// Converts ASCII display value back to [`Type`] enum value.
    fn try_from(value: i8) -> Result<Self, Self::Error> {
        if 0 <= value {
            (value as u8).try_into()
        } else {
            Err(MguError::SignedValueOutOfRange(
                value as i128,
                stringify!(Type),
                0,
                u8::MAX as u32,
            ))
        }
    }
}

byte_try_from_signed!(Type: i16, i32, i64, i128, isize,);

byte_try_from_unsigned!(Type: char, u16, u32, u64, u128, usize,);

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn type_boolean() {
        let goal_value = Type::Boolean;
        let short_name = goal_value.as_short_str();
        let long_name = goal_value.as_long_str();
        assert!(Type::VALUES.to_vec().contains(&goal_value));
        assert!(Type::UC_NAMES.to_vec().contains(&short_name));
        assert!(Type::UC_NAMES
            .to_vec()
            .contains(&(long_name.to_uppercase().as_str())));
        assert_eq!(Type::name_to_value(short_name), Some(goal_value));
        assert_eq!(Type::name_to_value(long_name), Some(goal_value));

        assert_eq!(Type::name_to_value(BLACKBOARD_B), Some(goal_value));
        assert_eq!(Type::name_to_value(BLACKBOARD_W), Some(goal_value));
        assert_eq!(Type::name_to_value(UC_BOOLEAN1), Some(goal_value));
        assert_eq!(Type::name_to_value(UC_BOOLEAN2), Some(goal_value));
        assert_eq!(Type::name_to_value(UC_BOOLEAN3), Some(goal_value));
        assert_eq!(Type::name_to_value(UC_BOOLEAN4), Some(goal_value));

        assert!(goal_value.may_assign_tree_to_this_var(&Type::Boolean));
        assert!(!goal_value.may_assign_tree_to_this_var(&Type::Setvar));
        assert!(!goal_value.may_assign_tree_to_this_var(&Type::Class));
    }

    #[test]
    fn type_setvar() {
        let goal_value = Type::Setvar;
        let short_name = goal_value.as_short_str();
        let long_name = goal_value.as_long_str();
        assert!(Type::VALUES.to_vec().contains(&goal_value));
        assert!(Type::UC_NAMES.to_vec().contains(&short_name));
        assert!(Type::UC_NAMES
            .to_vec()
            .contains(&(long_name.to_uppercase().as_str())));
        assert_eq!(Type::name_to_value(short_name), Some(goal_value));
        assert_eq!(Type::name_to_value(long_name), Some(goal_value));

        assert_eq!(Type::name_to_value(BLACKBOARD_S), Some(goal_value));
        assert_eq!(Type::name_to_value(UC_SETVAR1), Some(goal_value));
        assert_eq!(Type::name_to_value(UC_SETVAR2), Some(goal_value));
        assert_eq!(Type::name_to_value(UC_SETVAR3), Some(goal_value));

        assert!(!goal_value.may_assign_tree_to_this_var(&Type::Boolean));
        assert!(goal_value.may_assign_tree_to_this_var(&Type::Setvar));
        assert!(!goal_value.may_assign_tree_to_this_var(&Type::Class));
    }

    #[test]
    fn type_class() {
        let goal_value = Type::Class;
        let short_name = goal_value.as_short_str();
        let long_name = goal_value.as_long_str();
        assert!(Type::VALUES.to_vec().contains(&goal_value));
        assert!(Type::UC_NAMES.to_vec().contains(&short_name));
        assert!(Type::UC_NAMES
            .to_vec()
            .contains(&(long_name.to_uppercase().as_str())));
        assert_eq!(Type::name_to_value(short_name), Some(goal_value));
        assert_eq!(Type::name_to_value(long_name), Some(goal_value));

        assert_eq!(Type::name_to_value(BLACKBOARD_C), Some(goal_value));
        assert_eq!(Type::name_to_value(UC_CLASS1), Some(goal_value));
        assert_eq!(Type::name_to_value(UC_CLASS2), Some(goal_value));

        assert!(!goal_value.may_assign_tree_to_this_var(&Type::Boolean));
        assert!(goal_value.may_assign_tree_to_this_var(&Type::Setvar));
        assert!(goal_value.may_assign_tree_to_this_var(&Type::Class));
    }
}
