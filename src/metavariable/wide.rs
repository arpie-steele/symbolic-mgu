//! Wide metavariable implementation with unlimited index space.
//!
//! This module provides [`WideMetavariable`], a type alias for
//! [`ParametricMetavariable<SimpleType, usize, WideCharSet>`](crate::ParametricMetavariable),
//! which supports an effectively unlimited number of variables per type using
//! a (Type, usize) tuple with numeric subscripts.
//!
//! # Display Format
//!
//! [`WideMetavariable`]s use a single italic UTF-8 character (from Unicode Mathematical
//! Alphanumeric Symbols blocks) with an optional numeric subscript:
//!
//! - **Booleans**: Greek letters (φ, ψ, χ, θ, τ, η, ζ, σ, ρ, μ, λ, κ)
//! - **Setvars**: Italic Latin lowercase (𝑥, 𝑦, 𝑧, 𝑤, 𝑣, 𝑢, 𝑡, ...)
//! - **Classes**: Italic Latin uppercase (𝐴, 𝐵, 𝐶, 𝐷, 𝑃, 𝑄, 𝑅, ...)
//!
//! Subscripts use Unicode subscript digits (₀₁₂₃₄₅₆₇₈₉):
//! - Index 0 → φ (first Boolean)
//! - Index 12 → φ₁ (first Boolean, subscript 1)
//! - Index 153 → κ₁₂ (last Boolean κ, subscript 12)
//!
//! # Design Note
//!
//! Following Metamath conventions:
//! - Greek letters for Boolean-valued metavariables
//! - Lowercase Latin for set-valued variables (Setvars)
//! - Uppercase Latin for class-valued variables (Classes)
//!
//! # Examples
//!
//! ```
//! use symbolic_mgu::{WideMetavariable, Metavariable, SimpleType};
//!
//! // Create first Boolean metavariable
//! let phi = WideMetavariable::try_from_type_and_index(SimpleType::Boolean, 0).unwrap();
//! assert_eq!(phi.to_string(), "𝜑");
//!
//! // Create with subscript
//! let phi_1 = WideMetavariable::try_from_type_and_index(SimpleType::Boolean, 12).unwrap();
//! assert_eq!(phi_1.to_string(), "𝜑₁");
//!
//! // Enumerate variables
//! let mut bools = WideMetavariable::enumerate(SimpleType::Boolean);
//! assert_eq!(bools.next().unwrap().to_string(), "𝜑");
//! assert_eq!(bools.next().unwrap().to_string(), "𝜓");
//! ```

use crate::{ParametricMetavariable, SimpleType, WideCharSet};

/// A metavariable implementation with unlimited index space.
///
/// This is a type alias for [`ParametricMetavariable`] configured with:
/// - **Type system**: [`SimpleType`] (Boolean, Setvar, Class)
/// - **Decorator**: `usize` (numeric subscripts: φ, φ₁, φ₂, ...)
/// - **Character set**: [`WideCharSet`]
///
/// # Display Format
///
/// Variables display as a main character (from the appropriate constant)
/// with an optional subscript when the index exceeds the base character count:
///
/// - Index 0-11 (Booleans): φ, ψ, χ, θ, τ, η, ζ, σ, ρ, μ, λ, κ
/// - Index 12-23 (Booleans): φ₁, ψ₁, χ₁, θ₁, τ₁, η₁, ζ₁, σ₁, ρ₁, μ₁, λ₁, κ₁
/// - Index 24-35 (Booleans): φ₂, ψ₂, χ₂, ...
///
/// Subscripts are computed as `index / character_count`.
pub type WideMetavariable = ParametricMetavariable<SimpleType, usize, WideCharSet>;

/// Lowercase Greek letters used for Boolean metavariables.
///
/// Following Metamath conventions for propositional variables.
///
/// # Character Mapping Table
///
/// | Index | ASCII | Unicode | Name | Code Point |
/// |-------|-------|---------|------|------------|
/// | 0     | ph    | 𝜑      | MATHEMATICAL ITALIC SMALL PHI | U+1D711 |
/// | 1     | ps    | 𝜓      | MATHEMATICAL ITALIC SMALL PSI | U+1D713 |
/// | 2     | ch    | 𝜒      | MATHEMATICAL ITALIC SMALL CHI | U+1D712 |
/// | 3     | th    | 𝜃      | MATHEMATICAL ITALIC SMALL THETA | U+1D703 |
/// | 4     | ta    | 𝜏      | MATHEMATICAL ITALIC SMALL TAU | U+1D70F |
/// | 5     | et    | 𝜂      | MATHEMATICAL ITALIC SMALL ETA | U+1D702 |
/// | 6     | ze    | 𝜁      | MATHEMATICAL ITALIC SMALL ZETA | U+1D701 |
/// | 7     | si    | 𝜎      | MATHEMATICAL ITALIC SMALL SIGMA | U+1D70E |
/// | 8     | rh    | 𝜌      | MATHEMATICAL ITALIC SMALL RHO | U+1D70C |
/// | 9     | mu    | 𝜇      | MATHEMATICAL ITALIC SMALL MU | U+1D707 |
/// | 10    | la    | 𝜆      | MATHEMATICAL ITALIC SMALL LAMDA | U+1D706 |
/// | 11    | ka    | 𝜅      | MATHEMATICAL ITALIC SMALL KAPPA | U+1D705 |
///
/// Total: 12 characters.
///
/// See also: [`WIDE_BOOLEANS_ASCII`] for the corresponding ASCII representations.
pub const WIDE_BOOLEANS: &str = "𝜑𝜓𝜒𝜃𝜏𝜂𝜁𝜎𝜌𝜇𝜆𝜅";

/// ASCII representations for Boolean metavariables.
///
/// These are the Metamath-standard two-letter ASCII representations
/// that correspond 1-to-1 with [`WIDE_BOOLEANS`] by index position.
///
/// # Usage Examples
///
/// The ASCII constants correspond 1-to-1 with the UTF-8 characters:
/// - `WIDE_BOOLEANS_ASCII[0]` is `"ph"` → `WIDE_BOOLEANS` char 0 is `"𝜑"`
/// - `WIDE_BOOLEANS_ASCII[1]` is `"ps"` → `WIDE_BOOLEANS` char 1 is `"𝜓"`
pub const WIDE_BOOLEANS_ASCII: &[&str] = &[
    "ph", // 𝜑 MATHEMATICAL ITALIC SMALL PHI
    "ps", // 𝜓 MATHEMATICAL ITALIC SMALL PSI
    "ch", // 𝜒 MATHEMATICAL ITALIC SMALL CHI
    "th", // 𝜃 MATHEMATICAL ITALIC SMALL THETA
    "ta", // 𝜏 MATHEMATICAL ITALIC SMALL TAU
    "et", // 𝜂 MATHEMATICAL ITALIC SMALL ETA
    "ze", // 𝜁 MATHEMATICAL ITALIC SMALL ZETA
    "si", // 𝜎 MATHEMATICAL ITALIC SMALL SIGMA
    "rh", // 𝜌 MATHEMATICAL ITALIC SMALL RHO
    "mu", // 𝜇 MATHEMATICAL ITALIC SMALL MU
    "la", // 𝜆 MATHEMATICAL ITALIC SMALL LAMDA
    "ka", // 𝜅 MATHEMATICAL ITALIC SMALL KAPPA
];

/// Italic Latin lowercase letters used for Setvar metavariables.
///
/// Following Metamath conventions for set variables.
///
/// # Character Mapping Table
///
/// | Index | ASCII | Unicode | Name | Code Point |
/// |-------|-------|---------|------|------------|
/// | 0     | x     | 𝑥      | MATHEMATICAL ITALIC SMALL X | U+1D465 |
/// | 1     | y     | 𝑦      | MATHEMATICAL ITALIC SMALL Y | U+1D466 |
/// | 2     | z     | 𝑧      | MATHEMATICAL ITALIC SMALL Z | U+1D467 |
/// | 3     | w     | 𝑤      | MATHEMATICAL ITALIC SMALL W | U+1D464 |
/// | 4     | v     | 𝑣      | MATHEMATICAL ITALIC SMALL V | U+1D463 |
/// | 5     | u     | 𝑢      | MATHEMATICAL ITALIC SMALL U | U+1D462 |
/// | 6     | t     | 𝑡      | MATHEMATICAL ITALIC SMALL T | U+1D461 |
/// | 7     | f     | 𝑓      | MATHEMATICAL ITALIC SMALL F | U+1D453 |
/// | 8     | g     | 𝑔      | MATHEMATICAL ITALIC SMALL G | U+1D454 |
/// | 9     | s     | 𝑠      | MATHEMATICAL ITALIC SMALL S | U+1D460 |
/// | 10    | e     | 𝑒      | MATHEMATICAL ITALIC SMALL E | U+1D452 |
/// | 11    | h     | ℎ      | PLANCK CONSTANT | U+210E |
/// | 12    | i     | 𝑖      | MATHEMATICAL ITALIC SMALL I | U+1D456 |
/// | 13    | j     | 𝑗      | MATHEMATICAL ITALIC SMALL J | U+1D457 |
/// | 14    | k     | 𝑘      | MATHEMATICAL ITALIC SMALL K | U+1D458 |
/// | 15    | m     | 𝑚      | MATHEMATICAL ITALIC SMALL M | U+1D45A |
/// | 16    | n     | 𝑛      | MATHEMATICAL ITALIC SMALL N | U+1D45B |
/// | 17    | o     | 𝑜      | MATHEMATICAL ITALIC SMALL O | U+1D45C |
/// | 18    | r     | 𝑟      | MATHEMATICAL ITALIC SMALL R | U+1D45F |
/// | 19    | q     | 𝑞      | MATHEMATICAL ITALIC SMALL Q | U+1D45E |
/// | 20    | p     | 𝑝      | MATHEMATICAL ITALIC SMALL P | U+1D45D |
/// | 21    | a     | 𝑎      | MATHEMATICAL ITALIC SMALL A | U+1D44E |
/// | 22    | b     | 𝑏      | MATHEMATICAL ITALIC SMALL B | U+1D44F |
/// | 23    | c     | 𝑐      | MATHEMATICAL ITALIC SMALL C | U+1D450 |
/// | 24    | d     | 𝑑      | MATHEMATICAL ITALIC SMALL D | U+1D451 |
/// | 25    | l     | 𝑙      | MATHEMATICAL ITALIC SMALL L | U+1D459 |
///
/// Note: Index 11 uses PLANCK CONSTANT (ℎ) instead of MATHEMATICAL ITALIC SMALL H
/// due to Unicode encoding considerations.
///
/// Total: 26 characters.
///
/// See also: [`WIDE_SETVARS_ASCII`] for the corresponding ASCII representations.
pub const WIDE_SETVARS: &str = "𝑥𝑦𝑧𝑤𝑣𝑢𝑡𝑓𝑔𝑠𝑒ℎ𝑖𝑗𝑘𝑚𝑛𝑜𝑟𝑞𝑝𝑎𝑏𝑐𝑑𝑙";

/// ASCII representations for Setvar metavariables.
///
/// These are the Metamath-standard single-letter ASCII representations
/// that correspond 1-to-1 with [`WIDE_SETVARS`] by index position.
///
/// # Usage Examples
///
/// The ASCII constants correspond 1-to-1 with the UTF-8 characters:
/// - `WIDE_SETVARS_ASCII[0]` is `"x"` → `WIDE_SETVARS` char 0 is `"𝑥"`
/// - `WIDE_SETVARS_ASCII[1]` is `"y"` → `WIDE_SETVARS` char 1 is `"𝑦"`
pub const WIDE_SETVARS_ASCII: &[&str] = &[
    "x", // 𝑥 MATHEMATICAL ITALIC SMALL X
    "y", // 𝑦 MATHEMATICAL ITALIC SMALL Y
    "z", // 𝑧 MATHEMATICAL ITALIC SMALL Z
    "w", // 𝑤 MATHEMATICAL ITALIC SMALL W
    "v", // 𝑣 MATHEMATICAL ITALIC SMALL V
    "u", // 𝑢 MATHEMATICAL ITALIC SMALL U
    "t", // 𝑡 MATHEMATICAL ITALIC SMALL T
    "f", // 𝑓 MATHEMATICAL ITALIC SMALL F
    "g", // 𝑔 MATHEMATICAL ITALIC SMALL G
    "s", // 𝑠 MATHEMATICAL ITALIC SMALL S
    "e", // 𝑒 MATHEMATICAL ITALIC SMALL E
    "h", // ℎ PLANCK CONSTANT
    "i", // 𝑖 MATHEMATICAL ITALIC SMALL I
    "j", // 𝑗 MATHEMATICAL ITALIC SMALL J
    "k", // 𝑘 MATHEMATICAL ITALIC SMALL K
    "m", // 𝑚 MATHEMATICAL ITALIC SMALL M
    "n", // 𝑛 MATHEMATICAL ITALIC SMALL N
    "o", // 𝑜 MATHEMATICAL ITALIC SMALL O
    "r", // 𝑟 MATHEMATICAL ITALIC SMALL R
    "q", // 𝑞 MATHEMATICAL ITALIC SMALL Q
    "p", // 𝑝 MATHEMATICAL ITALIC SMALL P
    "a", // 𝑎 MATHEMATICAL ITALIC SMALL A
    "b", // 𝑏 MATHEMATICAL ITALIC SMALL B
    "c", // 𝑐 MATHEMATICAL ITALIC SMALL C
    "d", // 𝑑 MATHEMATICAL ITALIC SMALL D
    "l", // 𝑙 MATHEMATICAL ITALIC SMALL L
];

/// Italic Latin uppercase letters used for Class metavariables.
///
/// Following Metamath conventions for class variables.
///
/// # Character Mapping Table
///
/// | Index | ASCII | Unicode | Name | Code Point |
/// |-------|-------|---------|------|------------|
/// | 0     | A     | 𝐴      | MATHEMATICAL ITALIC CAPITAL A | U+1D434 |
/// | 1     | B     | 𝐵      | MATHEMATICAL ITALIC CAPITAL B | U+1D435 |
/// | 2     | C     | 𝐶      | MATHEMATICAL ITALIC CAPITAL C | U+1D436 |
/// | 3     | D     | 𝐷      | MATHEMATICAL ITALIC CAPITAL D | U+1D437 |
/// | 4     | P     | 𝑃      | MATHEMATICAL ITALIC CAPITAL P | U+1D443 |
/// | 5     | Q     | 𝑄      | MATHEMATICAL ITALIC CAPITAL Q | U+1D444 |
/// | 6     | R     | 𝑅      | MATHEMATICAL ITALIC CAPITAL R | U+1D445 |
/// | 7     | S     | 𝑆      | MATHEMATICAL ITALIC CAPITAL S | U+1D446 |
/// | 8     | T     | 𝑇      | MATHEMATICAL ITALIC CAPITAL T | U+1D447 |
/// | 9     | U     | 𝑈      | MATHEMATICAL ITALIC CAPITAL U | U+1D448 |
/// | 10    | E     | 𝐸      | MATHEMATICAL ITALIC CAPITAL E | U+1D438 |
/// | 11    | F     | 𝐹      | MATHEMATICAL ITALIC CAPITAL F | U+1D439 |
/// | 12    | G     | 𝐺      | MATHEMATICAL ITALIC CAPITAL G | U+1D43A |
/// | 13    | H     | 𝐻      | MATHEMATICAL ITALIC CAPITAL H | U+1D43B |
/// | 14    | I     | 𝐼      | MATHEMATICAL ITALIC CAPITAL I | U+1D43C |
/// | 15    | J     | 𝐽      | MATHEMATICAL ITALIC CAPITAL J | U+1D43D |
/// | 16    | K     | 𝐾      | MATHEMATICAL ITALIC CAPITAL K | U+1D43E |
/// | 17    | L     | 𝐿      | MATHEMATICAL ITALIC CAPITAL L | U+1D43F |
/// | 18    | M     | 𝑀      | MATHEMATICAL ITALIC CAPITAL M | U+1D440 |
/// | 19    | N     | 𝑁      | MATHEMATICAL ITALIC CAPITAL N | U+1D441 |
/// | 20    | V     | 𝑉      | MATHEMATICAL ITALIC CAPITAL V | U+1D449 |
/// | 21    | W     | 𝑊      | MATHEMATICAL ITALIC CAPITAL W | U+1D44A |
/// | 22    | X     | 𝑋      | MATHEMATICAL ITALIC CAPITAL X | U+1D44B |
/// | 23    | Y     | 𝑌      | MATHEMATICAL ITALIC CAPITAL Y | U+1D44C |
/// | 24    | Z     | 𝑍      | MATHEMATICAL ITALIC CAPITAL Z | U+1D44D |
/// | 25    | O     | 𝑂      | MATHEMATICAL ITALIC CAPITAL O | U+1D442 |
///
/// Total: 26 characters.
///
/// See also: [`WIDE_CLASSES_ASCII`] for the corresponding ASCII representations.
pub const WIDE_CLASSES: &str = "𝐴𝐵𝐶𝐷𝑃𝑄𝑅𝑆𝑇𝑈𝐸𝐹𝐺𝐻𝐼𝐽𝐾𝐿𝑀𝑁𝑉𝑊𝑋𝑌𝑍𝑂";

/// ASCII representations for Class metavariables.
///
/// These are the Metamath-standard single-letter ASCII representations
/// that correspond 1-to-1 with [`WIDE_CLASSES`] by index position.
///
/// # Usage Examples
///
/// The ASCII constants correspond 1-to-1 with the UTF-8 characters:
/// - `WIDE_CLASSES_ASCII[0]` is `"A"` → `WIDE_CLASSES` char 0 is `"𝐴"`
/// - `WIDE_CLASSES_ASCII[1]` is `"B"` → `WIDE_CLASSES` char 1 is `"𝐵"`
pub const WIDE_CLASSES_ASCII: &[&str] = &[
    "A", // 𝐴 MATHEMATICAL ITALIC CAPITAL A
    "B", // 𝐵 MATHEMATICAL ITALIC CAPITAL B
    "C", // 𝐶 MATHEMATICAL ITALIC CAPITAL C
    "D", // 𝐷 MATHEMATICAL ITALIC CAPITAL D
    "P", // 𝑃 MATHEMATICAL ITALIC CAPITAL P
    "Q", // 𝑄 MATHEMATICAL ITALIC CAPITAL Q
    "R", // 𝑅 MATHEMATICAL ITALIC CAPITAL R
    "S", // 𝑆 MATHEMATICAL ITALIC CAPITAL S
    "T", // 𝑇 MATHEMATICAL ITALIC CAPITAL T
    "U", // 𝑈 MATHEMATICAL ITALIC CAPITAL U
    "E", // 𝐸 MATHEMATICAL ITALIC CAPITAL E
    "F", // 𝐹 MATHEMATICAL ITALIC CAPITAL F
    "G", // 𝐺 MATHEMATICAL ITALIC CAPITAL G
    "H", // 𝐻 MATHEMATICAL ITALIC CAPITAL H
    "I", // 𝐼 MATHEMATICAL ITALIC CAPITAL I
    "J", // 𝐽 MATHEMATICAL ITALIC CAPITAL J
    "K", // 𝐾 MATHEMATICAL ITALIC CAPITAL K
    "L", // 𝐿 MATHEMATICAL ITALIC CAPITAL L
    "M", // 𝑀 MATHEMATICAL ITALIC CAPITAL M
    "N", // 𝑁 MATHEMATICAL ITALIC CAPITAL N
    "V", // 𝑉 MATHEMATICAL ITALIC CAPITAL V
    "W", // 𝑊 MATHEMATICAL ITALIC CAPITAL W
    "X", // 𝑋 MATHEMATICAL ITALIC CAPITAL X
    "Y", // 𝑌 MATHEMATICAL ITALIC CAPITAL Y
    "Z", // 𝑍 MATHEMATICAL ITALIC CAPITAL Z
    "O", // 𝑂 MATHEMATICAL ITALIC CAPITAL O
];

#[cfg(test)]
mod tests {
    use super::*;
    use crate::Metavariable;
    use std::collections::HashSet;

    #[test]
    fn wide_metavariable_display() {
        use SimpleType::*;

        for (t, data, final_girl) in [
            (Boolean, WIDE_BOOLEANS, "𝜃₁₅₃₇₂₂₈₆₇₂₈₀₉₁₂₉₃₀₁"),
            (Setvar, WIDE_SETVARS, "𝑚₇₀₉₄₉₀₁₅₆₆₈₁₁₃₆₆₀₀"),
            (Class, WIDE_CLASSES, "𝐽₇₀₉₄₉₀₁₅₆₆₈₁₁₃₆₆₀₀"),
        ] {
            let _short_t = format!("{t:?}");
            let first_char = data.chars().next().unwrap().to_string();
            let last_char = data.chars().next_back().unwrap().to_string();
            let n = data.chars().count();

            let var = WideMetavariable::try_from_type_and_index(t, 0).unwrap();
            assert!(format!("{var:?}").starts_with("ParametricMetavariable"));
            assert_eq!(format!("{var}"), first_char);
            assert_eq!(
                format!(
                    "{}",
                    WideMetavariable::try_from_type_and_index(t, n - 1).unwrap()
                ),
                last_char
            );
            assert_eq!(
                format!(
                    "{}",
                    WideMetavariable::try_from_type_and_index(t, n).unwrap()
                ),
                first_char.clone() + "₁"
            );
            assert_eq!(
                format!(
                    "{}",
                    WideMetavariable::try_from_type_and_index(t, usize::MAX).unwrap()
                ),
                final_girl
            );
        }
    }

    #[test]
    fn metavariable_wide() {
        assert!(!WIDE_BOOLEANS.is_ascii());
        assert!(!WIDE_SETVARS.is_ascii());
        assert!(!WIDE_CLASSES.is_ascii());

        let n = WIDE_BOOLEANS.chars().count();
        for (i, ch) in WIDE_BOOLEANS.chars().enumerate() {
            let x = WideMetavariable::try_from_type_and_index(SimpleType::Boolean, i).unwrap();
            assert_eq!(x.to_string(), ch.to_string());
            assert_eq!(x.get_type_and_index(), Ok((SimpleType::Boolean, i)));
            let y = WideMetavariable::try_from_type_and_index(SimpleType::Boolean, i);
            assert_eq!(y, Ok(x));

            let x = WideMetavariable::try_from_type_and_index(SimpleType::Boolean, i + n).unwrap();
            assert_eq!(x.to_string(), ch.to_string() + "₁");
            assert_eq!(x.get_type_and_index(), Ok((SimpleType::Boolean, i + n)));
            let y = WideMetavariable::try_from_type_and_index(SimpleType::Boolean, i + n);
            assert_eq!(y, Ok(x));
        }

        let n = WIDE_SETVARS.chars().count();
        for (i, ch) in WIDE_SETVARS.chars().enumerate() {
            let x = WideMetavariable::try_from_type_and_index(SimpleType::Setvar, i).unwrap();
            assert_eq!(x.to_string(), ch.to_string());
            assert_eq!(x.get_type_and_index(), Ok((SimpleType::Setvar, i)));
            let y = WideMetavariable::try_from_type_and_index(SimpleType::Setvar, i);
            assert_eq!(y, Ok(x));

            let x = WideMetavariable::try_from_type_and_index(SimpleType::Setvar, i + n).unwrap();
            assert_eq!(x.to_string(), ch.to_string() + "₁");
            assert_eq!(x.get_type_and_index(), Ok((SimpleType::Setvar, i + n)));
            let y = WideMetavariable::try_from_type_and_index(SimpleType::Setvar, i + n);
            assert_eq!(y, Ok(x));
        }

        let n = WIDE_CLASSES.chars().count();
        for (i, ch) in WIDE_CLASSES.chars().enumerate() {
            let x = WideMetavariable::try_from_type_and_index(SimpleType::Class, i).unwrap();
            assert_eq!(x.to_string(), ch.to_string());
            assert_eq!(x.get_type_and_index(), Ok((SimpleType::Class, i)));
            let y = WideMetavariable::try_from_type_and_index(SimpleType::Class, i);
            assert_eq!(y, Ok(x));

            let x = WideMetavariable::try_from_type_and_index(SimpleType::Class, i + n).unwrap();
            assert_eq!(x.to_string(), ch.to_string() + "₁");
            assert_eq!(x.get_type_and_index(), Ok((SimpleType::Class, i + n)));
            let y = WideMetavariable::try_from_type_and_index(SimpleType::Class, i + n);
            assert_eq!(y, Ok(x));
        }

        let mut uniques = HashSet::new();
        for t in [SimpleType::Boolean, SimpleType::Setvar, SimpleType::Class] {
            for i in WideMetavariable::enumerate(t).take(100) {
                assert_eq!(i.get_type(), Ok(t));
                assert!(uniques.insert(i));
            }
        }
    }

    #[test]
    fn enumerate_produces_unique_variables() {
        // Test that enumeration produces unique variables
        let vars: Vec<_> = WideMetavariable::enumerate(SimpleType::Boolean)
            .take(100)
            .collect();
        let unique_vars: HashSet<_> = vars.iter().cloned().collect();

        assert_eq!(
            vars.len(),
            unique_vars.len(),
            "All enumerated variables should be unique"
        );
    }

    #[test]
    fn subscript_formatting() {
        // Test various subscript numbers
        // Note: Uses Mathematical Italic characters from `OUR_BOOLEANS` constant
        let first_bool = WIDE_BOOLEANS.chars().next().unwrap().to_string();
        let test_cases = vec![
            (0, first_bool.clone()),            // No subscript
            (12, first_bool.clone() + "₁"),     // First subscript
            (24, first_bool.clone() + "₂"),     // Second subscript
            (120, first_bool.clone() + "₁₀"),   // Two-digit subscript
            (1200, first_bool.clone() + "₁₀₀"), // Three-digit subscript
        ];

        for (index, expected) in test_cases {
            let var =
                WideMetavariable::try_from_type_and_index(SimpleType::Boolean, index).unwrap();
            assert_eq!(
                var.to_string(),
                expected,
                "Index {} should format as {}",
                index,
                expected
            );
        }
    }
}
