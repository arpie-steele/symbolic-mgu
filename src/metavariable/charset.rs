//! Character set mappings for parametric metavariables.
//!
//! This module provides [`WideCharSet`], which defines character mappings
//! for Boolean, Setvar, and Class metavariables in multiple output formats.

use crate::{SimpleType, WIDE_BOOLEANS_ASCII, WIDE_CLASSES_ASCII, WIDE_SETVARS_ASCII};
use SimpleType::*;

/// Character set for WideMetavariable-style display.
///
/// Provides const functions for looking up character representations
/// in ASCII, UTF-8, and LaTeX formats.
///
/// # Character Sets
///
/// - **Booleans**: 12 Greek letters (φ, ψ, χ, θ, τ, η, ζ, σ, ρ, μ, λ, κ)
/// - **Setvars**: 26 lowercase Latin letters (x, y, z, w, v, u, t, ...)
/// - **Classes**: 26 uppercase Latin letters (A, B, C, D, P, Q, R, S, ...)
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct WideCharSet;

impl WideCharSet {
    // ==================== BOOLEAN CHARACTERS ====================

    /// ASCII representations for Boolean metavariables (Metamath-compatible).
    #[must_use]
    pub const fn ascii_boolean(index: usize) -> Option<&'static str> {
        /// See `crate::WIDE_BOOLEANS_ASCII`
        const CHARS: &[&str] = WIDE_BOOLEANS_ASCII;
        if index < CHARS.len() {
            Some(CHARS[index])
        } else {
            None
        }
    }

    /// UTF-8 representations for Boolean metavariables (Unicode mathematical symbols).
    #[must_use]
    pub const fn utf8_boolean(index: usize) -> Option<&'static str> {
        /// See `crate::WIDE_BOOLEANS` for an equivalent string.
        const CHARS: &[&str] = &[
            "𝜑", // U+1D711 MATHEMATICAL ITALIC SMALL PHI
            "𝜓", // U+1D713 MATHEMATICAL ITALIC SMALL PSI
            "𝜒", // U+1D712 MATHEMATICAL ITALIC SMALL CHI
            "𝜃", // U+1D703 MATHEMATICAL ITALIC SMALL THETA
            "𝜏", // U+1D70F MATHEMATICAL ITALIC SMALL TAU
            "𝜂", // U+1D702 MATHEMATICAL ITALIC SMALL ETA
            "𝜁", // U+1D701 MATHEMATICAL ITALIC SMALL ZETA
            "𝜎", // U+1D70E MATHEMATICAL ITALIC SMALL SIGMA
            "𝜌", // U+1D70C MATHEMATICAL ITALIC SMALL RHO
            "𝜇", // U+1D707 MATHEMATICAL ITALIC SMALL MU
            "𝜆", // U+1D706 MATHEMATICAL ITALIC SMALL LAMDA
            "𝜅", // U+1D705 MATHEMATICAL ITALIC SMALL KAPPA
        ];
        if index < CHARS.len() {
            Some(CHARS[index])
        } else {
            None
        }
    }

    /// LaTeX representations for Boolean metavariables.
    #[must_use]
    pub const fn latex_boolean(index: usize) -> Option<&'static str> {
        /// See `crate::WIDE_BOOLEANS` for a corresponding UTF-8 string.
        const CHARS: &[&str] = &[
            r"\varphi", // φ
            r"\psi",    // ψ
            r"\chi",    // χ
            r"\theta",  // θ
            r"\tau",    // τ
            r"\eta",    // η
            r"\zeta",   // ζ
            r"\sigma",  // σ
            r"\rho",    // ρ
            r"\mu",     // μ
            r"\lambda", // λ
            r"\kappa",  // κ
        ];
        if index < CHARS.len() {
            Some(CHARS[index])
        } else {
            None
        }
    }

    // ==================== SETVAR CHARACTERS ====================

    /// ASCII representations for Setvar metavariables (Metamath-compatible).
    #[must_use]
    pub const fn ascii_setvar(index: usize) -> Option<&'static str> {
        /// See `crate::WIDE_SETVARS_ASCII`.
        const CHARS: &[&str] = WIDE_SETVARS_ASCII;
        if index < CHARS.len() {
            Some(CHARS[index])
        } else {
            None
        }
    }

    /// UTF-8 representations for Setvar metavariables (italic Latin lowercase).
    #[must_use]
    pub const fn utf8_setvar(index: usize) -> Option<&'static str> {
        /// See `crate::WIDE_SETVARS` for an equivalent string.
        const CHARS: &[&str] = &[
            "𝑥", // U+1D465 MATHEMATICAL ITALIC SMALL X
            "𝑦", // U+1D466 MATHEMATICAL ITALIC SMALL Y
            "𝑧", // U+1D467 MATHEMATICAL ITALIC SMALL Z
            "𝑤", // U+1D464 MATHEMATICAL ITALIC SMALL W
            "𝑣", // U+1D463 MATHEMATICAL ITALIC SMALL V
            "𝑢", // U+1D462 MATHEMATICAL ITALIC SMALL U
            "𝑡", // U+1D461 MATHEMATICAL ITALIC SMALL T
            "𝑓", // U+1D453 MATHEMATICAL ITALIC SMALL F
            "𝑔", // U+1D454 MATHEMATICAL ITALIC SMALL G
            "𝑠", // U+1D460 MATHEMATICAL ITALIC SMALL S
            "𝑒", // U+1D452 MATHEMATICAL ITALIC SMALL E
            "ℎ", // U+210E PLANCK CONSTANT
            "𝑖", // U+1D456 MATHEMATICAL ITALIC SMALL I
            "𝑗", // U+1D457 MATHEMATICAL ITALIC SMALL J
            "𝑘", // U+1D458 MATHEMATICAL ITALIC SMALL K
            "𝑚", // U+1D45A MATHEMATICAL ITALIC SMALL M
            "𝑛", // U+1D45B MATHEMATICAL ITALIC SMALL N
            "𝑜", // U+1D45C MATHEMATICAL ITALIC SMALL O
            "𝑟", // U+1D45F MATHEMATICAL ITALIC SMALL R
            "𝑞", // U+1D45E MATHEMATICAL ITALIC SMALL Q
            "𝑝", // U+1D45D MATHEMATICAL ITALIC SMALL P
            "𝑎", // U+1D44E MATHEMATICAL ITALIC SMALL A
            "𝑏", // U+1D44F MATHEMATICAL ITALIC SMALL B
            "𝑐", // U+1D450 MATHEMATICAL ITALIC SMALL C
            "𝑑", // U+1D451 MATHEMATICAL ITALIC SMALL D
            "𝑙", // U+1D459 MATHEMATICAL ITALIC SMALL L
        ];
        if index < CHARS.len() {
            Some(CHARS[index])
        } else {
            None
        }
    }

    /// LaTeX representations for Setvar metavariables.
    ///
    /// Latin letters are used as-is in LaTeX math mode.
    #[must_use]
    pub const fn latex_setvar(index: usize) -> Option<&'static str> {
        // Same as ASCII for Latin letters
        Self::ascii_setvar(index)
    }

    // ==================== CLASS CHARACTERS ====================

    /// ASCII representations for Class metavariables (Metamath-compatible).
    #[must_use]
    pub const fn ascii_class(index: usize) -> Option<&'static str> {
        /// See `crate::WIDE_CLASSES_ASCII`.
        const CHARS: &[&str] = WIDE_CLASSES_ASCII;
        if index < CHARS.len() {
            Some(CHARS[index])
        } else {
            None
        }
    }

    /// UTF-8 representations for Class metavariables (italic Latin uppercase).
    #[must_use]
    pub const fn utf8_class(index: usize) -> Option<&'static str> {
        /// See `crate::WIDE_CLASSES` for an equivalent string.
        const CHARS: &[&str] = &[
            "𝐴", // U+1D434 MATHEMATICAL ITALIC CAPITAL A
            "𝐵", // U+1D435 MATHEMATICAL ITALIC CAPITAL B
            "𝐶", // U+1D436 MATHEMATICAL ITALIC CAPITAL C
            "𝐷", // U+1D437 MATHEMATICAL ITALIC CAPITAL D
            "𝑃", // U+1D443 MATHEMATICAL ITALIC CAPITAL P
            "𝑄", // U+1D444 MATHEMATICAL ITALIC CAPITAL Q
            "𝑅", // U+1D445 MATHEMATICAL ITALIC CAPITAL R
            "𝑆", // U+1D446 MATHEMATICAL ITALIC CAPITAL S
            "𝑇", // U+1D447 MATHEMATICAL ITALIC CAPITAL T
            "𝑈", // U+1D448 MATHEMATICAL ITALIC CAPITAL U
            "𝐸", // U+1D438 MATHEMATICAL ITALIC CAPITAL E
            "𝐹", // U+1D439 MATHEMATICAL ITALIC CAPITAL F
            "𝐺", // U+1D43A MATHEMATICAL ITALIC CAPITAL G
            "𝐻", // U+1D43B MATHEMATICAL ITALIC CAPITAL H
            "𝐼", // U+1D43C MATHEMATICAL ITALIC CAPITAL I
            "𝐽", // U+1D43D MATHEMATICAL ITALIC CAPITAL J
            "𝐾", // U+1D43E MATHEMATICAL ITALIC CAPITAL K
            "𝐿", // U+1D43F MATHEMATICAL ITALIC CAPITAL L
            "𝑀", // U+1D440 MATHEMATICAL ITALIC CAPITAL M
            "𝑁", // U+1D441 MATHEMATICAL ITALIC CAPITAL N
            "𝑉", // U+1D449 MATHEMATICAL ITALIC CAPITAL V
            "𝑊", // U+1D44A MATHEMATICAL ITALIC CAPITAL W
            "𝑋", // U+1D44B MATHEMATICAL ITALIC CAPITAL X
            "𝑌", // U+1D44C MATHEMATICAL ITALIC CAPITAL Y
            "𝑍", // U+1D44D MATHEMATICAL ITALIC CAPITAL Z
            "𝑂", // U+1D442 MATHEMATICAL ITALIC CAPITAL O
        ];
        if index < CHARS.len() {
            Some(CHARS[index])
        } else {
            None
        }
    }

    /// LaTeX representations for Class metavariables.
    ///
    /// Latin letters are used as-is in LaTeX math mode.
    #[must_use]
    pub const fn latex_class(index: usize) -> Option<&'static str> {
        // Same as ASCII for Latin letters
        Self::ascii_class(index)
    }

    // ==================== TYPE DISPATCHERS ====================

    /// Get ASCII representation for any type.
    #[must_use]
    pub fn ascii_char(ty: &SimpleType, index: usize) -> Option<&'static str> {
        match ty {
            Boolean => Self::ascii_boolean(index),
            Setvar => Self::ascii_setvar(index),
            Class => Self::ascii_class(index),
        }
    }

    /// Get UTF-8 representation for any type.
    #[must_use]
    pub fn utf8_char(ty: &SimpleType, index: usize) -> Option<&'static str> {
        match ty {
            Boolean => Self::utf8_boolean(index),
            Setvar => Self::utf8_setvar(index),
            Class => Self::utf8_class(index),
        }
    }

    /// Get LaTeX representation for any type.
    #[must_use]
    pub fn latex_char(ty: &SimpleType, index: usize) -> Option<&'static str> {
        match ty {
            Boolean => Self::latex_boolean(index),
            Setvar => Self::latex_setvar(index),
            Class => Self::latex_class(index),
        }
    }

    /// Get maximum base index for a type (before decorators).
    #[must_use]
    pub const fn max_index(ty: &SimpleType) -> usize {
        match ty {
            Boolean => 11, // 12 chars (0..11)
            Setvar => 25,  // 26 chars (0..25)
            Class => 25,   // 26 chars (0..25)
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn boolean_char_counts_match() {
        // Count non-None entries
        let ascii_count = (0..20)
            .filter(|&i| WideCharSet::ascii_boolean(i).is_some())
            .count();
        let utf8_count = (0..20)
            .filter(|&i| WideCharSet::utf8_boolean(i).is_some())
            .count();
        let latex_count = (0..20)
            .filter(|&i| WideCharSet::latex_boolean(i).is_some())
            .count();

        assert_eq!(ascii_count, 12, "ASCII Booleans should have 12 entries");
        assert_eq!(utf8_count, 12, "UTF-8 Booleans should have 12 entries");
        assert_eq!(latex_count, 12, "LaTeX Booleans should have 12 entries");
    }

    #[test]
    fn setvar_char_counts_match() {
        let ascii_count = (0..30)
            .filter(|&i| WideCharSet::ascii_setvar(i).is_some())
            .count();
        let utf8_count = (0..30)
            .filter(|&i| WideCharSet::utf8_setvar(i).is_some())
            .count();
        let latex_count = (0..30)
            .filter(|&i| WideCharSet::latex_setvar(i).is_some())
            .count();

        assert_eq!(ascii_count, 26, "ASCII Setvars should have 26 entries");
        assert_eq!(utf8_count, 26, "UTF-8 Setvars should have 26 entries");
        assert_eq!(latex_count, 26, "LaTeX Setvars should have 26 entries");
    }

    #[test]
    fn class_char_counts_match() {
        let ascii_count = (0..30)
            .filter(|&i| WideCharSet::ascii_class(i).is_some())
            .count();
        let utf8_count = (0..30)
            .filter(|&i| WideCharSet::utf8_class(i).is_some())
            .count();
        let latex_count = (0..30)
            .filter(|&i| WideCharSet::latex_class(i).is_some())
            .count();

        assert_eq!(ascii_count, 26, "ASCII Classes should have 26 entries");
        assert_eq!(utf8_count, 26, "UTF-8 Classes should have 26 entries");
        assert_eq!(latex_count, 26, "LaTeX Classes should have 26 entries");
    }

    #[test]
    fn max_index_matches_counts() {
        assert_eq!(WideCharSet::max_index(&Boolean), 11); // 12 chars: 0..11
        assert_eq!(WideCharSet::max_index(&Setvar), 25); // 26 chars: 0..25
        assert_eq!(WideCharSet::max_index(&Class), 25); // 26 chars: 0..25
    }

    #[test]
    fn out_of_bounds_returns_none() {
        assert_eq!(WideCharSet::ascii_boolean(12), None);
        assert_eq!(WideCharSet::ascii_setvar(26), None);
        assert_eq!(WideCharSet::ascii_class(26), None);
    }

    #[test]
    fn sample_boolean_chars() {
        // First Boolean: φ
        assert_eq!(WideCharSet::ascii_boolean(0), Some("ph"));
        assert_eq!(WideCharSet::utf8_boolean(0), Some("𝜑"));
        assert_eq!(WideCharSet::latex_boolean(0), Some(r"\varphi"));

        // Second Boolean: ψ
        assert_eq!(WideCharSet::ascii_boolean(1), Some("ps"));
        assert_eq!(WideCharSet::utf8_boolean(1), Some("𝜓"));
        assert_eq!(WideCharSet::latex_boolean(1), Some(r"\psi"));
    }

    #[test]
    fn sample_setvar_chars() {
        // First Setvar: x
        assert_eq!(WideCharSet::ascii_setvar(0), Some("x"));
        assert_eq!(WideCharSet::utf8_setvar(0), Some("𝑥"));
        assert_eq!(WideCharSet::latex_setvar(0), Some("x"));

        // Second Setvar: y
        assert_eq!(WideCharSet::ascii_setvar(1), Some("y"));
        assert_eq!(WideCharSet::utf8_setvar(1), Some("𝑦"));
        assert_eq!(WideCharSet::latex_setvar(1), Some("y"));
    }

    #[test]
    fn sample_class_chars() {
        // First Class: A
        assert_eq!(WideCharSet::ascii_class(0), Some("A"));
        assert_eq!(WideCharSet::utf8_class(0), Some("𝐴"));
        assert_eq!(WideCharSet::latex_class(0), Some("A"));

        // Second Class: B
        assert_eq!(WideCharSet::ascii_class(1), Some("B"));
        assert_eq!(WideCharSet::utf8_class(1), Some("𝐵"));
        assert_eq!(WideCharSet::latex_class(1), Some("B"));
    }

    #[test]
    fn type_dispatchers_work() {
        // Test Boolean dispatch
        assert_eq!(WideCharSet::ascii_char(&Boolean, 0), Some("ph"));
        assert_eq!(WideCharSet::utf8_char(&Boolean, 0), Some("𝜑"));
        assert_eq!(WideCharSet::latex_char(&Boolean, 0), Some(r"\varphi"));

        // Test Setvar dispatch
        assert_eq!(WideCharSet::ascii_char(&Setvar, 0), Some("x"));

        // Test Class dispatch
        assert_eq!(WideCharSet::ascii_char(&Class, 0), Some("A"));
    }
}
