//! Introduce an implementation of the [`Metavariable`] trait for [`MetaByte`].

use crate::Metavariable;
use crate::MetavariableFactory;
use crate::MguError;
use crate::SimpleType;

/// Uppercase letters from the second half of the Latin alphabet, used for ASCII Boolean metavariables.
pub const OUR_BOOLEANS: &str = "PQRSTUVWXYZ";

/// Uppercase letters from the Latin alphabet used for ASCII `Setvar` metavariables.
pub const OUR_SETVARS: &str = "xyzabcdwuvfg";

/// Capital letters from the first half of the Latin alphabet, used for ASCII Class metavariables.
pub const OUR_CLASSES: &str = "ABCDFGHJKLM";

/// A byte-sized metavariable representation.
///
/// This type wraps a `u8` and implements the [`Metavariable`] trait,
/// using ASCII characters to represent different types of metavariables:
/// - Boolean: P, Q, R, S, T, U, V, W, X, Y, Z
/// - `Setvar`: x, y, z, a, b, c, d, w, u, v, f, g
/// - Class: A, B, C, D, F, G, H, J, K, L, M
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct MetaByte(pub u8);

impl MetaByte {
    /// From a type, return maximum valid index.
    pub fn max_index_by_type(typ: SimpleType) -> usize {
        use SimpleType::*;
        let data = match typ {
            Boolean => OUR_BOOLEANS,
            Setvar => OUR_SETVARS,
            Class => OUR_CLASSES,
        };
        match data.len() {
            0 => 0,
            len => len - 1,
        }
    }

    /// From a type and index, create an ASCII metavariable representation.
    ///
    /// There are at least 10 possible values per TYPE.
    ///
    /// # Errors
    /// - It is an error if the index is out-of-range.
    pub fn try_from_type_and_index(my_type: SimpleType, my_index: usize) -> Result<Self, MguError> {
        use SimpleType::*;
        let data = match my_type {
            Boolean => OUR_BOOLEANS,
            Setvar => OUR_SETVARS,
            Class => OUR_CLASSES,
        };
        let n = data.len();
        if my_index < n {
            Ok(MetaByte(data.as_bytes()[my_index]))
        } else {
            Err(MguError::from_index_and_len(Some(my_type), my_index, n))
        }
    }

    /// Return an iterator over Metavariables.
    ///
    /// Every metavariable has a string display form.
    ///
    /// This methods need not check that the item is valid data for Metavariable purposes.
    pub fn to_str(&self) -> String {
        if self.0.is_ascii() && !self.0.is_ascii_control() {
            format!("{0}", self.0 as char)
        } else {
            format!("\\{0:02x}", self.0)
        }
    }
}

impl Metavariable for MetaByte {
    type Type = SimpleType;

    /// Describe ASCII metavariable as ordered pairs of a type and an arbitrary index.
    ///
    /// Some implementations will include values that do no map to a metavariable,
    /// so we allow this function to return None.
    fn get_type_and_index(&self) -> Result<(SimpleType, usize), MguError> {
        use SimpleType::*;
        let our_type;
        let data;
        if OUR_BOOLEANS.contains(self.0 as char) {
            our_type = Boolean;
            data = OUR_BOOLEANS;
        } else if OUR_SETVARS.contains(self.0 as char) {
            our_type = Setvar;
            data = OUR_SETVARS;
        } else if OUR_CLASSES.contains(self.0 as char) {
            our_type = Class;
            data = OUR_CLASSES;
        } else {
            return Err(MguError::UnknownMetavariable(
                stringify!(MetaByte),
                self.to_string(),
            ));
        }
        Ok((our_type, data.find(self.0 as char).unwrap()))
    }

    fn max_index_by_type(typ: SimpleType) -> usize {
        Self::max_index_by_type(typ)
    }

    fn try_from_type_and_index(my_type: SimpleType, my_index: usize) -> Result<Self, MguError> {
        Self::try_from_type_and_index(my_type, my_index)
    }

    fn format_with(&self, formatter: &dyn crate::formatter::OutputFormatter) -> String {
        match formatter.name() {
            "ascii" => self.to_ascii(),
            "latex" => self.to_latex(),
            "html" | "html-color" => self.to_html(formatter),
            "utf8-color" => self.to_utf8_color(formatter),
            _ => self.to_utf8(), // Default: UTF-8
        }
    }

    fn to_ascii(&self) -> String {
        // Metamath-style ASCII names
        match self.0 as char {
            // Boolean variables: ph, ps, ch, th, ta, et, ze, si, rh, mu, la
            'P' => "ph".to_string(),
            'Q' => "ps".to_string(),
            'R' => "ch".to_string(),
            'S' => "th".to_string(),
            'T' => "ta".to_string(),
            'U' => "et".to_string(),
            'V' => "ze".to_string(),
            'W' => "si".to_string(),
            'X' => "rh".to_string(),
            'Y' => "mu".to_string(),
            'Z' => "la".to_string(),
            // Setvar and Class: use character as-is
            c => format!("{}", c),
        }
    }

    fn to_utf8(&self) -> String {
        // Same as Display implementation for now
        self.to_str()
    }
}

impl MetaByte {
    /// Get LaTeX representation.
    fn to_latex(self) -> String {
        match self.0 as char {
            // Boolean variables: Greek letters in LaTeX
            'P' => r"\varphi".to_string(),
            'Q' => r"\psi".to_string(),
            'R' => r"\chi".to_string(),
            'S' => r"\theta".to_string(),
            'T' => r"\tau".to_string(),
            'U' => r"\eta".to_string(),
            'V' => r"\zeta".to_string(),
            'W' => r"\sigma".to_string(),
            'X' => r"\rho".to_string(),
            'Y' => r"\mu".to_string(),
            'Z' => r"\lambda".to_string(),
            // Setvar: lowercase variables
            c if c.is_ascii_lowercase() => format!("{}", c),
            // Class: uppercase variables
            c => format!("{}", c),
        }
    }

    /// Get HTML representation with optional coloring.
    fn to_html(self, formatter: &dyn crate::formatter::OutputFormatter) -> String {
        let char_str = self.to_str();

        if let Ok((typ, _)) = self.get_type_and_index() {
            use SimpleType::*;
            let color = match typ {
                Boolean => formatter.get_boolean_color(),
                Setvar => formatter.get_setvar_color(),
                Class => formatter.get_class_color(),
            };

            if let Some(color) = color {
                return format!("<i style='color:{}'>{}</i>", color.to_html(), char_str);
            }
        }

        format!("<i>{}</i>", char_str)
    }

    /// Get UTF-8 representation with ANSI color codes.
    fn to_utf8_color(self, formatter: &dyn crate::formatter::OutputFormatter) -> String {
        let char_str = self.to_str();

        if let Ok((typ, _)) = self.get_type_and_index() {
            use SimpleType::*;
            let color = match typ {
                Boolean => formatter.get_boolean_color(),
                Setvar => formatter.get_setvar_color(),
                Class => formatter.get_class_color(),
            };

            if let Some(color) = color {
                return format!("\x1b[38;5;{}m{}\x1b[0m", color.to_xterm256(), char_str);
            }
        }

        char_str
    }
}

impl std::fmt::Display for MetaByte {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.to_str())
    }
}

impl From<u8> for MetaByte {
    fn from(value: u8) -> Self {
        MetaByte(value)
    }
}

/// A very simple example of a factory for a very simple metavariable.
#[derive(Debug)]
pub struct MetaByteFactory();

impl MetavariableFactory for MetaByteFactory {
    type MetavariableType = <MetaByte as Metavariable>::Type;

    type Metavariable = MetaByte;

    type MetavariableIterator<'a> = std::vec::IntoIter<MetaByte>;

    fn create_by_name(&self, name: &str) -> Result<Self::Metavariable, MguError> {
        if name.is_ascii() && name.len() == 1 {
            for data in [OUR_BOOLEANS, OUR_SETVARS, OUR_CLASSES] {
                let found = OUR_BOOLEANS.find(name);
                if let Some(index) = found {
                    return Ok(MetaByte(data.as_bytes()[index]));
                }
            }
        }
        Err(MguError::UnknownMetavariable(
            stringify!(MetaByte),
            name.to_owned(),
        ))
    }

    fn create_by_type_and_index(
        &self,
        the_type: &Self::MetavariableType,
        index: usize,
    ) -> Result<Self::Metavariable, MguError> {
        MetaByte::try_from_type_and_index(*the_type, index)
    }

    #[allow(clippy::unnecessary_to_owned)]
    fn list_metavariables_by_type(
        &self,
        the_type: &Self::MetavariableType,
    ) -> Self::MetavariableIterator<'_> {
        use SimpleType::*;
        let data = match the_type {
            Boolean => OUR_BOOLEANS,
            Setvar => OUR_SETVARS,
            Class => OUR_CLASSES,
        };
        data.as_bytes()
            .to_vec()
            .into_iter()
            .map(MetaByte)
            .collect::<Vec<_>>()
            .into_iter()
    }
}
