//! Define [`AsciiMetaVar`], an enum which represents ASCII [`Metavariable`] legal values.
//!
//! [`AsciiMetaVar`]: `crate::AsciiMetaVar`
//! [`Metavariable`]: `crate::Metavariable`

use crate::{byte_try_from_signed, byte_try_from_unsigned, MguError, SimpleType};
use std::convert::{TryFrom, TryInto};

/// Named ASCII metavariable variants.
///
/// This enum provides named constants for all valid ASCII metavariable characters.
/// Unlike [`MetaByte`] which is a general wrapper for any `u8` value, this enum
/// explicitly enumerates the 32 valid ASCII metavariables used in the system.
///
/// [`MetaByte`]: `crate::MetaByte`
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
#[repr(u8)]
pub enum AsciiMetaVar {
    /// <span style="color: #C3C">A</span>, a class metavariable.
    AClass = b'A',
    /// <span style="color: #C3C">B</span>, a class metavariable.
    BClass,
    /// <span style="color: #C3C">C</span>, a class metavariable.
    CClass,
    /// <span style="color: #C3C">D</span>, a class metavariable.
    DClass,
    /// <span style="color: #C3C">F</span>, a class metavariable.
    FClass = b'F',
    /// <span style="color: #C3C">G</span>, a class metavariable.
    GClass,
    /// <span style="color: #C3C">H</span>, a class metavariable.
    HClass,
    /// <span style="color: #C3C">J</span>, a class metavariable.
    JClass = b'J',
    /// <span style="color: #C3C">K</span>, a class metavariable.
    KClass,
    /// <span style="color: #C3C">L</span>, a class metavariable.
    LClass,
    /// <span style="color: #C3C">M</span>, a class metavariable.
    MClass,
    /// <span style="color: blue">P</span>, a Boolean metavariable.
    PBoolean = b'P',
    /// <span style="color: blue">Q</span>, a Boolean metavariable.
    QBoolean,
    /// <span style="color: blue">R</span>, a Boolean metavariable.
    RBoolean,
    /// <span style="color: blue">S</span>, a Boolean metavariable.
    SBoolean,
    /// <span style="color: blue">T</span>, a Boolean metavariable.
    TBoolean,
    /// <span style="color: blue">U</span>, a Boolean metavariable.
    UBoolean,
    /// <span style="color: blue">V</span>, a Boolean metavariable.
    VBoolean,
    /// <span style="color: blue">W</span>, a Boolean metavariable.
    WBoolean,
    /// <span style="color: blue">X</span>, a Boolean metavariable.
    XBoolean,
    /// <span style="color: blue">Y</span>, a Boolean metavariable.
    YBoolean,
    /// <span style="color: blue">Z</span>, a Boolean metavariable.
    ZBoolean,
    /// <span style="color: red">a</span>, a `Setvar` metavariable.
    ASet = b'a',
    /// <span style="color: red">b</span>, a `Setvar` metavariable.
    BSet,
    /// <span style="color: red">c</span>, a `Setvar` metavariable.
    CSet,
    /// <span style="color: red">d</span>, a `Setvar` metavariable.
    DSet,
    /// <span style="color: red">f</span>, a `Setvar` metavariable.
    FSet = b'f',
    /// <span style="color: red">g</span>, a `Setvar` metavariable.
    GSet,
    /// <span style="color: red">u</span>, a `Setvar` metavariable.
    USet = b'u',
    /// <span style="color: red">v</span>, a `Setvar` metavariable.
    VSet,
    /// <span style="color: red">w</span>, a `Setvar` metavariable.
    WSet = b'w',
    /// <span style="color: red">x</span>, a `Setvar` metavariable.
    XSet = b'x',
    /// <span style="color: red">y</span>, a `Setvar` metavariable.
    YSet,
    /// <span style="color: red">z</span>, a `Setvar` metavariable.
    ZSet,
}

impl AsciiMetaVar {
    /// Convert a value of [`AsciiMetaVar`] to presentation order within those of the same type.
    #[must_use]
    pub fn to_order(self) -> u8 {
        use AsciiMetaVar::*;
        match self {
            AClass | PBoolean | XSet => 0,
            BClass | QBoolean | YSet => 1,
            CClass | RBoolean | ZSet => 2,
            DClass | SBoolean | ASet => 3,
            FClass | TBoolean | BSet => 4,
            GClass | UBoolean | CSet => 5,
            HClass | VBoolean | DSet => 6,
            JClass | WBoolean | WSet => 7,
            KClass | XBoolean | USet => 8,
            LClass | YBoolean | VSet => 9,
            MClass | ZBoolean | FSet => 10,
            GSet => 11,
        }
    }

    /// Describe [` SimpleType`] of this for this instance of [`AsciiMetaVar`].
    #[must_use]
    pub fn to_type(self) -> SimpleType {
        use AsciiMetaVar::*;
        use SimpleType::*;
        match self {
            AClass | BClass | CClass | DClass | FClass | GClass | HClass | JClass | KClass
            | LClass | MClass => Class,

            PBoolean | QBoolean | RBoolean | SBoolean | TBoolean | UBoolean | VBoolean
            | WBoolean | XBoolean | YBoolean | ZBoolean => Boolean,

            ASet | BSet | CSet | DSet | FSet | GSet | USet | VSet | WSet | XSet | YSet | ZSet => {
                Setvar
            }
        }
    }
}

impl TryFrom<u8> for AsciiMetaVar {
    type Error = MguError;

    /// Performs the conversion.
    ///
    /// Converts ASCII display value back to [`AsciiMetaVar`] enum value.
    fn try_from(value: u8) -> Result<Self, Self::Error> {
        use AsciiMetaVar::*;
        match value {
            b'A' => Ok(AClass),
            b'B' => Ok(BClass),
            b'C' => Ok(CClass),
            b'D' => Ok(DClass),
            b'F' => Ok(FClass),
            b'G' => Ok(GClass),
            b'H' => Ok(HClass),
            b'J' => Ok(JClass),
            b'K' => Ok(KClass),
            b'L' => Ok(LClass),
            b'M' => Ok(MClass),
            b'P' => Ok(PBoolean),
            b'Q' => Ok(QBoolean),
            b'R' => Ok(RBoolean),
            b'S' => Ok(SBoolean),
            b'T' => Ok(TBoolean),
            b'U' => Ok(UBoolean),
            b'V' => Ok(VBoolean),
            b'W' => Ok(WBoolean),
            b'X' => Ok(XBoolean),
            b'Y' => Ok(YBoolean),
            b'Z' => Ok(ZBoolean),
            b'a' => Ok(ASet),
            b'b' => Ok(BSet),
            b'c' => Ok(CSet),
            b'd' => Ok(DSet),
            b'f' => Ok(FSet),
            b'g' => Ok(GSet),
            b'u' => Ok(USet),
            b'v' => Ok(VSet),
            b'w' => Ok(WSet),
            b'x' => Ok(XSet),
            b'y' => Ok(YSet),
            b'z' => Ok(ZSet),
            _ => Err(MguError::UnsignedValueUnsupported(
                value as u128,
                stringify!(AsciiMetaVar),
            )),
        }
    }
}

impl TryFrom<i8> for AsciiMetaVar {
    type Error = MguError;

    /// Performs the conversion.
    ///
    /// Converts ASCII display value back to [`AsciiMetaVar`] enum value.
    fn try_from(value: i8) -> Result<Self, Self::Error> {
        if 0 <= value {
            (value as u8).try_into()
        } else {
            Err(MguError::SignedValueOutOfRange(
                value as i128,
                stringify!(AsciiMetaVar),
                0,
                u8::MAX as u32,
            ))
        }
    }
}

byte_try_from_signed!(AsciiMetaVar: i16, i32, i64, i128, isize,);

byte_try_from_unsigned!(AsciiMetaVar: char, u16, u32, u64, u128, usize,);

#[cfg(test)]
mod tests {
    use std::collections::HashSet;

    use super::super::meta_byte::{OUR_BOOLEANS, OUR_CLASSES, OUR_SETVARS};
    use super::*;

    #[test]
    fn ascii_metavar() {
        let mut seen: HashSet<u8> = HashSet::new();
        for (my_type, my_string) in [
            (SimpleType::Boolean, OUR_BOOLEANS),
            (SimpleType::Setvar, OUR_SETVARS),
            (SimpleType::Class, OUR_CLASSES),
        ] {
            for (index, unsigned_byte) in my_string.bytes().enumerate() {
                seen.insert(unsigned_byte);
                let our_enum: Result<AsciiMetaVar, _> = unsigned_byte.try_into();
                assert!(
                    our_enum.is_ok(),
                    "Conversion of {0} into a AsciiMetaVar enum value of type {my_type} failed.",
                    unsigned_byte as char
                );
                let our_enum = our_enum.unwrap();
                assert_eq!(
                    our_enum as u8, unsigned_byte,
                    "{our_enum:?} as u8 ≠ {unsigned_byte}."
                );
                assert_eq!(
                    our_enum.to_type(),
                    my_type,
                    "{our_enum:?}.to_type() ≠ {my_type}."
                );
                assert_eq!(
                    our_enum.to_order() as usize,
                    index,
                    "{our_enum:?}.to_order() ≠ {index}."
                );
                let byte_display = unsigned_byte as char;

                let mb_display = format!("{our_enum:?}");
                let mb_display_first = mb_display.chars().next().unwrap();
                let mb_diplay_class = &mb_display[1..];
                assert_eq!(
                    mb_display_first.to_ascii_uppercase(),
                    byte_display.to_ascii_uppercase()
                );
                assert_eq!(SimpleType::name_to_value(mb_diplay_class), Some(my_type));
            }
        }
        for unsigned_byte in 0..u8::MAX {
            if seen.contains(&unsigned_byte) {
                continue;
            }
            let our_enum: Result<AsciiMetaVar, _> = unsigned_byte.try_into();
            if unsigned_byte.is_ascii_graphic() {
                assert!(
                    our_enum.is_err(),
                    "Conversion of {0:?} into a AsciiMetaVar enum value didn't fail as planned.",
                    unsigned_byte as char
                );
            } else {
                assert!(
                    our_enum.is_err(),
                    "Conversion of \\x{0:02x} into a AsciiMetaVar enum value didn't fail as planned.",
                    unsigned_byte
                );
            }
        }
    }
}
