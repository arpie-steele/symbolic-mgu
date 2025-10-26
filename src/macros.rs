//! Public macros.

/// Check that the single type supplied is a primitive type.
///
/// Throws a compile-time error if utilized with something other
/// than a primitive type.
///
/// # Examples
///
/// ```compile_fail
/// use symbolic_mgu::enforce_primitive_type;
/// enforce_primitive_type!(str);
/// ```
///
/// ```
/// use symbolic_mgu::enforce_primitive_type;
/// enforce_primitive_type!(i16);
/// ```
#[macro_export]
macro_rules! enforce_primitive_type {
    (bool) => {};
    (i8) => {};
    (i16) => {};
    (i32) => {};
    (i64) => {};
    (i128) => {};
    (isize) => {};
    (u8) => {};
    (u16) => {};
    (char) => {};
    (u32) => {};
    (u64) => {};
    (u128) => {};
    (usize) => {};
    (f16) => {};
    (f32) => {};
    (f64) => {};
    (f128) => {};
    ($type:ident) => {
        compile_error!("Argument is not recognized as a primitive type.");
    };
}

/// Check that the single type supplied is a legal integer larger
/// than a byte.
///
/// Throws a compile-time error if utilized with a [`bool`], [`i8`],
/// [`u8`], [`f32`], or [`f64`].
///
/// # Examples
///
/// ```compile_fail
/// use symbolic_mgu::{enforce_bigger_than_byte, enforce_primitive_type};
/// enforce_bigger_than_byte!(u8);
/// ```
///
/// ```
/// use symbolic_mgu::{enforce_bigger_than_byte, enforce_primitive_type};
/// // next line expands to:
/// //      debug_assert!(i16::MAX as usize > u8::MAX as usize);
/// enforce_bigger_than_byte!(i16);
/// ```
#[macro_export]
macro_rules! enforce_bigger_than_byte {
    (bool) => {
        compile_error!("The primitive type needs to be larger than a byte.");
    };
    (i8) => {
        compile_error!("The primitive type needs to be larger than a byte.");
    };
    (u8) => {
        compile_error!("The primitive type needs to be larger than a byte.");
    };
    (f16) => {
        compile_error!("The primitive type needs to be an integer larger than a byte.");
    };
    (f32) => {
        compile_error!("The primitive type needs to be an integer larger than a byte.");
    };
    (f64) => {
        compile_error!("The primitive type needs to be an integer larger than a byte.");
    };
    (f128) => {
        compile_error!("The primitive type needs to be an integer larger than a byte.");
    };
    ($type:ident) => {
        $crate::enforce_primitive_type!($type);
        debug_assert!($type::MAX as usize > u8::MAX as usize);
    };
}

/// Implements fallible conversions (`TryFrom`) from signed integer
/// types larger than 8 bits into a target enum or new type represented
/// by `u8`.
///
/// This macro is typically used when you have an enum (or wrapper
/// type) backed by a `u8`, and you want to allow safe conversion
/// from wider signed integer types (e.g. `i16`, `i32`, `i64`) with
/// bounds checking.
///
/// If the input value is within the valid `u8` range (`0..=255`),
/// the conversion will succeed or fail as if it were first converted
/// to `u8`. Otherwise, it fails with [`MguError::SignedValueOutOfRange`].
///
/// # Syntax
///
/// ```ignore
/// byte_try_from_signed!(DestinationType: SourceType1, SourceType2, ...);
/// ```
///
/// - `DestinationType`: The `u8`-backed type to implement `TryFrom`
///   for.
/// - `SourceTypeN`: One or more signed integer types larger than
///   8 bits (e.g. `i16`, `i32`, `i64`, `isize`).
///
/// # Example
///
/// ```rust
/// use symbolic_mgu::{byte_try_from_signed, MguError};
/// use std::convert::{TryFrom, TryInto};
///
/// #[repr(u8)]
/// enum SmallCode {
///     A = 1,
///     B = 2,
/// }
///
/// impl TryFrom<u8> for SmallCode {
///     type Error = MguError;
///
///     /// Performs the conversion.
///     ///
///     /// Converts a byte to [`NewType`] enum value.
///     fn try_from(value: u8) -> Result<Self, Self::Error> {
///         match value {
///             1 => Ok(SmallCode::A),
///             2 => Ok(SmallCode::B),
///             _ => Err(MguError::UnsignedValueUnsupported(
///                 value as u128,
///                 stringify!(NewType),
///             )),
///         }
///     }
/// }
///
/// // Provide conversions from `i16` and `i32` into `SmallCode`.
/// byte_try_from_signed!(SmallCode: i16, i32);
///
/// fn main() -> Result<(), MguError> {
///     let a: SmallCode = 1i16.try_into()?;  // Ok(SmallCode::A)
///     let c: SmallCode = 3i32.try_into().unwrap_or(SmallCode::B); // Err(UnsignedValueUnsupported)
///     let d: SmallCode = 999i32.try_into().unwrap_or(SmallCode::B); // Err(SignedValueOutOfRange)
///     Ok(())
/// }
/// ```
///
/// # See also
///
/// - [`byte_try_from_unsigned!`] for conversions from unsigned types.
///
/// [`byte_try_from_unsigned!`]: crate::byte_try_from_unsigned
/// [`MguError::SignedValueOutOfRange`]: crate::MguError::SignedValueOutOfRange
#[macro_export]
macro_rules! byte_try_from_signed {
    ($destination:ident: $($source:ident),* $(,)?) => {
        $(
            impl TryFrom<$source> for $destination {
                type Error = MguError;

                /// Performs the conversion.
                ///
                #[doc = "Converts ASCII display value back to"]
                #[doc = concat!("[`", stringify!($destination), "`]")]
                #[doc = "enum value."]
                #[doc = ""]
                #[doc = "# Errors"]
                #[doc = ""]
		#[doc = "Returns [`MguError::SignedValueOutOfRange`]"]
		#[doc = "if the input value is negative or greater"]
                #[doc = "than `u8::MAX`."]
                fn try_from(value: $source) -> Result<Self, Self::Error> {
                      $crate::enforce_bigger_than_byte!($source);
                    if 0 <= value && value <= u8::MAX as $source {
                        (value as u8).try_into()
                    } else {
			Err(MguError::SignedValueOutOfRange(
                            value as i128,
                            stringify!($destination),
                            0,
                            u8::MAX as u32,
                        ))
                    }
                }
            }
        )*
    };
}

/// Implements fallible conversions (`TryFrom`) from unsigned integer
/// types larger than 8 bits into a target enum or new type represented
/// by `u8`.
///
/// This macro is typically used when you have an enum (or wrapper
/// type) backed by a `u8`, and you want to allow safe conversion
/// from wider signed integer types (e.g. `u16`, `u32`, `u64`) with
/// bounds checking.
///
/// If the input value is within the valid `u8` range (`0..=255`),
/// the conversion will succeed or fail as if it were first converted
/// to `u8`. Otherwise, it fails with
/// [`MguError::UnsignedValueOutOfRange`].
///
/// # Syntax
///
/// ```ignore
/// byte_try_from_unsigned!(DestinationType: SourceType1, SourceType2, ...);
/// ```
///
/// - `DestinationType`: The `u8`-backed type to implement `TryFrom` for.
/// - `SourceTypeN`: One or more signed integer types larger than 8 bits
///   (e.g. `u16`, `u32`, `u64`, `usize`).
///
/// # Example
///
/// ```ignore
/// use symbolic_mgu::{
///     MguError, byte_try_from_signed, byte_try_from_unsigned,
///     enforce_bigger_than_byte, enforce_primitive_type,
/// };
///
/// #[derive(Debug, Clone, Copy, PartialEq, Eq)]
/// #[repr(u8)]
/// pub enum NewType {
///     ...
/// }
///
/// impl TryFrom<u8> for NewType {
///     type Error = MguError;
///
///     /// Performs the conversion.
///     ///
///     /// Converts a byte to [`NewType`] enum value.
///     fn try_from(value: u8) -> Result<Self, Self::Error> {
///         use NewType::*;
///         match value {
///             ...
///             _ => Err(MguError::UnsignedValueUnsupported(
///                 value as u128,
///                 stringify!(NewType),
///             )),
///         }
///     }
/// }
///
/// byte_try_from_signed!(NewType: i16, i32, i64, i128, isize,);
///
/// byte_try_from_unsigned!(NewType: char, u16, u32, u64, u128, usize,);
/// ```
///
/// # See also
///
/// - [`byte_try_from_signed!`] for conversions from signed types.
///
/// [`byte_try_from_signed!`]: crate::byte_try_from_signed
/// [`MguError::UnsignedValueOutOfRange`]: crate::MguError::UnsignedValueOutOfRange
#[macro_export]
macro_rules! byte_try_from_unsigned {
    ($destination:ident: $($source:ident),* $(,)?) => {
        $(
            impl TryFrom<$source> for $destination {
                type Error = MguError;

                /// Performs the conversion.
                ///
                #[doc = "Converts ASCII display value back to"]
                #[doc = concat!("[`", stringify!($destination), "`]")]
                #[doc = "enum value."]
                #[doc = ""]
                #[doc = "# Errors"]
                #[doc = ""]
		#[doc = "Returns [`MguError::SignedValueOutOfRange`]"]
		#[doc = "if the input value is greater than `u8::MAX`."]
                fn try_from(value: $source) -> Result<Self, Self::Error> {
                    $crate::enforce_bigger_than_byte!($source);
                    if value <= u8::MAX as $source {
                        (value as u8).try_into()
                    } else {
                        Err(MguError::UnsignedValueOutOfRange(
                            value as u128,
                            stringify!($destination),
                            0,
                            u8::MAX as u32
                        ))
                    }
                }
            }
        )*
    };
}

/// Returns the last identifier in a whitespace-separated sequence.
///
/// This is a small helper macro for [`dlgt0!`], allowing it to
/// distinguish whether the receiver is `&self` or `&mut self`.
///
/// # Examples
///
/// ```
/// use symbolic_mgu::last_ident;
///
/// let (word, three, two, one, contact) = ("bird", "3", "2", "1", "Contact!");
///
/// assert_eq!(last_ident!(word), "bird");
/// assert_eq!(last_ident!(three two one contact), "Contact!");
/// ```
///
/// [`dlgt0!`]: `crate::dlgt0`
#[macro_export]
macro_rules! last_ident {
    (
        $first:ident
    ) => {
        $first
    };
    (
        $first:ident $($others:ident)+
    ) => {
        $crate::last_ident! { $($others)+ }
    };
}

/// Generates a wrapper method that delegates its call to an inner
/// field.
///
/// This macro reduces boilerplate when forwarding methods through
/// layers of wrapper structs. It supports both `&self` and
/// `&mut self` receivers, arbitrary visibility (`pub`, `pub(crate)`,
/// or none), and optional doc comments and attributes.
///
/// # Syntax
///
/// ```ignore
/// dlgt0! {
///     $(#[$meta:meta])*
///     $vis:vis fn $new_name:ident ( &$($self:ident)+ $(, $arg:ident : $typ:ty)* )
///     $(-> $ret:ty)? => $($field:tt).+
/// }
/// ```
///
/// - `$(#[$meta:meta])*`: Optional attributes such as `/// doc comments`.
/// - `$vis:vis`: Optional method visibility (`pub`, `pub(crate)`, etc.).
/// - `$new_name:ident`: The name of the new wrapper method.
/// - `&$($self:ident)+`: Either `&self` or `&mut self`.
/// - `$arg : $typ`: Zero or more method parameters.
/// - `$(-> $ret:ty)?`: Optional return type.
/// - `$($field:tt).+`: The field path to which the call is delegated.
///   Both named and numbered structures may be navigated.
///
/// # Examples
///
/// ```rust
/// use symbolic_mgu::dlgt0;
///
/// struct C;
/// impl C {
///     fn foo(&self) -> i32 { 42 }
///     fn bar(&mut self, x: i32) { println!("C got {}", x); }
/// }
///
/// struct B { c: C }
///
/// impl B {
///     dlgt0!(
///         /// Delegates to `C::foo`.
///         pub fn foo_in_b(&self) -> i32 => c.foo
///     );
///
///     dlgt0!(
///         /// Delegates to `C::bar`.
///         fn bar_in_b(&mut self, x: i32) => c.bar
///     );
/// }
/// ```
#[macro_export]
macro_rules! dlgt0 {
    (
        $(#[$meta:meta])*
        $vis:vis fn $new_name:ident (&$($self:ident)+$(,$arg:ident:$typ:ty)* )
        $(-> $ret:ty)? =>  $($field:tt).+
    ) => {
        $(#[$meta])*
        $vis fn $new_name(&$($self)+$(,$arg: $typ),*) $(-> $ret)? {
            $crate::last_ident!{ $($self)+ }.$($field).+($($arg),*)
        }
    };
}

/// Helper macro for defining enums with rich, structured documentation.
///
/// This macro is a one-time utility used to reduce boilerplate in the
/// definition of [`NodeBytes`]. It generates enum variants with
/// automatically attached documentation, including:
///
/// - A header section (`$head`) shown as doc lines.
/// - A "Syntax" section with a single syntax string.
/// - A "Definition" section listing one or more definition strings.
///
/// The generated enum variants can also include explicit discriminant
/// values (`= $value`).
///
/// # Syntax
///
/// ```ignore
/// enum0! {
///     $(#[$meta:meta])*
///     $vis:vis enum $name:ident {
///         {
///             $($head:literal),+;
///             $syntax:literal;
///             $($defs:literal),+;
///             $entry:ident $(= $value:literal)?
///         },*
///     }
/// }
/// ```
///
/// # Example
///
/// ```rust
/// use symbolic_mgu::enum0;
///
/// enum0! {
///     /// Example enum generated by `enum0!`.
///     pub enum Example {
///         { "Add two numbers"; "x + y"; "Sum of two integers"; Add },
///         { "Subtract numbers"; "x - y"; "Difference of two integers"; Sub = 2 }
///     }
/// }
/// ```
///
/// [`NodeBytes`]: crate::NodeBytes
#[macro_export]
macro_rules! enum0 {
    (
        $(#[$meta:meta])*
        $vis:vis enum $name:ident {
            $({$($head:literal),+; $syntax:literal; $($defs:literal),+; $entry:ident $(= $value:literal)?}),*
        }
    ) => {
        $(#[$meta])*
        $vis enum $name {
            $($(
        #[doc = $head])+
        #[doc = ""]
        #[doc = "Syntax:"]
        #[doc = concat!("* `", $syntax, "`")]
        #[doc = ""]
        #[doc = "Definition:"]
        #[doc = ""]$(
            #[doc = concat!("* `", $defs, "`")])+
        $entry $(= $value)?),*
        }
    };
}
