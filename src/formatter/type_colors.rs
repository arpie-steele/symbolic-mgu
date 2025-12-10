//! Type-color registry for metavariable coloring.
//!
//! This module provides a global registry mapping type names to colors.
//! Formatters can query this registry to determine how to color metavariables
//! based on their type (Boolean, Setvar, Class, or custom types).

use super::color::Color;
use std::collections::HashMap;
use std::sync::{OnceLock, RwLock};

/// Global registry mapping type names to colors.
///
/// Initialized with default colors for Boolean, Setvar, and Class types.
/// Applications can register custom colors for new types.
static TYPE_COLOR_REGISTRY: OnceLock<RwLock<HashMap<String, Color>>> = OnceLock::new();

/// Get or initialize the type-color registry.
///
/// Initializes the registry with default colors on first access:
/// - Boolean → Blue (#0088ff / xterm256:33)
/// - Setvar → Green (#00aa00 / xterm256:34)
/// - Class → Red (#cc0000 / xterm256:160)
#[must_use]
fn type_color_registry() -> &'static RwLock<HashMap<String, Color>> {
    TYPE_COLOR_REGISTRY.get_or_init(|| {
        let mut map = HashMap::new();

        // Default colors for standard types
        map.insert("Boolean".to_string(), Color::BLUE);
        map.insert("Setvar".to_string(), Color::GREEN);
        map.insert("Class".to_string(), Color::RED);

        RwLock::new(map)
    })
}

/// Register a color for a type.
///
/// # Arguments
///
/// * `type_name` - Name of the type (e.g., "Boolean", "Real")
/// * `color` - Color to associate with this type
///
/// # Examples
///
/// ```
/// use symbolic_mgu::{register_type_color, Color};
///
/// // Register a custom color for a new type
/// register_type_color("RealNumber", Color::new(220, "#ffaa00"));
/// ```
///
/// # Panics
///
/// Can panic
/// - if `RwLock` is poisoned because a writer panics while holding an exclusive lock, or
/// - if the lock is already held by the current thread.
pub fn register_type_color(type_name: impl Into<String>, color: Color) {
    type_color_registry()
        .write()
        .expect("type color registry lock poisoned")
        .insert(type_name.into(), color);
}

/// Get color for a type by name.
///
/// Returns `None` if the type name is not registered.
///
/// # Arguments
///
/// * `type_name` - Name of the type to look up
///
/// # Examples
///
/// ```
/// use symbolic_mgu::{get_type_color, Color};
///
/// // Get default color for Boolean type
/// let blue = get_type_color("Boolean");
/// assert_eq!(blue, Some(Color::BLUE));
///
/// // Unregistered type returns None
/// let unknown = get_type_color("UnknownType");
/// assert_eq!(unknown, None);
/// ```
///
/// # Panics
///
/// Can panic
/// - if `RwLock` is poisoned because a writer panics while holding an exclusive lock, or
/// - if the lock is already held by the current thread.
#[must_use]
pub fn get_type_color(type_name: &str) -> Option<Color> {
    type_color_registry()
        .read()
        .expect("type color registry lock poisoned")
        .get(type_name)
        .copied()
}

/// Get color for a type using the Type trait.
///
/// Uses the type's trait methods to determine its name:
/// - `is_boolean()` → "Boolean"
/// - `is_setvar()` → "Setvar"
/// - `is_class()` → "Class"
/// - Otherwise returns None
///
/// # Examples
///
/// ```
/// use symbolic_mgu::{get_type_color_from_trait, Color, SimpleType};
///
/// let bool_color = get_type_color_from_trait(&SimpleType::Boolean);
/// assert_eq!(bool_color, Some(Color::BLUE));
/// ```
#[must_use]
pub fn get_type_color_from_trait(ty: &impl crate::Type) -> Option<Color> {
    let type_name = if ty.is_boolean() {
        "Boolean"
    } else if ty.is_setvar() {
        "Setvar"
    } else if ty.is_class() {
        "Class"
    } else {
        return None;
    };

    get_type_color(type_name)
}
