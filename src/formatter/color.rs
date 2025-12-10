//! Simple color representation for terminal and HTML output.

/// Simple color representation supporting both terminal and HTML output.
///
/// Colors are specified using xterm256 color codes (0-255) and HTML hex colors.
/// This avoids complex color theory (RGB → XYZ → Lab conversions) while providing
/// practical color support for formatters.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Color {
    /// xterm256 color code (0-255) for terminal output
    xterm256: u8,
    /// HTML hex color for web output
    html_hex: &'static str,
}

impl Color {
    /// Create a new Color with xterm256 and HTML hex values.
    ///
    /// # Arguments
    ///
    /// * `xterm256` - xterm256 color code (0-255)
    /// * `html_hex` - HTML hex color string (e.g., "#0088ff")
    ///
    /// # Examples
    ///
    /// ```
    /// use symbolic_mgu::Color;
    ///
    /// let blue = Color::new(33, "#0088ff");
    /// assert_eq!(blue.to_xterm256(), 33);
    /// assert_eq!(blue.to_html(), "#0088ff");
    /// ```
    #[must_use]
    pub const fn new(xterm256: u8, html_hex: &'static str) -> Self {
        Self { xterm256, html_hex }
    }

    /// Get the xterm256 color code for terminal output.
    ///
    /// # Examples
    ///
    /// ```
    /// use symbolic_mgu::Color;
    ///
    /// let blue = Color::new(33, "#0088ff");
    /// assert_eq!(blue.to_xterm256(), 33);
    /// ```
    #[must_use]
    pub const fn to_xterm256(self) -> u8 {
        self.xterm256
    }

    /// Get the HTML hex color for web output.
    ///
    /// # Examples
    ///
    /// ```
    /// use symbolic_mgu::Color;
    ///
    /// let blue = Color::new(33, "#0088ff");
    /// assert_eq!(blue.to_html(), "#0088ff");
    /// ```
    #[must_use]
    pub const fn to_html(self) -> &'static str {
        self.html_hex
    }

    /// Extract RGB components for 24-bit color output.
    ///
    /// Returns a tuple (r, g, b) where each component is in the range 0-255.
    /// This enables true color ANSI escape sequences: `\x1b[38;2;r;g;b m`
    ///
    /// # Examples
    ///
    /// ```
    /// use symbolic_mgu::Color;
    ///
    /// let blue = Color::BLUE;
    /// assert_eq!(blue.to_rgb(), (0, 135, 255)); // #0087ff
    ///
    /// let gray = Color::GRAY;
    /// assert_eq!(gray.to_rgb(), (128, 128, 128)); // #808080
    /// ```
    #[must_use]
    pub const fn to_rgb(self) -> (u8, u8, u8) {
        // Parse "#rrggbb" at compile time
        let bytes = self.html_hex.as_bytes();
        let r = hex_to_u8(bytes[1], bytes[2]);
        let g = hex_to_u8(bytes[3], bytes[4]);
        let b = hex_to_u8(bytes[5], bytes[6]);
        (r, g, b)
    }

    // The xterm-256 color cube (colors 16-231) uses the formula:
    // Index = 16 + 36×r + 6×g + b
    // Where r, g, b ∈ {0, 1, 2, 3, 4, 5} map to RGB values:
    // {0x00, 0x5f, 0x87, 0xaf, 0xd7, 0xff} = {0, 95, 135, 175, 215, 255}
    //
    // The xterm-256 gray-scale ramp (colors 232-255) uses the formula:
    // RGB = 8 + 10×(index - 232)
    // Where all three components have the same value (24 shades of gray).
    //
    // See also: https://www.ditig.com/256-colors-cheat-sheet

    /// Default blue color for Boolean types.
    pub const BLUE: Color = Color::new(33, "#0087ff");

    /// Default green color for Setvar types.
    pub const GREEN: Color = Color::new(34, "#00af00");

    /// Default red color for Class types.
    pub const RED: Color = Color::new(160, "#d70000");

    /// Default orange color for operators.
    pub const ORANGE: Color = Color::new(208, "#ff8700");

    /// Pure blue color (HTML standard).
    pub const HTML_BLUE: Color = Color::new(21, "#0000ff");

    /// Pure red color (HTML standard).
    pub const HTML_RED: Color = Color::new(196, "#ff0000");

    /// Purple color.
    pub const PURPLE: Color = Color::new(170, "#d75fd7");

    /// Medium gray color.
    pub const GRAY: Color = Color::new(244, "#808080");
}

/// Convert two hex digits to a u8 value.
///
/// # Arguments
///
/// * `high` - The high nibble hex digit (0-9, a-f, A-F)
/// * `low` - The low nibble hex digit (0-9, a-f, A-F)
const fn hex_to_u8(high: u8, low: u8) -> u8 {
    let h = hex_digit(high);
    let l = hex_digit(low);
    h * 16 + l
}

/// Convert a single hex digit character to its numeric value.
///
/// # Arguments
///
/// * `c` - A hex digit (0-9, a-f, A-F)
///
/// Returns 0 for invalid input (const fn cannot panic).
const fn hex_digit(c: u8) -> u8 {
    match c {
        b'0'..=b'9' => c - b'0',
        b'a'..=b'f' => c - b'a' + 10,
        b'A'..=b'F' => c - b'A' + 10,
        _ => 0, // Invalid input
    }
}
