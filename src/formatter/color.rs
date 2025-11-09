//! Simple color representation for terminal and HTML output.

/// Simple color representation supporting both terminal and HTML output.
///
/// Colors are specified using xterm256 color codes (0-255) and HTML hex colors.
/// This avoids complex color theory (RGB→XYZ→Lab conversions) while providing
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
    pub const fn to_html(self) -> &'static str {
        self.html_hex
    }

    /// Default blue color for Boolean types.
    pub const BLUE: Color = Color::new(33, "#0088ff");

    /// Default green color for Setvar types.
    pub const GREEN: Color = Color::new(34, "#00aa00");

    /// Default red color for Class types.
    pub const RED: Color = Color::new(160, "#cc0000");

    /// Default orange color for operators.
    pub const ORANGE: Color = Color::new(208, "#ff8700");
}
