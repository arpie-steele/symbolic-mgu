//! Comment metadata extraction for Metamath databases.
//!
//! Parses contributor attributions and preserves raw text for later parsing
//! of typesetting directives ($t) and project hints ($j).
//!
//! # Contribution Patterns
//!
//! Metamath comments contain structured metadata about contributions:
//! - `(Contributed by NAME, DD-MMM-YYYY.)`
//! - `(Revised by NAME, DD-MMM-YYYY.)`
//! - `(Proof shortened by NAME, DD-MMM-YYYY.)`
//!
//! # Example
//!
//! ```
//! use symbolic_mgu::metamath::CommentMetadata;
//!
//! let comment = "Theorem about implication. (Contributed by NM, 5-Aug-1993.)";
//! let metadata = CommentMetadata::parse(comment);
//!
//! assert_eq!(metadata.contributions.len(), 1);
//! assert_eq!(metadata.contributions[0].contributor, "NM");
//! ```

use std::fmt;
use thiserror::Error;

/// Errors that can occur during comment parsing.
#[derive(Debug, Error, Clone, PartialEq, Eq)]
pub enum CommentError {
    /// Invalid month name in date.
    #[error("Invalid month name: {month}")]
    InvalidMonth {
        /// The invalid month string.
        month: String,
    },

    /// Malformed date string.
    #[error("Malformed date: {date}")]
    MalformedDate {
        /// The malformed date string.
        date: String,
    },

    /// Invalid day (must be 1-31).
    #[error("Invalid day: {day}")]
    InvalidDay {
        /// The invalid day value.
        day: u8,
    },
}

/// A month in the Gregorian calendar.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[repr(u8)]
pub enum Month {
    /// January
    Jan = 1,
    /// February
    Feb = 2,
    /// March
    Mar = 3,
    /// April
    Apr = 4,
    /// May
    May = 5,
    /// June
    Jun = 6,
    /// July
    Jul = 7,
    /// August
    Aug = 8,
    /// September
    Sep = 9,
    /// October
    Oct = 10,
    /// November
    Nov = 11,
    /// December
    Dec = 12,
}

impl Month {
    /// Convert month to numeric representation (1-12).
    pub fn as_number(self) -> u8 {
        self as u8
    }

    /// Parse month from 3-letter abbreviation.
    pub fn from_abbreviation(s: &str) -> Option<Self> {
        match s {
            "Jan" => Some(Month::Jan),
            "Feb" => Some(Month::Feb),
            "Mar" => Some(Month::Mar),
            "Apr" => Some(Month::Apr),
            "May" => Some(Month::May),
            "Jun" => Some(Month::Jun),
            "Jul" => Some(Month::Jul),
            "Aug" => Some(Month::Aug),
            "Sep" => Some(Month::Sep),
            "Oct" => Some(Month::Oct),
            "Nov" => Some(Month::Nov),
            "Dec" => Some(Month::Dec),
            _ => None,
        }
    }
}

impl fmt::Display for Month {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let s = match self {
            Month::Jan => "Jan",
            Month::Feb => "Feb",
            Month::Mar => "Mar",
            Month::Apr => "Apr",
            Month::May => "May",
            Month::Jun => "Jun",
            Month::Jul => "Jul",
            Month::Aug => "Aug",
            Month::Sep => "Sep",
            Month::Oct => "Oct",
            Month::Nov => "Nov",
            Month::Dec => "Dec",
        };
        write!(f, "{}", s)
    }
}

/// A date in DD-MMM-YYYY format (as used in Metamath comments).
///
/// This is a simple value type optimized for size (4 bytes) and copy semantics.
/// No validation is performed beyond checking month names during parsing.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct ContributionDate {
    /// Day of month (1-31)
    pub day: u8,
    /// Month
    pub month: Month,
    /// Year
    pub year: u16,
}

impl ContributionDate {
    /// Parse a date from DD-MMM-YYYY format.
    ///
    /// # Errors
    ///
    /// Returns an error if the date is malformed, the month name is invalid,
    /// or the day is out of range (0 or >31).
    ///
    /// # Example
    ///
    /// ```
    /// # use symbolic_mgu::metamath::ContributionDate;
    /// let date = ContributionDate::parse("5-Aug-1993").unwrap();
    /// assert_eq!(date.day, 5);
    /// assert_eq!(date.month.as_number(), 8);
    /// assert_eq!(date.year, 1993);
    /// ```
    pub fn parse(s: &str) -> Result<Self, CommentError> {
        let parts: Vec<&str> = s.split('-').collect();
        if parts.len() != 3 {
            return Err(CommentError::MalformedDate {
                date: s.to_string(),
            });
        }

        let day: u8 = parts[0].parse().map_err(|_| CommentError::MalformedDate {
            date: s.to_string(),
        })?;

        if day == 0 || day > 31 {
            return Err(CommentError::InvalidDay { day });
        }

        let month =
            Month::from_abbreviation(parts[1]).ok_or_else(|| CommentError::InvalidMonth {
                month: parts[1].to_string(),
            })?;

        let year: u16 = parts[2].parse().map_err(|_| CommentError::MalformedDate {
            date: s.to_string(),
        })?;

        Ok(ContributionDate { day, month, year })
    }
}

impl fmt::Display for ContributionDate {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}-{}-{}", self.day, self.month, self.year)
    }
}

/// The type of contribution made to a theorem or axiom.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum ContributionKind {
    /// Initial contribution.
    Contributed,
    /// Revision of statement or proof.
    Revised,
    /// Proof shortened (optimization).
    ProofShortened,
}

impl fmt::Display for ContributionKind {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let s = match self {
            ContributionKind::Contributed => "Contributed",
            ContributionKind::Revised => "Revised",
            ContributionKind::ProofShortened => "Proof shortened",
        };
        write!(f, "{}", s)
    }
}

/// A contribution to a theorem or axiom.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Contribution {
    /// Name or initials of the contributor
    pub contributor: String,
    /// Date of the contribution
    pub date: ContributionDate,
    /// Type of contribution (contributed, revised, proof shortened)
    pub kind: ContributionKind,
}

impl fmt::Display for Contribution {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{} by {}, {}", self.kind, self.contributor, self.date)
    }
}

/// Metadata extracted from a Metamath comment.
///
/// Preserves both structured contribution data and the raw text for later
/// parsing of typesetting directives ($t) and project hints ($j).
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CommentMetadata {
    /// Parsed contribution attributions.
    pub contributions: Vec<Contribution>,
    /// Raw comment text (for deferred $t/$j parsing).
    pub raw_text: String,
}

impl CommentMetadata {
    /// Parse comment metadata from a comment string.
    ///
    /// Extracts contribution patterns while preserving the full text.
    ///
    /// # Example
    ///
    /// ```
    /// use symbolic_mgu::metamath::CommentMetadata;
    ///
    /// let comment = "Double modus ponens. (Contributed by NM, 5-Aug-1993.) \
    ///                (Proof shortened by Wolf Lammen, 23-Jul-2013.)";
    /// let metadata = CommentMetadata::parse(comment);
    ///
    /// assert_eq!(metadata.contributions.len(), 2);
    /// assert_eq!(metadata.contributions[0].contributor, "NM");
    /// assert_eq!(metadata.contributions[1].contributor, "Wolf Lammen");
    /// ```
    pub fn parse(text: &str) -> Self {
        let mut contributions = Vec::new();

        // Parse contribution patterns
        // Pattern: (KIND by NAME, DATE.)
        // where KIND is "Contributed" | "Revised" | "Proof shortened"

        // Find all contribution patterns in the text
        let mut pos = 0;
        while let Some(start) = text[pos..].find('(') {
            let abs_start = pos + start;
            if let Some(end) = text[abs_start..].find(')') {
                let abs_end = abs_start + end;
                let content = &text[abs_start + 1..abs_end];

                // Try to parse this as a contribution
                if let Some(contribution) = Self::parse_contribution(content) {
                    contributions.push(contribution);
                }

                pos = abs_end + 1;
            } else {
                break;
            }
        }

        CommentMetadata {
            contributions,
            raw_text: text.to_string(),
        }
    }

    /// Try to parse a contribution from text between parentheses.
    fn parse_contribution(text: &str) -> Option<Contribution> {
        let text = text.trim();

        // Determine the kind
        let (kind, remainder) = if let Some(rest) = text.strip_prefix("Contributed by ") {
            (ContributionKind::Contributed, rest)
        } else if let Some(rest) = text.strip_prefix("Revised by ") {
            (ContributionKind::Revised, rest)
        } else if let Some(rest) = text.strip_prefix("Proof shortened by ") {
            (ContributionKind::ProofShortened, rest)
        } else {
            return None;
        };

        // Find the comma that separates name from date
        let comma_pos = remainder.rfind(',')?;
        let contributor = remainder[..comma_pos].trim().to_string();

        // Extract date (after comma, before period)
        let date_part = remainder[comma_pos + 1..].trim();
        let date_str = date_part.strip_suffix('.')?;
        let date = ContributionDate::parse(date_str.trim()).ok()?;

        Some(Contribution {
            contributor,
            date,
            kind,
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn month_from_str() {
        assert_eq!(Month::from_abbreviation("Jan"), Some(Month::Jan));
        assert_eq!(Month::from_abbreviation("Dec"), Some(Month::Dec));
        assert_eq!(Month::from_abbreviation("Invalid"), None);
    }

    #[test]
    fn month_as_number() {
        assert_eq!(Month::Jan.as_number(), 1);
        assert_eq!(Month::Dec.as_number(), 12);
        assert_eq!(Month::Aug.as_number(), 8);
    }

    #[test]
    fn month_display() {
        assert_eq!(format!("{}", Month::Jan), "Jan");
        assert_eq!(format!("{}", Month::Dec), "Dec");
    }

    #[test]
    fn parse_date() -> Result<(), CommentError> {
        let date = ContributionDate::parse("5-Aug-1993")?;
        assert_eq!(date.day, 5);
        assert_eq!(date.month, Month::Aug);
        assert_eq!(date.year, 1993);
        Ok(())
    }

    #[test]
    fn parse_date_display() -> Result<(), CommentError> {
        let date = ContributionDate::parse("31-Dec-2015")?;
        assert_eq!(format!("{}", date), "31-Dec-2015");
        Ok(())
    }

    #[test]
    fn parse_invalid_date() {
        assert!(ContributionDate::parse("32-Jan-2000").is_err());
        assert!(ContributionDate::parse("0-Jan-2000").is_err());
        assert!(ContributionDate::parse("5-Xxx-2000").is_err());
        assert!(ContributionDate::parse("5/Aug/1993").is_err());
    }

    #[test]
    fn parse_single_contribution() {
        let comment = "Theorem about implication. (Contributed by NM, 5-Aug-1993.)";
        let metadata = CommentMetadata::parse(comment);

        assert_eq!(metadata.contributions.len(), 1);
        assert_eq!(metadata.contributions[0].contributor, "NM");
        assert_eq!(metadata.contributions[0].date.year, 1993);
        assert_eq!(
            metadata.contributions[0].kind,
            ContributionKind::Contributed
        );
    }

    #[test]
    fn parse_multiple_contributions() {
        let comment = "Double modus ponens. (Contributed by NM, 5-Aug-1993.) \
                       (Proof shortened by Wolf Lammen, 23-Jul-2013.)";
        let metadata = CommentMetadata::parse(comment);

        assert_eq!(metadata.contributions.len(), 2);
        assert_eq!(metadata.contributions[0].contributor, "NM");
        assert_eq!(
            metadata.contributions[0].kind,
            ContributionKind::Contributed
        );
        assert_eq!(metadata.contributions[1].contributor, "Wolf Lammen");
        assert_eq!(
            metadata.contributions[1].kind,
            ContributionKind::ProofShortened
        );
    }

    #[test]
    fn parse_revised_contribution() {
        let comment = "(Contributed by NM, 5-Aug-1993.) (Revised by NM, 13-Jul-2013.)";
        let metadata = CommentMetadata::parse(comment);

        assert_eq!(metadata.contributions.len(), 2);
        assert_eq!(metadata.contributions[1].kind, ContributionKind::Revised);
    }

    #[test]
    fn parse_contributor_with_apostrophe() {
        let comment = "(Proof shortened by O'Cat, 20-Oct-2011.)";
        let metadata = CommentMetadata::parse(comment);

        assert_eq!(metadata.contributions.len(), 1);
        assert_eq!(metadata.contributions[0].contributor, "O'Cat");
    }

    #[test]
    fn parse_contributor_with_question_mark() {
        let comment = "(Contributed by NM?, 7-Feb-2006.)";
        let metadata = CommentMetadata::parse(comment);

        assert_eq!(metadata.contributions.len(), 1);
        assert_eq!(metadata.contributions[0].contributor, "NM?");
    }

    #[test]
    fn raw_text_preserved() {
        let comment = "Some theorem. (Contributed by NM, 5-Aug-1993.)";
        let metadata = CommentMetadata::parse(comment);

        assert_eq!(metadata.raw_text, comment);
    }

    #[test]
    fn contribution_date_size() {
        // Verify `ContributionDate` is 4 bytes (optimization goal)
        assert_eq!(std::mem::size_of::<ContributionDate>(), 4);
    }
}
