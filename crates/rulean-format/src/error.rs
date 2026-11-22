//! The errors of the parser (spec 07.1.2).
//!
//! An error is a reject or a decline. A reject means that the input is not a valid export. A decline means that rulean cannot check the input, for example because of an unknown format version or a resource limit (spec 02.3).

/// The kind of a parse error.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ErrorKind {
    /// An empty line.
    EmptyLine,
    /// The last line has no newline at the end.
    TruncatedLine,
    /// The line is not valid UTF-8.
    BadUtf8,
    /// The line is not one well-formed JSON object.
    BadJson,
    /// An object has the same key two times.
    DuplicateKey,
    /// A record has no value for a key that it must have.
    MissingKey,
    /// A value has the wrong JSON type for its key.
    WrongType,
    /// An integer has a sign, a fraction, an exponent or a leading zero.
    BadInteger,
    /// An integer is too large for its field.
    IntegerOverflow,
    /// A `\u` escape is a surrogate without its pair.
    LoneSurrogate,
    /// A string value is not one of the values that the key permits.
    BadEnumValue,
    /// The line is not a record kind of the format.
    UnknownRecord,
    /// The first line is not a `meta` record.
    NoMeta,
    /// A `meta` record after the first line.
    LateMeta,
    /// A record uses an index that no earlier record defines.
    UndefinedIndex,
    /// A record defines an index that is already defined.
    DuplicateIndex,
    /// A `natVal` is not a decimal string without leading zeros.
    BadNatLiteral,
    /// A `natVal` is above the literal bound of spec 05.8.
    NatTooLarge,
    /// The major format version is not 3, or the minor version is newer than rulean knows. This is a decline.
    UnknownVersion,
    /// An index is above the limit of the parser tables. This is a decline.
    IndexLimit,
    /// An array of the store is full. This is a decline.
    StoreFull,
    /// The layout of a binary file is wrong: a bad magic, a section out of the file, a missing section or a record that is cut (spec 07.2).
    BadBinary,
    /// A section of a binary file does not have the CRC-32C of its directory entry.
    BadChecksum,
}

impl ErrorKind {
    /// True if the error is a decline, false if it is a reject.
    pub fn is_decline(self) -> bool {
        matches!(
            self,
            ErrorKind::UnknownVersion | ErrorKind::IndexLimit | ErrorKind::StoreFull
        )
    }

    /// A short text for messages.
    ///
    /// Aeneas does not translate a `match` that gives string constants. The text is not part of the verified behavior, so the extract keeps this function opaque.
    #[cfg_attr(rulean_extract, charon::opaque)]
    pub fn text(self) -> &'static str {
        match self {
            ErrorKind::EmptyLine => "empty line",
            ErrorKind::TruncatedLine => "the last line has no newline",
            ErrorKind::BadUtf8 => "invalid UTF-8",
            ErrorKind::BadJson => "invalid JSON",
            ErrorKind::DuplicateKey => "duplicate key",
            ErrorKind::MissingKey => "missing key",
            ErrorKind::WrongType => "value of the wrong type",
            ErrorKind::BadInteger => "invalid integer",
            ErrorKind::IntegerOverflow => "integer too large",
            ErrorKind::LoneSurrogate => "unpaired surrogate escape",
            ErrorKind::BadEnumValue => "unknown value for the key",
            ErrorKind::UnknownRecord => "unknown record kind",
            ErrorKind::NoMeta => "the first line is not a meta record",
            ErrorKind::LateMeta => "a meta record after the first line",
            ErrorKind::UndefinedIndex => "use of an undefined index",
            ErrorKind::DuplicateIndex => "index defined two times",
            ErrorKind::BadNatLiteral => "invalid natVal",
            ErrorKind::NatTooLarge => "natVal above the literal bound",
            ErrorKind::UnknownVersion => "unknown format version",
            ErrorKind::IndexLimit => "index above the table limit",
            ErrorKind::StoreFull => "the term store is full",
            ErrorKind::BadBinary => "invalid binary file layout",
            ErrorKind::BadChecksum => "section checksum mismatch",
        }
    }
}

/// A parse error and the number of its line. The first line is line 1.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Error {
    pub line: u64,
    pub kind: ErrorKind,
}
