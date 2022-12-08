// Copyright (c) 2019 libeither developers
//
// Licensed under the Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0> or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your
// option. All files in the project carrying such notice may not be copied,
// modified, or distributed except according to those terms.

//! Error Handling

use std::fmt;

/// A result that must include an `Error`
pub type Result<T> = std::result::Result<T, Error>;

/// An error from the `libeither` library
#[derive(Debug)]
#[allow(dead_code)]
pub struct Error {
    /// the code
    code: ErrCode,
    /// the reason
    reason: String,
    /// the description
    description: String,
    /// the kind
    source: Option<ErrSource>,
}

impl Error {
    fn new<U>(code: ErrCode, reason: U, source: Option<ErrSource>) -> Self
    where
        U: Into<String>,
    {
        let reason = reason.into();
        let code_str: &str = code.into();
        let description = format!("{code_str}: {reason}");

        Self {
            code,
            reason,
            description,
            source,
        }
    }

    pub(crate) fn extract_left() -> Self {
        Self::new(ErrCode::Left, "Unable to extract Left value", None)
    }

    pub(crate) fn extract_right() -> Self {
        Self::new(ErrCode::Right, "Unable to extract Right value", None)
    }

    pub(crate) fn invalid() -> Self {
        Self::new(ErrCode::Invalid, "Invalid Either", None)
    }
}

impl std::error::Error for Error {
    #[must_use]
    fn description(&self) -> &str {
        &self.description
    }

    #[must_use]
    fn source(&self) -> Option<&(dyn std::error::Error + 'static)> {
        if let Some(ref x) = self.source {
            Some(x)
        } else {
            None
        }
    }
}

impl fmt::Display for Error {
    #[cfg(all(nightly_lints, feature = "unstable"))]
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        use std::error::Error;
        let res = <dyn Error>::sources(self).fold(format!("{self}"), |mut s, e| {
            s.push_str(&format!(" => {}", e));
            s
        });
        write!(f, "{}", res)
    }

    #[cfg(any(stable_lints, beta_lints))]
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.description)
    }

    #[cfg(all(nightly_lints, not(feature = "unstable")))]
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.description)
    }
}

impl From<&str> for Error {
    #[must_use]
    fn from(text: &str) -> Self {
        let split = text.split(':');
        let vec = split.collect::<Vec<&str>>();
        let code = vec.first().unwrap_or(&"");
        let reason = vec.get(1).unwrap_or(&"");
        Self::new((*code).into(), *reason, None)
    }
}

/// Error Codes
#[derive(Copy, Clone, Debug)]
enum ErrCode {
    /// An error working with the Left
    Left,
    /// An error working with the Right
    Right,
    /// An invalid either
    Invalid,
    /// An unknown error code
    Unknown,
}

impl From<ErrCode> for &str {
    fn from(value: ErrCode) -> &'static str {
        match value {
            ErrCode::Left => "left",
            ErrCode::Right => "right",
            ErrCode::Invalid => "invalid",
            ErrCode::Unknown => "unknown",
        }
    }
}

impl From<ErrCode> for String {
    fn from(value: ErrCode) -> String {
        match value {
            ErrCode::Left => "left",
            ErrCode::Right => "right",
            ErrCode::Invalid => "invalid",
            ErrCode::Unknown => "unknown",
        }
        .to_string()
    }
}

impl From<&str> for ErrCode {
    #[must_use]
    fn from(text: &str) -> Self {
        match text {
            "left" => Self::Left,
            "right" => Self::Right,
            "invalid" => Self::Invalid,
            _ => Self::Unknown,
        }
    }
}

macro_rules! dep_error {
    ($error:ty, $kind:expr, $code:expr, $reason:expr) => {
        impl From<$error> for Error {
            #[must_use]
            fn from(inner: $error) -> Self {
                Self::new($code, $reason, Some($kind(inner)))
            }
        }
    };
}

dep_error!(
    std::io::Error,
    ErrSource::Io,
    ErrCode::Unknown,
    "There was an I/O error"
);
#[cfg(all(test, feature = "serde"))]
dep_error!(
    serde_json::Error,
    ErrSource::SerdeJson,
    ErrCode::Unknown,
    "There was an error converting JSON"
);
#[cfg(all(test, feature = "serde"))]
dep_error!(
    toml::de::Error,
    ErrSource::TomlDe,
    ErrCode::Unknown,
    "There was an error deserializing TOML"
);
#[cfg(all(test, feature = "serde"))]
dep_error!(
    toml::ser::Error,
    ErrSource::TomlSer,
    ErrCode::Unknown,
    "There was an error serializing TOML"
);

/// Error Source
#[derive(Debug)]
#[allow(clippy::large_enum_variant, variant_size_differences)]
enum ErrSource {
    /// An I/O error
    Io(std::io::Error),
    /// An error with the serde_json library
    #[cfg(all(test, feature = "serde"))]
    SerdeJson(serde_json::Error),
    /// An error with the toml library
    #[cfg(all(test, feature = "serde"))]
    TomlDe(toml::de::Error),
    /// An error with the toml library
    #[cfg(all(test, feature = "serde"))]
    TomlSer(toml::ser::Error),
}

impl std::error::Error for ErrSource {}

impl fmt::Display for ErrSource {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Io(source) => write!(f, "{source}"),
            #[cfg(all(test, feature = "serde"))]
            Self::SerdeJson(source) => write!(f, "{source}"),
            #[cfg(all(test, feature = "serde"))]
            Self::TomlDe(source) => write!(f, "{source}"),
            #[cfg(all(test, feature = "serde"))]
            Self::TomlSer(source) => write!(f, "{source}"),
        }
    }
}
