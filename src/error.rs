/// Represents the possible errors that can occur within this lib.
///
/// This enum consolidates errors from various stages, including parsing dice notation,
/// validating roll configurations, and handling invalid numerical values.
#[derive(Debug, Clone, PartialEq, thiserror::Error)]
pub enum Error {
    /// Indicates an invalid dice roll configuration that cannot be processed.
    ///
    /// This typically occurs when the combination of dice count, sides, and mode
    /// results in a logically impossible or nonsensical roll (e.g., dropping all dice,
    /// keeping more dice than are rolled in a way that isn't equivalent to `Mode::None`).
    ///
    /// The contained `String` provides a more specific message about the nature
    /// of the invalid configuration.
    #[error("Invalid roll: {0}")]
    InvalidRoll(String),

    /// Indicates that a zero value was provided where it is not allowed.
    ///
    /// This error is typically encountered when:
    /// - The number of sides for a die (`size`) is 0.
    /// - The number of dice to roll (`count`) is 0.
    /// - A [`Mode`](crate::Mode) (like `Keep` or `Drop`) specifies 0 for the number of dice `n`
    ///   to keep or drop.
    #[error("Zero value not allowed")]
    ZeroValue,
}
