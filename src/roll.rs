use std::{fmt::Display, iter::FromIterator, ops::Deref};
use rand::Rng;
use crate::Error;


/// Specifies a modification rule to apply to a pool of dice rolls,
/// such as keeping or dropping a certain number of the highest or lowest dice.
///
/// This is used to implement common dice notation modifiers like "keep highest 1" (kh1),
/// "drop lowest 2" (dl2), etc.
#[derive(Debug, Clone, Default, PartialEq)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub enum Mode {
    /// Indicates that a certain number of dice should be kept, either the highest or the lowest.
    Keep {
        /// If `true`, the `n` highest dice are kept.
        /// If `false`, the `n` lowest dice are kept.
        highest: bool,
        /// The number of dice to keep.
        n: u16
    },

    /// Indicates that a certain number of dice should be dropped,
    /// either the highest or the lowest.
    Drop {
        /// If `true`, the `n` highest dice are dropped.
        /// If `false`, the `n` lowest dice are dropped.
        highest: bool,
        /// The number of dice to drop.
        n: u16,
    },

    /// Represents no modification, all dice rolled are considered.
    #[default]
    None
}

impl Mode {
    /// Creates a [`Mode::Keep`] mode to keep the `n` highest dice.
    pub fn kh(n: u16) -> Self {
        Mode::Keep { highest: true, n }
    }

    /// Creates a [`Mode::Keep`] mode to keep the `n` lowest dice.
    pub fn kl(n: u16) -> Self {
        Mode::Keep { highest: false, n }
    }

    /// Creates a [`Mode::Drop`] mode to keep the `n` highest dice.
    pub fn dh(n: u16) -> Self {
        Mode::Drop { highest: true, n }
    }

    /// Creates a [`Mode::Drop`] mode to keep the `n` lowest dice.
    pub fn dl(n: u16) -> Self {
        Mode::Drop { highest: false, n }
    }

    /// Validates that if the mode is [`Mode::Keep`] or [`Mode::Drop`], the associated `n` value is not zero.
    ///
    /// This method is useful for ensuring that a mode configuration is sensible before
    /// applying it to a dice roll, as keeping or dropping zero dice is usually not meaningful.
    ///
    /// # Errors
    /// Returns [`Err(crate::error::Error::ZeroValue)`] if the mode has an `n` and `n == 0`
    fn validate_non_zero(self) -> Result<Self, Error> {
        match self {
            Mode::Keep { n, .. } | Mode::Drop { n , .. } if n == 0 => Err(Error::ZeroValue),
            _ => Ok(self)
        }
    }

    /// If Mode has a `n` associated such as [`Mode::Keep`] or [`Mode::Drop`] returns `Some(&n)` else returns `None`.
    pub fn value(&self) -> Option<&u16> {
        match self {
            Mode::Keep { n, .. } | Mode::Drop { n , .. } => Some(n),
            Mode::None => None
        }
    }
}

impl Display for Mode {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let mode = match self {
            Mode::Keep { highest, n } => format!("k{}{}", if *highest { "h" } else { "l" }, n),
            Mode::Drop { highest, n } => format!("d{}{}", if *highest { "h" } else { "l" }, n),
            Mode::None => "".into()
        };

        write!(f, "{}", mode)
    }
}


/// Represents the outcome of a single die roll within a larger dice pool,
/// indicating whether the die's value was kept or dropped according to
/// modifiers keep/drop highest/lowest.
///
/// It's useful for displaying individual die results and understanding how
/// the final sum was calculated.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub enum RollValue {
    /// The die's value was kept and contributes to the final sum.
    Kept(u16),
    /// The die's value was dropped and does not contribute to the final sum.
    Dropped(u16)
}

impl RollValue {
    /// If the [`RollValue`] is [`RollValue::Kept`], this method returns `Some(u16)`.
    /// Otherwise (if it was [`RollValue::Dropped`]), it returns `None`.
    pub fn kept(self) -> Option<u16> {
        match self {
            RollValue::Kept(value) => Some(value),
            _ => None
        }
    }

    /// If the [`RollValue`] is [`RollValue::Dropped`], this method returns `Some(u16)`.
    /// Otherwise (if it was [`RollValue::Kept`]), it returns `None`.
    pub fn dropped(self) -> Option<u16> {
        match self {
            RollValue::Dropped(value) => Some(value),
            _ => None
        }
    }
}


/// Represents a dice roll configuration, including the number of dice,
/// the number of sides on each die, and any modifiers (like keep/drop).
///
/// This struct is typically created using [`Roll::builder()`] or the [`crate::roll!`] macro.
/// Once configured, you can use the [`Roll::roll()`] method to simulate the dice roll
/// and get a [`RollResult`].
#[derive(Debug, Clone, PartialEq)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct Roll {
    size: u16,
    count: u16,
    mode: Mode
}

impl Roll {
    /// Creates a new [`RollBuilder`] to construct a `Roll` instance.
    /// This is the primary way to start defining a dice roll configuration.
    ///
    /// # Arguments
    /// * `size`: The number of sides for each die in the roll (e.g., 6 for a d6, 20 for a d20).
    ///
    /// # Examples
    /// ```
    /// use math_rocks::{Roll, Mode};
    ///
    /// let roll = Roll::builder(20)    // Creates a builder for a d20
    ///              .count(3)          // We want to roll 3d20
    ///              .mode(Mode::kh(1)) // Keep the highest 1
    ///              .build()
    ///              .unwrap();
    ///
    /// assert_eq!(format!("{}", roll), "3d20kh1");
    /// ```
    pub fn builder(size: u16) -> RollBuilder {
        RollBuilder::new(size)
    }

    /// Simulates the dice roll according to the configuration.
    /// Generates random values for each die, then applies the specified [`Mode`]
    /// to determine which dice are kept or dropped.
    ///
    /// # Returns
    /// A [`RollResult`] containing the outcome of each individual die.
    ///
    /// # Examples
    /// ```
    /// use math_rocks::Roll;
    ///
    /// let roll = Roll::builder(6).count(3).build().unwrap(); // 3d6
    /// let result = roll.roll();
    ///
    /// // The result will contain 3 RollValue instances, all Kept by default.
    /// assert_eq!(result.len(), 3);
    /// println!("Rolled 3d6: {:?}", result);
    /// println!("Total: {}", result.total());
    /// ```
    pub fn roll(&self) -> RollResult {
        let values = self.generate_values();

        match self.mode {
            Mode::None => values.into_iter().map(RollValue::Kept).collect(),
            Mode::Keep { highest, n } => roll_result(highest, n, values),
            Mode::Drop { highest, n } => {
                let n = self.count - n;
                roll_result(!highest, n, values)
            }
        }
    }

    /// Calculates the minimum possible sum for this dice roll configuration.
    /// # Examples
    /// ```
    /// use math_rocks::{Roll, Mode};
    ///use math_rocks::$1;
    /// // 3d20 (no mode): minimun possible values are 1 + 1 + 1 = 3
    /// let roll = Roll::builder(20).count(3).build().unwrap();
    /// assert_eq!(roll.min(), 3);
    ///use math_rocks::$1;
    /// // 3d20kh1: only the highest rolled value will be kept, so the minimun possible value is 1
    /// let roll = Roll::builder(20).count(3).mode(Mode::kh(1)).build().unwrap();
    /// assert_eq!(roll.min(), 1);
    ///use math_rocks::$1;
    /// // 3d20dl1: the lowest rolled value will be dropped, so the minimun possible value is 1 + 1 = 2
    /// let roll = Roll::builder(20).count(3).mode(Mode::dl(1)).build().unwrap();
    /// assert_eq!(roll.min(), 2);
    /// ```
    pub const fn min(&self) -> u16 {
        match self.mode {
            Mode::None => self.count,
            Mode::Keep { n, .. } => n,
            Mode::Drop { n, .. } => self.count - n
        }
    }

    /// Calculates the maximum possible sum for this dice roll configuration.
    /// # Examples
    /// ```
    /// use math_rocks::{Roll, Mode};
    ///use math_rocks::$1;
    /// // 3d20 (no mode): maximum possible values are 20 + 20 + 20 = 60
    /// let roll = Roll::builder(20).count(3).build().unwrap();
    /// assert_eq!(roll.max(), 60);
    ///use math_rocks::$1;
    /// // 3d20kh1: only the highest rolled value will be kept, so the maximum possible value is 20
    /// let roll = Roll::builder(20).count(3).mode(Mode::kh(1)).build().unwrap();
    /// assert_eq!(roll.max(), 20);
    ///use math_rocks::$1;
    /// // 3d20dl1: the lowest rolled value will be dropped, so the maximum possible value is 20 + 20 = 40
    /// let roll = Roll::builder(20).count(3).mode(Mode::dl(1)).build().unwrap();
    /// assert_eq!(roll.max(), 40);
    /// ```
    pub const fn max(&self) -> u16 {
        match self.mode {
            Mode::None => self.size * self.count,
            Mode::Keep { n, .. } => self.size * n,
            Mode::Drop { n, .. } => self.size * (self.count - n)
        }
    }

    /// Calculates the average value that will be obtained in this roll.
    /// This provides a simple statistical average for the roll configuration.
    ///use math_rocks::$1;
    /// # Examples
    /// ```
    /// use math_rocks::Roll;
    ///
    /// // For 1d6, min = 1, max = 6, avg = (1 + 6) / 2 = 3.5
    /// let roll = Roll::builder(6).build().unwrap();
    /// assert_eq!(roll.avg(), 3.5);
    /// ```
    pub const fn avg(&self) -> f32 {
        (self.min() as f32 + self.max() as f32) / 2.0
    }

    /// Returns a tuple containing the minimum and maximum possible sums for the roll.
    /// Equivalent to `(self.min(), self.max())`.
    ///
    /// # Examples
    /// ```
    /// use math_rocks::Roll;
    ///
    /// let roll = Roll::builder(10).count(2).build().unwrap(); // 2d10
    /// assert_eq!(roll.possible_values(), (2, 20));
    /// ```
    pub const fn possible_values(&self) -> (u16, u16) {
        (self.min(), self.max())
    }

    /// Generates a vector of random die values based on `count` and `size`.
    /// This method is used internally by [`Roll::roll()`] before applying any [`Mode`].
    /// It uses `rand::thread_rng()` for randomness.
    ///
    /// # Returns
    /// A `Vec<u16>` where each element is a random integer between 1 and `self.size` (inclusive).
    /// The length of the vector is `self.count`.
    pub fn generate_values(&self) -> Vec<u16> {
        let mut rng = rand::rng();

        (0..self.count)
            .map(|_| rng.random_range(1..=self.size))
            .collect()
    }
}

impl Display for Roll {
    /// Formats the `Roll` configuration as a standard dice notation string.
    ///
    /// # Examples
    /// ```
    /// use math_rocks::{Roll, Mode};
    ///use math_rocks::$1;
    /// let roll = Roll::builder(20).build().unwrap();
    /// assert_eq!(format!("{roll}"), "1d20");
    ///use math_rocks::$1;
    /// let roll = Roll::builder(4).count(3).build().unwrap();
    /// assert_eq!(format!("{roll}"), "3d4");
    ///use math_rocks::$1;
    /// let roll = Roll::builder(6).count(2).mode(Mode::dl(1)).build().unwrap();
    /// assert_eq!(format!("{roll}"), "2d6dl1");
    /// ```
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}d{}{}", self.count, self.size, self.mode)
    }
}


/// A builder for creating [`Roll`] instances with a fluent API.
///
/// Start with [`Roll::builder()`] then chain methods
/// like [`RollBuilder::count()`] and [`RollBuilder::mode()`], and finally call
/// [`RollBuilder::build()`] to get a `Result<Roll, Error>`.
#[derive(Debug, Clone)]
pub struct RollBuilder {
    size: u16,
    count: u16,
    mode: Mode
}

impl RollBuilder {
    /// Creates a new `RollBuilder` with a given die size.
    /// The initial roll count defaults to 1 and the mode defaults to [`Mode::None`].
    ///
    /// # Arguments
    /// * `size`: The number of sides for each die.
    fn new(size: u16) -> Self {
        Self {
            size,
            count: 1,
            mode: Mode::None
        }
    }

    /// Sets the number of dice to roll.
    ///
    /// # Arguments
    /// * `count`: The number of dice.
    pub fn count(mut self, count: u16) -> Self {
        self.count = count;
        self
    }

    /// Sets the mode for the dice roll.
    ///
    /// # Arguments
    /// * `mode`: The [`Mode`] to apply (e.g., `Mode::kh(1)`).
    pub fn mode(mut self, mode: Mode) -> Self {
        self.mode = mode;
        self
    }

    /// Sets the mode for the dice roll to [`Mode::Keep`] highest n.
    ///
    /// # Arguments
    /// * `n`: number of dice to keep.
    pub fn kh(mut self, n: u16) -> Self {
        self.mode = Mode::Keep { highest: true, n };
        self
    }

    /// Sets the mode for the dice roll to [`Mode::Keep`] lowest n.
    ///
    /// # Arguments
    /// * `n`: number of dice to keep.
    pub fn kl(mut self, n: u16) -> Self {
        self.mode = Mode::Keep { highest: false, n };
        self
    }

    /// Sets the mode for the dice roll to [`Mode::Drop`] highest n.
    ///
    /// # Arguments
    /// * `n`: number of dice to drop.
    pub fn dh(mut self, n: u16) -> Self {
        self.mode = Mode::Drop { highest: true, n };
        self
    }

    /// Sets the mode for the dice roll to [`Mode::Drop`] lowest n.
    ///
    /// # Arguments
    /// * `n`: number of dice to drop.
    pub fn dl(mut self, n: u16) -> Self {
        self.mode = Mode::Drop { highest: false, n };
        self
    }

    /// Finalizes the configuration and attempts to build a [`Roll`] instance.
    ///
    /// # Errors
    /// - Returns `Err(Error::ZeroValue)` if `size` or `count` is 0.
    /// - Returns `Err(Error::ZeroValue)` if the `mode` involves keeping or dropping zero dice.
    /// - Returns `Err(Error::InvalidRoll)` if the `mode` attempts to keep or drop
    ///   a number of dice equal to or greater than the total `count` in a way
    ///   that is invalid (e.g., keeping all dice when `Mode::None` should be used,
    ///   or dropping all dice).
    ///
    /// # Examples
    /// ```
    /// use math_rocks::{Roll, Mode, Error};
    ///
    /// let roll_result = Roll::builder(6).count(3).build();
    /// assert!(roll_result.is_ok());
    ///
    /// let invalid_roll_result = Roll::builder(0).count(1).build();
    /// assert_eq!(invalid_roll_result, Err(Error::ZeroValue));
    ///
    /// let invalid_mode_result = Roll::builder(6).count(3).mode(Mode::Keep { highest: true, n: 3 }).build();
    /// assert!(matches!(invalid_mode_result, Err(Error::InvalidRoll(_))));
    /// ```
    pub fn build(self) -> Result<Roll, Error> {
        if self.size == 0 || self.count == 0 {
            return Err(Error::ZeroValue);
        }

        let mode = self.mode.validate_non_zero()?;

        match mode {
            Mode::Keep { n, .. } if n >= self.count => {
                Err(Error::InvalidRoll("Cannot keep all dice, use none instead".into()))
            },
            Mode::Drop { n, .. } if n >= self.count => {
                Err(Error::InvalidRoll("Cannot drop all dice".into()))
            },
            _ => Ok(Roll {
                size: self.size,
                count: self.count,
                mode
            })
        }
    }
}


/// Represents the result of a dice roll, containing a list of individual [`RollValue`]s.
///
/// This struct provides methods to inspect the outcome, such as calculating the
/// total sum of kept dice. It dereferences to `Vec<RollValue>` for direct slice/vector operations.
#[derive(Debug, Clone, PartialEq)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct RollResult(Vec<RollValue>);

impl RollResult {
    /// Creates a new `RollResult` from a vector of [`RollValue`]s.
    ///
    /// This is typically used internally when constructing results after a roll.
    pub fn new(rolls: Vec<RollValue>) -> Self {
        Self(rolls)
    }

    /// Calculates the sum of all dice values that were [`RollValue::Kept`].
    /// Dropped dice do not contribute to this total.
    ///
    /// # Examples
    /// ```
    /// use math_rocks::{RollResult, RollValue};
    ///
    /// let result = RollResult::new(vec![
    ///     RollValue::Kept(5),
    ///     RollValue::Dropped(1),
    ///     RollValue::Kept(3),
    /// ]);
    /// assert_eq!(result.total(), 8); // 5 + 3
    /// ```
    pub fn total(&self) -> u32 {
        self.iter()
            .flat_map(|roll| match roll {
                RollValue::Kept(v) => Some(*v as u32),
                RollValue::Dropped(_) => None
            })
            .sum()
    }
}

impl FromIterator<RollValue> for RollResult {
    fn from_iter<T: IntoIterator<Item = RollValue>>(iter: T) -> Self {
        Self(iter.into_iter().collect())
    }
}

impl Deref for RollResult {
    type Target = Vec<RollValue>;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}


fn roll_result(highest: bool, n: u16, values: Vec<u16>) -> RollResult {
    let mut indexed: Vec<(usize, &u16)> = values.iter()
        .enumerate()
        .collect();

    if highest {
        indexed.sort_unstable_by(|a, b| b.1.cmp(a.1));
    } else {
        indexed.sort_unstable_by(|a, b| a.1.cmp(b.1));
    }

    let keep_indexes: Vec<usize> = indexed.into_iter()
        .take(n as usize)
        .map(|(i, _)| i)
        .collect();

    values.into_iter()
        .enumerate()
        .map(|(i, value)| {
            if keep_indexes.contains(&i) {
                RollValue::Kept(value)
            } else {
                RollValue::Dropped(value)
            }
        })
        .collect()
}


/// A macro for conveniently creating [`Roll`] instances.
///
/// # Syntax
/// - `roll!(SIZE)`: Creates a roll for a single die of `SIZE` sides (e.g., `roll!(6)` for 1d6).
/// - `roll!(SIZE, COUNT)`: Creates a roll for `COUNT` dice of `SIZE` sides (e.g., `roll!(10, 3)` for 3d10).
/// - `roll!(SIZE, COUNT, MODE_FN)`: Creates a roll with a mode with n = 1.
///   `MODE_FN` must be one of `kh`, `kl`, `dh`, `dl`.
///   (e.g., `roll!(20, 4, kh)` for 4d20kh1).
/// - `roll!(SIZE, COUNT, MODE_FN, N)`: Creates a roll with a mode with custom n.
///   `MODE_FN` must be one of `kh`, `kl`, `dh`, `dl`.
///   (e.g., `roll!(20, 4, kh, 1)` for 4d20kh1).
///
/// # Returns
/// `Result<Roll, Error>` - The result of calling `RollBuilder::build()`.
///
/// # Examples
/// ```
/// use math_rocks::roll;
///
/// let r1d6 = roll!(6);
/// assert!(r1d6.is_ok());
/// assert_eq!(format!("{}", r1d6.unwrap()), "1d6");
///
/// let r3d10 = roll!(10, 3);
/// assert!(r3d10.is_ok());
/// assert_eq!(format!("{}", r3d10.unwrap()), "3d10");
///
/// let r4d20kh1 = roll!(20, 4, kh);
/// assert!(r4d20kh1.is_ok());
/// assert_eq!(format!("{}", r4d20kh1.unwrap()), "4d20kh1");
///
/// let r3d8dl2 = roll!(8, 3, dl, 2);
/// assert!(r3d8dl2.is_ok());
/// assert_eq!(format!("{}", r3d8dl2.unwrap()), "3d8dl2");
/// ```
#[macro_export]
macro_rules! roll {
    ($size:literal) => {
        $crate::Roll::builder($size)
            .build()
    };

    ($size:literal, $count:literal) => {
        $crate::Roll::builder($size)
            .count($count)
            .build()
    };

    ($size:literal, $count:literal, $mode:ident) => {
        $crate::Roll::builder($size)
            .count($count)
            .mode($crate::Mode::$mode(1))
            .build()
    };

    ($size:literal, $count:literal, $mode:ident, $n:literal) => {
        $crate::Roll::builder($size)
            .count($count)
            .mode($crate::Mode::$mode($n))
            .build()
    }
}


#[cfg(test)]
mod test {
    use proptest::prelude::*;
    use super::*;
    use crate::roll_test_strategies::roll_strategy;


    proptest! {
        #[test]
        fn test_mode_constructors(n in 1..100u16) {
            let kh = Mode::kh(n);
            assert!(matches!(kh, Mode::Keep { highest: true, n: _ }));

            let kl = Mode::kl(n);
            assert!(matches!(kl, Mode::Keep { highest: false, n: _ }));

            let dh = Mode::dh(n);
            assert!(matches!(dh, Mode::Drop { highest: true, n: _ }));

            let dl = Mode::dl(n);
            assert!(matches!(dl, Mode::Drop { highest: false, n: _ }));
        }

        #[test]
        fn test_mode_validation(n in 0..100u16, highest: bool) {
            let keep_mode = Mode::Keep { highest, n }.validate_non_zero();
            let drop_mode = Mode::Drop { highest, n }.validate_non_zero();

            if n == 0 {
                prop_assert!(keep_mode.is_err());
                prop_assert!(drop_mode.is_err());
            } else {
                prop_assert!(keep_mode.is_ok());
                prop_assert!(drop_mode.is_ok());
            }
        }

        #[test]
        fn test_mode_value(n in 0..100u16, highest: bool) {
            let keep_mode = Mode::Keep { highest, n };
            let drop_mode = Mode::Drop { highest, n };

            prop_assert_eq!(keep_mode.value().copied(), if n == 0 { Some(0) } else { Some(n) });
            prop_assert_eq!(drop_mode.value().copied(), if n == 0 { Some(0) } else { Some(n) });
            prop_assert_eq!(Mode::None.value(), None);
        }

        #[test]
        fn test_mode_display(n in 1..100u16, highest: bool) {
            let keep_mode = Mode::Keep { highest, n };
            let drop_mode = Mode::Drop { highest, n };

            let keep_str = format!("{}", keep_mode);
            let drop_str = format!("{}", drop_mode);
            let none_str = format!("{}", Mode::None);

            if highest {
                prop_assert_eq!(keep_str, format!("kh{n}"));
                prop_assert_eq!(drop_str, format!("dh{n}"));
            } else {
                prop_assert_eq!(keep_str, format!("kl{n}"));
                prop_assert_eq!(drop_str, format!("dl{n}"));
            }

            prop_assert_eq!(none_str, "");
        }

        #[test]
        fn test_roll_value_methods(value in 1..100u16) {
            let kept = RollValue::Kept(value);
            let dropped = RollValue::Dropped(value);

            prop_assert_eq!(kept.kept(), Some(value));
            prop_assert_eq!(dropped.kept(), None);

            prop_assert_eq!(kept.dropped(), None);
            prop_assert_eq!(dropped.dropped(), Some(value));
        }

        #[test]
        fn test_roll_methods(roll in roll_strategy()) {
            let size = roll.size;
            let count = roll.count;
            let result = roll.roll();

            prop_assert!(result.len() == count as usize);

            let min_val = roll.min();
            match roll.mode {
                Mode::None => prop_assert_eq!(min_val, count),
                Mode::Keep { n, .. } => prop_assert_eq!(min_val, n),
                Mode::Drop { n, .. } => prop_assert_eq!(min_val, count - n),
            }

            let max_val = roll.max();
            match roll.mode {
                Mode::None => prop_assert_eq!(max_val, size * count),
                Mode::Keep { n, .. } => prop_assert_eq!(max_val, size * n),
                Mode::Drop { n, .. } => prop_assert_eq!(max_val, size * (count - n)),
            }

            let avg = roll.avg();
            let (min_poss, max_poss) = roll.possible_values();
            prop_assert_eq!(avg, (min_val as f32 + max_val as f32) / 2.0);
            prop_assert_eq!((min_poss, max_poss), (min_val, max_val));

            let values = roll.generate_values();
            prop_assert_eq!(values.len(), count as usize);
            for &val in &values {
                prop_assert!(val >= 1 && val <= size);
            }
        }

        #[test]
        fn test_roll_display(roll in roll_strategy()) {
            let mode = match roll.mode {
                Mode::None => "".into(),
                Mode::Keep { highest, n } => if highest { format!("kh{n}") } else { format!("kl{n}") },
                Mode::Drop { highest, n } => if highest { format!("dh{n}") } else { format!("dl{n}") }
            };

            let expected_display = format!("{}d{}{}", roll.count, roll.size, mode);
            let actual_display = roll.to_string();

            prop_assert_eq!(expected_display, actual_display);
        }

        #[test]
        fn test_roll_builder_validation(
            size in 0..100u16,
            count in 0..100u16,
            mode_n in 0..50u16
        ) {
            let builder = Roll::builder(size).count(count);

            let modes = vec![
                Mode::None,
                Mode::kh(mode_n),
                Mode::kl(mode_n),
                Mode::dh(mode_n),
                Mode::dl(mode_n),
            ];

            for mode in modes {
                let result = builder.clone().mode(mode.clone()).build();

                if size == 0 || count == 0 {
                    prop_assert!(result.is_err());
                    continue;
                }

                if let Some(&n) = mode.value() {
                    if n == 0 {
                        prop_assert!(result.is_err());
                        continue;
                    }
                }

                match mode {
                    Mode::Keep { n, .. } if n >= count => {
                        prop_assert!(result.is_err());
                    },
                    Mode::Drop { n, .. } if n >= count => {
                        prop_assert!(result.is_err());
                    },
                    _ => {
                        prop_assert!(result.is_ok());
                    }
                }
            }
        }

        #[test]
        fn test_roll_result_total(values in prop::collection::vec(1..100u16, 1..20)) {
            let kept_only: Vec<RollValue> = values.iter()
                .map(|&v| RollValue::Kept(v))
                .collect();

            let result_kept = RollResult::new(kept_only);

            let dropped_only: Vec<RollValue> = values.iter()
                .map(|&v| RollValue::Dropped(v))
                .collect();

            let result_dropped = RollResult::new(dropped_only);

            let mixed: Vec<RollValue> = values.iter()
                .enumerate()
                .map(|(i, &v)| if i % 2 == 0 { RollValue::Kept(v) } else { RollValue::Dropped(v) })
                .collect();

            let result_mixed = RollResult::new(mixed);

            let expected_kept: u32 = values.iter().map(|&v| v as u32).sum();
            prop_assert_eq!(result_kept.total(), expected_kept);
            prop_assert_eq!(result_dropped.total(), 0);

            let expected_mixed: u32 = values.iter()
                .enumerate()
                .flat_map(|(i, &v)| if i % 2 == 0 { Some(v as u32) } else { None })
                .sum();

            prop_assert_eq!(result_mixed.total(), expected_mixed);
        }

        #[test]
        fn test_roll_result_function(
            values in prop::collection::vec(1..20u16, 2..10),
            n in 1..5u16,
            highest: bool
        ) {
            let n = std::cmp::min(n, values.len() as u16);

            let result = roll_result(highest, n, values.clone());

            prop_assert_eq!(result.len(), values.len());

            let kept_count = result.iter()
                .filter(|v| matches!(v, RollValue::Kept(_)))
                .count();

            prop_assert_eq!(kept_count, n as usize);

            let dropped_count = result.iter()
                .filter(|v| matches!(v, RollValue::Dropped(_)))
                .count();

            prop_assert_eq!(dropped_count, values.len() - n as usize);
        }

        #[test]
        fn test_roll_result_from_iterator(values in prop::collection::vec(1..100u16, 1..20)) {
            let roll_values: Vec<RollValue> = values.into_iter()
                .map(RollValue::Kept)
                .collect();

            let result: RollResult = roll_values.clone().into_iter().collect();
            prop_assert_eq!(result.len(), roll_values.len());
        }
    }
}
