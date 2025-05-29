use std::{fmt::Display, iter::FromIterator, ops::Deref};
use rand::Rng;
use crate::Error;


#[derive(Debug, Clone, Default, PartialEq)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub enum Mode {
    Keep { highest: bool, n: u16 },
    Drop { highest: bool, n: u16 },
    #[default]
    None
}

impl Mode {
    pub fn kh(n: u16) -> Self {
        Mode::Keep { highest: true, n }
    }

    pub fn kl(n: u16) -> Self {
        Mode::Keep { highest: false, n }
    }

    pub fn dh(n: u16) -> Self {
        Mode::Drop { highest: true, n }
    }

    pub fn dl(n: u16) -> Self {
        Mode::Drop { highest: false, n }
    }

    pub fn validate_non_zero(self) -> Result<Self, Error> {
        match self {
            Mode::Keep { n, .. } | Mode::Drop { n , .. } if n == 0 => Err(Error::ZeroValue),
            _ => Ok(self)
        }
    }

    pub fn value(&self) -> Option<u16> {
        match self {
            Mode::Keep { n, .. } | Mode::Drop { n , .. } => Some(*n),
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


#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub enum RollValue {
    Kept(u16),
    Dropped(u16)
}

impl RollValue {
    pub fn kept(self) -> Option<u16> {
        match self {
            RollValue::Kept(value) => Some(value),
            _ => None
        }
    }

    pub fn dropped(self) -> Option<u16> {
        match self {
            RollValue::Dropped(value) => Some(value),
            _ => None
        }
    }
}


#[derive(Debug, Clone, PartialEq)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct Roll {
    size: u16,
    count: u16,
    mode: Mode
}

impl Roll {
    pub fn builder(size: u16) -> RollBuilder {
        RollBuilder::new(size)
    }

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

    pub const fn min(&self) -> u16 {
        match self.mode {
            Mode::None => self.count,
            Mode::Keep { n, .. } => n,
            Mode::Drop { n, .. } => self.count - n
        }
    }

    pub const fn max(&self) -> u16 {
        match self.mode {
            Mode::None => self.size * self.count,
            Mode::Keep { n, .. } => self.size * n,
            Mode::Drop { n, .. } => self.size * (self.count - n)
        }
    }

    pub const fn avg(&self) -> f32 {
        (self.min() as f32 + self.max() as f32) / 2.0
    }

    pub const fn possible_values(&self) -> (u16, u16) {
        (self.min(), self.max())
    }

    pub fn generate_values(&self) -> Vec<u16> {
        let mut rng = rand::rng();

        (0..self.count)
            .map(|_| rng.random_range(1..=self.size))
            .collect()
    }
}

impl Display for Roll {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}d{}{}", self.count, self.size, self.mode)
    }
}


#[derive(Debug, Clone)]
pub struct RollBuilder {
    size: u16,
    count: u16,
    mode: Mode
}

impl RollBuilder {
    fn new(size: u16) -> Self {
        Self {
            size,
            count: 1,
            mode: Mode::None
        }
    }

    pub fn count(mut self, count: u16) -> Self {
        self.count = count;
        self
    }

    pub fn mode(mut self, mode: Mode) -> Self {
        self.mode = mode;
        self
    }

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


#[derive(Debug, Clone, PartialEq)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct RollResult(Vec<RollValue>);

impl RollResult {
    pub fn new(rolls: Vec<RollValue>) -> Self {
        Self(rolls)
    }

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

            prop_assert_eq!(keep_mode.value(), if n == 0 { Some(0) } else { Some(n) });
            prop_assert_eq!(drop_mode.value(), if n == 0 { Some(0) } else { Some(n) });
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

                if let Some(n) = mode.value() {
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
