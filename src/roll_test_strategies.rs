use proptest::prelude::*;
use crate::roll::{Roll, Mode};


pub(crate) fn mode_strategy(max_n: u16) -> impl Strategy<Value = Mode> {
    if max_n <= 1 {
        return Just(Mode::None).boxed();
    }

    (1u16..max_n, 0u8..5).prop_map(|(n, mode_type)| {
        match mode_type {
            0 => Mode::None,
            1 => Mode::kh(n),
            2 => Mode::kl(n),
            3 => Mode::dh(n),
            _ => Mode::dl(n),
        }
    }).boxed()
}

pub(crate) fn roll_strategy() -> impl Strategy<Value = Roll> {
    (1..=100u16, 1..=100u16)
        .prop_flat_map(|(size, count)| {
            mode_strategy(count).prop_map(move |mode| {
                Roll::builder(size).count(count).mode(mode).build().unwrap()
            })
        })
}
