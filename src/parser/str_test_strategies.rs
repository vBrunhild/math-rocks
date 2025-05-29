use proptest::prelude::*;


pub(crate) fn simple_number_strategy() -> impl Strategy<Value = String> {
    (1u16..=1000).prop_map(|n| n.to_string())
}

pub(crate) fn simple_dice_strategy() -> impl Strategy<Value = String> {
    (1u16..=1000, 1u16..=1000)
        .prop_map(|(count, size)| {
            let size = if size == 1 { 2 } else { size };
            format!("{}d{}", count, size)
        })
}

pub(crate) fn dice_with_modifier_strategy() -> impl Strategy<Value = String> {
    (
        2u16..=1000,
        1u16..=1000,
        prop_oneof!["kh", "kl", "dh", "dl"],
        prop::option::of(1u16..=1000)
    ).prop_map(|(count, size, modifier, mod_value)| {
        match mod_value {
            None => format!("{}d{}{}", count, size, modifier),
            Some(val) => {
                let val = std::cmp::min(count, val) - 1;

                if val == 0 {
                    format!("{}d{}{}", count, size, modifier)
                } else {
                    format!("{}d{}{}{}", count, size, modifier, val)
                }
            }
        }
    })
}

pub(crate) fn parenthesized_strategy(inner: impl Strategy<Value = String>) -> impl Strategy<Value = String> {
    inner.prop_map(|expr| format!("({})", expr))
}

pub(crate) fn binary_operation_strategy(
    left: impl Strategy<Value = String>,
    right: impl Strategy<Value = String>
) -> impl Strategy<Value = String> {
    (
        left,
        prop_oneof![Just("+"), Just("-"), Just("*"), Just("/")],
        right
    ).prop_map(|(l, op, r)| format!("{} {} {}", l, op, r))
}

pub(crate) fn dice_expression_strategy() -> impl Strategy<Value = String> {
    let leaf = prop_oneof![
        simple_number_strategy(),
        simple_dice_strategy(),
        dice_with_modifier_strategy(),
    ];

    leaf.prop_recursive(4, 32, 10, |inner| {
        prop_oneof![
            parenthesized_strategy(inner.clone()),
            binary_operation_strategy(inner.clone(), inner),
        ]
    })
}
