#![cfg_attr(feature = "nightly", feature(hint_prefetch))]
#![cfg_attr(feature = "nightly", feature(impl_trait_in_assoc_type))]
#![doc = include_str!("../README.md")]

pub mod key;
pub mod map;
pub mod set;
pub mod two;
pub mod old_map;
pub mod old_key;
