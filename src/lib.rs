#![cfg_attr(feature = "nightly", feature(extend_one))]
#![cfg_attr(feature = "nightly", feature(hint_prefetch))]
#![feature(likely_unlikely)]
#![doc = include_str!("../README.md")]

pub mod key;
pub mod map;
pub mod set;

pub mod new;
