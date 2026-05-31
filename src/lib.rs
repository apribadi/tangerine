#![no_std]
#![allow(unused_features)]
#![cfg_attr(miri, feature(uint_carryless_mul))]
#![doc = include_str!("../README.md")]

pub mod hash;
pub mod key;
pub mod map;
pub mod set;

mod cast;
mod util;
mod word;

extern crate alloc;
