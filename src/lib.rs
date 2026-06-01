#![no_std]
#![allow(unused_features)]
#![cfg_attr(miri, feature(uint_carryless_mul))]
#![doc = include_str!("../README.md")]

pub mod key;
pub mod map;
pub mod set;

mod cast;
mod util;
mod word;
mod hash;

extern crate alloc;
