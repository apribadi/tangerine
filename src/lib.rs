#![no_std]
#![doc = include_str!("../README.md")]

pub mod key;
pub mod map;
pub mod set;

mod invert_mul;
mod word;
mod hash;

extern crate alloc;
