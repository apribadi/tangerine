#![doc = include_str!("../README.md")]
#![cfg(any(target_pointer_width = "32", target_pointer_width = "64"))]

pub mod key;
pub mod map;
pub mod set;
