#![plugin(phf_macros)]
#![feature(plugin)]
#![cfg_attr(test, feature(test))]
#![cfg_attr(test, feature(inclusive_range_syntax))]
#![allow(dead_code)]

//============================================================================//
// Crates:
//============================================================================//

#[macro_use]
extern crate nom;

#[macro_use]
extern crate quick_error;

extern crate itertools;
extern crate unreachable;

extern crate arraydeque;
extern crate arrayvec;

extern crate phf;

//============================================================================//
// Testing crates:
//============================================================================//

#[macro_use]
extern crate cfg_if;

cfg_if! {
    if #[cfg(test)] {
        extern crate test;

        #[macro_use] extern crate proptest;

        mod test_generators;
    }
}

//============================================================================//
// Modules:
//============================================================================//

mod util;

pub mod str_strategy;

pub mod tokens;
pub mod lexer;
pub mod lexer_deabbr;
pub mod lexer_abbr;

pub mod expr;
pub mod parser;
mod unparser;
