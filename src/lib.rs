#![plugin(phf_macros)]
#![feature(plugin)]
#![cfg_attr(test, feature(test))]
#![cfg_attr(test, feature(inclusive_range_syntax))]
#![allow(dead_code)]

#[macro_use]
extern crate cfg_if;

cfg_if! {
    if #[cfg(test)] {
        extern crate test;

        #[macro_use] extern crate proptest;

        mod test_generators;
    }
}

extern crate phf;

#[macro_use]
extern crate nom;

#[macro_use]
extern crate quick_error;

extern crate unreachable;

extern crate itertools;

extern crate arraydeque;

pub mod tokens;

pub mod lexer;
pub mod lexer_deabbr;
pub mod lexer_abbr;

pub mod str_strategy;

pub mod expr;

pub mod parser;
mod unparser;

mod util;
