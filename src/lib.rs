#![plugin(phf_macros)]
#![feature(plugin)]
#![cfg_attr(test, feature(test))]
#![cfg_attr(test, feature(plugin))]
#![cfg_attr(test, plugin(quickcheck_macros))]
#![allow(dead_code)]

#[cfg(test)]
extern crate quickcheck;

#[cfg(test)]
extern crate test;

extern crate phf;

#[macro_use]
extern crate nom;

#[macro_use]
extern crate quick_error;

extern crate unreachable;

extern crate itertools;

pub mod tokens;

pub mod lexer;
pub mod lexer_deabbr;
pub mod show;

pub mod str_strategy;

pub mod expr;

//pub mod expr_allocator;

pub mod parser;

mod util;
