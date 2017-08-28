#![allow(dead_code)]
#![allow(unused_imports)]
#![allow(unused_macros)]
#![allow(unknown_lints)]
#![feature(test)]
#![feature(plugin)]
#![plugin(phf_macros)]
extern crate phf;

#[macro_use]
extern crate nom;

#[macro_use]
extern crate quick_error;

extern crate test;

extern crate unreachable;

pub mod tokens;

pub mod lexer;
pub mod lexer_deabbr;

pub mod str_strategy;

pub mod expr;

pub mod parser;

mod util;
