#![allow(dead_code)]
//#![allow(unused_imports)]

#![feature(inclusive_range_syntax)]
#![feature(test)]
#![feature(plugin)]

#![plugin(phf_macros)]
extern crate phf;

#[macro_use]
extern crate nom;

#[macro_use]
extern crate quick_error;

extern crate test;

mod tokens;

mod lexer;
mod lexer_deabbr;

pub mod str_strategy;

mod expr;