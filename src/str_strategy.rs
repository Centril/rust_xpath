//! Provides a [generic way] of reasoning about strategies for injection of the
//! contents of things that [can be represented] as a [string slice] in a
//! specific way. The strategies are:
//!
//! + cache it in a set, [`HashSetStrategy`]
//! + box it in the heap, [`BoxStrategy`]
//! + box it in the heap as a String, [`StringStrategy`]
//! + just return the slice, [`RefStrategy`]
//!
//! [generic way]: trait.StrStrategy.html
//! [can be represented]: https://doc.rust-lang.org/std/convert/trait.AsRef.html
//! [string slice]: https://doc.rust-lang.org/std/primitive.str.html
//! [`HashSetStrategy`]: struct.HashSetStrategy.html
//! [`BoxStrategy`]: struct.BoxStrategy.html`
//! [`StringStrategy`]: struct.StringStrategy.html
//! [`RefStrategy`]: struct.RefStrategy.html

use std::marker::PhantomData;
use std::fmt;
use std::collections::HashSet;
use std::cell::UnsafeCell;

type BS = Box<str>;

/// Takes something representable as a string slice and creates an owned
/// `Box<str>` out of it.
fn bs_new<S: AsRef<str>>(s: S) -> BS {
    s.as_ref().to_owned().into_boxed_str()
}

//============================================================================//
// StrStrategy (trait)
//============================================================================//

/// Provides a specific way to inject things [representable] as a [string slice]
/// as another form [representable] as a [string slice]. This provides
/// opportunities for caching, etc., when [interior mutability] is used.
///
/// [representable]: https://doc.rust-lang.org/std/convert/trait.AsRef.html
/// [string slice]: https://doc.rust-lang.org/std/primitive.str.html
/// [interior mutability]: https://doc.rust-lang.org/std/cell
pub trait StrStrategy<'a> {
    /// The type of inputs, representable as a string slice,
    /// that the strategy accepts.
    type Input: AsRef<str>;

    /// The type of outputs, representable as a string slice,
    /// that the strategy yields when used.
    type Output: AsRef<str>;

    /// Injects the contents from an input of type [`Input`] to one of
    /// type [`Output`], with potential side effects.
    ///
    /// Subsequent applications should not panic.
    ///
    /// [`Input`]: trait.StrStrategy.html#associatedtype.Input
    /// [`Output`]: trait.StrStrategy.html#associatedtype.Output
    fn inject_str(&'a self, input: Self::Input) -> Self::Output;
}

//============================================================================//
// HashSetStrategy
//============================================================================//

/// A caching [`StrStrategy`] using the heap.
/// Identical strings are only allocated once.
///
/// The strategy is internally backed by a [`HashSet`]
/// which is never removed from.
///
/// [`StrStrategy`]: trait.StrStrategy.html
/// [`HashSet`]: https://doc.rust-lang.org/std/collections/struct.HashSet.html
pub struct HashSetStrategy<I> {
    store: UnsafeCell<HashSet<BS>>,
    ph: PhantomData<I>,
}

impl<I: AsRef<str>> HashSetStrategy<I> {
    #[allow(unknown_lints)]
    #[allow(mut_from_ref)]
    unsafe fn store_mut(&self) -> &mut HashSet<BS> {
        self.store.get().as_mut().unwrap()
    }

    fn store(&self) -> &HashSet<BS> {
        unsafe { self.store.get().as_ref().unwrap() }
    }

    /// The value of is_empty() on the owned hash set.
    pub fn is_empty(&self) -> bool {
        self.store().is_empty()
    }

    /// The value of len() of the owned hash set.
    pub fn len(&self) -> usize {
        self.store().len()
    }

    /// Has the given input been hashed already?
    pub fn contains(&self, value: I) -> bool {
        self.store().contains(value.as_ref())
    }
}

impl<I> Default for HashSetStrategy<I> {
    fn default() -> Self {
        HashSetStrategy {
            store: UnsafeCell::new(HashSet::new()),
            ph: PhantomData,
        }
    }
}

impl<I: AsRef<str>> fmt::Debug for HashSetStrategy<I> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{:?}", self.store())
    }
}

impl<'a, I: AsRef<str>> StrStrategy<'a> for HashSetStrategy<I> {
    type Input = I;
    type Output = &'a str;

    /// Allocates the given input in the cache and yields a reference to it.
    fn inject_str(&'a self, input: Self::Input) -> Self::Output {
        let i = input.as_ref();

        /*
         * This is safe because nothing is ever removed from the HashSet,
         * and when it grows (length == capacity), Box<str> may be moved,
         * but the heap allocated contents are never deallocated,
         * thus the &'a str returned always points to a valid memory location.
         * Therefore, this will never cause memory unsafety.
         */
        let si = unsafe { self.store_mut() };

        // TODO: Replace with entry API if and when HashSet:s get them.
        if !si.contains(i) {
            si.insert(bs_new(i));
        }

        si.get(i).unwrap()
    }
}

//============================================================================//
// BoxStrategy
//============================================================================//

/// A [`StrStrategy`] that simply allocates using the heap.
///
/// [`StrStrategy`]: trait.StrStrategy.html
pub struct BoxStrategy<I>(PhantomData<I>);

impl<I> Default for BoxStrategy<I> {
    fn default() -> Self {
        BoxStrategy(PhantomData)
    }
}

impl<I> fmt::Debug for BoxStrategy<I> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "BoxStrategy")
    }
}

impl<'a, I: AsRef<str>> StrStrategy<'a> for BoxStrategy<I> {
    type Output = Box<str>;
    type Input = I;

    /// Allocates the input on the heap and just returns that box.
    fn inject_str(&'a self, input: Self::Input) -> Self::Output {
        bs_new(input)
    }
}

//============================================================================//
// StringStrategy
//============================================================================//

/// A [`StrStrategy`] that simply allocates using [`String`].
///
/// Use this if you want mutability, otherwise, use [`BoxStrategy`].
///
/// [`StrStrategy`]: trait.StrStrategy.html
/// [`BoxStrategy`]: struct.BoxStrategy.html
/// [`String`]: https://doc.rust-lang.org/nightly/collections/string/struct.String.html
pub struct StringStrategy<I>(PhantomData<I>);

impl<I> Default for StringStrategy<I> {
    fn default() -> Self {
        StringStrategy(PhantomData)
    }
}

impl<I> fmt::Debug for StringStrategy<I> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "StringStrategy")
    }
}

impl<'a, I: AsRef<str>> StrStrategy<'a> for StringStrategy<I> {
    type Output = String;
    type Input = I;

    /// Allocates the input on the heap as a [`String`] and just returns it.
    /// [`String`]: https://doc.rust-lang.org/nightly/collections/string/struct.String.html
    fn inject_str(&'a self, input: Self::Input) -> Self::Output {
        input.as_ref().to_owned()
    }
}

//============================================================================//
// RefStrategy
//============================================================================//

/// A [`StrStrategy`] that is the indentity function on inputs
/// In other words: given a reference to a string slice, it gives it back.
///
/// The strategy must live as long as the most long lived input does.
///
/// [`StrStrategy`]: trait.StrStrategy.html
pub struct RefStrategy;

impl Default for RefStrategy {
    fn default() -> Self {
        RefStrategy
    }
}

impl fmt::Debug for RefStrategy {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "RefStrategy")
    }
}

impl<'a> StrStrategy<'a> for RefStrategy {
    type Output = &'a str;
    type Input = &'a str;

    /// Returns the given input back.
    fn inject_str(&'a self, input: Self::Input) -> Self::Output {
        input.as_ref()
    }
}

//============================================================================//
// Tests
//============================================================================//

#[test]
fn str_strategy_hashset() {
    let ss = (HashSetStrategy::default(), 0);
    let (i1, i2, i3) = {
        let s1 = "hello";
        let s2 = "world";
        let i1 = ss.0.inject_str(s1);
        // Force reallocation. We do this to ensure that addresses are stable.
        unsafe {
            ss.0.store_mut().reserve(1);
        }
        let i2 = ss.0.inject_str(s2);
        let i3 = ss.0.inject_str(s2);
        (i1, i2, i3)
    };
    assert_eq!("hello", i1);
    assert_eq!("world", i2);
    assert_eq!("world", i3);
    assert_eq!(i2.as_ptr(), i3.as_ptr());
    assert!(ss.0.contains("hello"));
    assert!(ss.0.contains("world"));
    assert!(ss.0.len() == 2);
}

#[test]
fn str_strategy_box() {
    let ss = (BoxStrategy::default(), 0);
    let (i1, i2, i3) = {
        let s1 = "hello";
        let s2 = "world";
        let i1 = ss.0.inject_str(s1);
        let i2 = ss.0.inject_str(s2);
        let i3 = ss.0.inject_str(s2);
        (i1, i2, i3)
    };
    assert_eq!("hello", i1.as_ref());
    assert_eq!("world", i2.as_ref());
    assert_eq!("world", i3.as_ref());
    assert_ne!(i2.as_ptr(), i3.as_ptr());
}

#[test]
fn str_strategy_string() {
    let ss = (StringStrategy::default(), 0);
    let (i1, i2, i3) = {
        let s1 = "hello";
        let s2 = "world";
        let i1 = ss.0.inject_str(s1);
        let i2 = ss.0.inject_str(s2);
        let i3 = ss.0.inject_str(s2);
        (i1, i2, i3)
    };
    assert_eq!("hello", (i1.as_ref() as &str));
    assert_eq!("world", (i2.as_ref() as &str));
    assert_eq!("world", (i3.as_ref() as &str));
    assert_ne!(i2.as_ptr(), i3.as_ptr());
}

#[test]
fn str_strategy_ref() {
    let ss = (RefStrategy::default(), 0);
    let s1 = "hello";
    let s2 = "world";
    let (i1, i2, i3) = {
        let i1 = ss.0.inject_str(s1);
        let i2 = ss.0.inject_str(s2);
        let i3 = ss.0.inject_str(s2);
        (i1, i2, i3)
    };
    assert_eq!(s1.as_ptr(), i1.as_ptr());
    assert_eq!(s2.as_ptr(), i2.as_ptr());
    assert_eq!(s2.as_ptr(), i3.as_ptr());
}
