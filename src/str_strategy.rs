//! Provides a specific way to inject [string slice]s into other forms which
//! are [representable] as a [string slice]s. This provides opportunities for
//! caching, etc., when [interior mutability] is used.
//!
//! The strategies are:
//!
//! + cache it in a hash set, and yield `Rc<str>`, [`RcStrategy`]
//! + cache it in a hash set, and yield [`HoldingRef`], [`HoldingRefStrategy`]
//! + cache it in a hash set, but shareable across threads, [`ArcStrategy`]
//! + box it in the heap, [`BoxStrategy`]
//! + box it in the heap as a String, [`StringStrategy`]
//! + just return the slice, [`RefStrategy`]
//!
//! [generic way]: trait.StrStrategy.html
//! [can be represented]: https://doc.rust-lang.org/std/convert/trait.AsRef.html
//! [string slice]: https://doc.rust-lang.org/std/primitive.str.html
//! [`HoldingRef`]: struct.HoldingRef.html
//! [`HoldingRefStrategy`]: struct.HoldingRefStrategy.html
//! [`ArcStrategy`]: struct.ArcStrategy.html
//! [`RcStrategy`]: struct.RcStrategy.html
//! [`BoxStrategy`]: struct.BoxStrategy.html`
//! [`StringStrategy`]: struct.StringStrategy.html
//! [`RefStrategy`]: struct.RefStrategy.html

use std::collections::HashSet;
use std::cell::UnsafeCell;
use std::rc::Rc;
use std::sync::Arc;
use std::hash::Hash;
use std::ops::Deref;

use unreachable::UncheckedOptionExt;

//============================================================================//
// StrStrategy (trait)
//============================================================================//

/// Provides a specific way to inject [string slice]s into other forms which
/// are [representable] as a [string slice]s. This provides opportunities for
/// caching, etc., when [interior mutability] is used.
///
/// [representable]: https://doc.rust-lang.org/std/convert/trait.AsRef.html
/// [string slice]: https://doc.rust-lang.org/std/primitive.str.html
/// [interior mutability]: https://doc.rust-lang.org/std/cell
pub trait StrStrategy<'a> {
    /// The type of outputs, representable as a string slice,
    /// that the strategy yields when used.
    type Output: AsRef<str>;

    /// Injects the contents from string slices to one of
    /// type [`Output`], with potential side effects.
    ///
    /// Subsequent applications should not panic.
    ///
    /// [`Output`]: trait.StrStrategy.html#associatedtype.Output
    fn inject_str(&self, input: &'a str) -> Self::Output;
}

/// [`StrStrategy`] which also cache:s injected strings.
/// These are based on [`HashSet`]s and provide an immutable view into the set.
///
/// [`StrStrategy`]: trait.StrStrategy.html
/// [`HashSet`]: https://doc.rust-lang.org/std/collections/struct.HashSet.html
pub trait CachingStrStrategy<'a, Store>
where
    Self: StrStrategy<'a>,
    Store: Eq + Hash,
{
    /// Provides an immutable view of the backing `HashSet` storage.
    fn store<'store>(&'store self) -> &'store HashSet<Store>;
}

macro_rules! caching_strategy {
    ($recv: ty, $store: ty) => {
        impl $recv {
            unsafe fn store_mut(&self) -> &mut HashSet<$store> {
                self.0.get().as_mut().unchecked_unwrap()
            }
        }

        impl <'a> CachingStrStrategy<'a, $store> for $recv {
            fn store(&self) -> &HashSet<$store> {
                unsafe { self.0.get().as_ref().unchecked_unwrap() }
            }
        }
    };
}

macro_rules! cs_get_or_insert {
    ($self: ident, $input: ident) => {{
        let si = unsafe { $self.store_mut() };

        // TODO: Replace with entry API if and when HashSet:s get them.
        if !si.contains($input) {
            si.insert($input.into());
        }

        let out = si.get($input);

        unsafe { out.unchecked_unwrap() }
    }};
}

//============================================================================//
// HoldingRefStrategy
//============================================================================//

/// Synonym for storage of `HoldingRefStrategy`.
type HRSInside = Rc<UnsafeCell<HashSet<Box<str>>>>;

/// A caching [`StrStrategy`] using the heap.
/// Identical strings are only allocated once.
/// Compared to [`RcStrategy`], this version uses more stack space but less
/// heap space.
///
/// The strategy is internally backed by a [`HashSet`]
/// which is never removed from.
///
/// [`RcStrategy`]: struct.RcStrategy.html
/// [`StrStrategy`]: trait.StrStrategy.html
/// [`HashSet`]: https://doc.rust-lang.org/std/collections/struct.HashSet.html
#[derive(Debug, Default)]
pub struct HoldingRefStrategy(HRSInside);

impl<'a> StrStrategy<'a> for HoldingRefStrategy {
    type Output = HoldingRef;

    /// Allocates the given input in the cache and yields a HoldingRef to it.
    fn inject_str(&self, input: &'a str) -> Self::Output {
        /*
         * This is safe because nothing is ever removed from the HashSet,
         * and when it grows (length == capacity), Box<str> may be moved,
         * but the heap allocated contents are never deallocated,
         * thus the HoldingRef returned always points to a valid memory location.
         * Therefore, this will never cause memory unsafety.
         *
         * In addition, UnsafeCell causes HashSetStrategy to be !Sync, which
         * makes unsynchronized mutation impossible. Were this not the case,
         * a data race could occur when reallocation of the HashSet occurs.
         */
        let out = cs_get_or_insert!(self, input);
        HoldingRef {
            parent: self.0.clone(),
            item: out.as_ref(),
        }
    }
}

caching_strategy!(HoldingRefStrategy, Box<str>);

/// A reference into boxed string slice stored inside a [`HoldingRefStrategy`].
///
/// [`HoldingRef`]: struct.HoldingRefStrategy.html
pub struct HoldingRef {
    parent: HRSInside,
    item: *const str,
}

impl AsRef<str> for HoldingRef {
    fn as_ref(&self) -> &str {
        unsafe { &*self.item }
    }
}

impl Deref for HoldingRef {
    type Target = str;

    fn deref(&self) -> &Self::Target {
        unsafe { &*self.item }
    }
}

//============================================================================//
// ArcStrategy
//============================================================================//

/// A caching [`StrStrategy`] using the heap.
/// Identical strings are only allocated once.
/// Unlike [`RcStrategy`], the strategy allocates into [`Arc`]s.
///
/// The strategy is internally backed by a [`HashSet`]
/// which is never removed from.
///
/// [`StrStrategy`]: trait.StrStrategy.html
/// [`RcStrategy`]: struct.RcStrategy.html
/// [`HashSet`]: https://doc.rust-lang.org/std/collections/struct.HashSet.html
/// [`Arc`]: https://doc.rust-lang.org/std/sync/struct.Arc.html
#[derive(Debug, Default)]
pub struct ArcStrategy(UnsafeCell<HashSet<Arc<str>>>);

impl<'a> StrStrategy<'a> for ArcStrategy {
    type Output = Arc<str>;

    /// Allocates the given input in the cache and yields a cloned Arc<str>.
    fn inject_str(&self, input: &'a str) -> Self::Output {
        /*
         * This is safe since UnsafeCell causes HashSetStrategy to be !Sync,
         * which makes unsynchronized mutation impossible.
         */
        cs_get_or_insert!(self, input).clone()
    }
}

caching_strategy!(ArcStrategy, Arc<str>);

//============================================================================//
// RcStrategy
//============================================================================//

/// A caching [`StrStrategy`] using the heap.
/// Identical strings are only allocated once.
///
/// The strategy is internally backed by a [`HashSet`]
/// which is never removed from.
///
/// [`StrStrategy`]: trait.StrStrategy.html
/// [`HashSet`]: https://doc.rust-lang.org/std/collections/struct.HashSet.html
#[derive(Debug, Default)]
pub struct RcStrategy(UnsafeCell<HashSet<Rc<str>>>);

impl<'a> StrStrategy<'a> for RcStrategy {
    type Output = Rc<str>;

    /// Allocates the given input in the cache and yields a cloned Rc<str>.
    fn inject_str(&self, input: &'a str) -> Self::Output {
        /*
         * This is safe since UnsafeCell causes HashSetStrategy to be !Sync,
         * which makes unsynchronized mutation impossible.
         */
         cs_get_or_insert!(self, input).clone()
    }
}

caching_strategy!(RcStrategy, Rc<str>);

//============================================================================//
// BoxStrategy
//============================================================================//

/// A [`StrStrategy`] that simply allocates using the heap.
///
/// [`StrStrategy`]: trait.StrStrategy.html
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default, PartialOrd, Ord, Hash)]
pub struct BoxStrategy;

impl<'a> StrStrategy<'a> for BoxStrategy {
    type Output = Box<str>;

    /// Allocates the input on the heap and just returns that box.
    fn inject_str(&self, input: &'a str) -> Self::Output {
        input.into()
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
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default, PartialOrd, Ord, Hash)]
pub struct StringStrategy;

impl<'a> StrStrategy<'a> for StringStrategy {
    type Output = String;

    /// Allocates the input on the heap as a [`String`] and just returns it.
    /// [`String`]: https://doc.rust-lang.org/nightly/collections/string/struct.String.html
    fn inject_str(&self, input: &'a str) -> Self::Output {
        input.into()
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
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default, PartialOrd, Ord, Hash)]
pub struct RefStrategy;

impl<'a> StrStrategy<'a> for RefStrategy {
    type Output = &'a str;

    /// Returns the given input back.
    fn inject_str(&self, input: &'a str) -> Self::Output {
        input
    }
}

//============================================================================//
// Tests
//============================================================================//

#[test]
fn str_strategy_holdingref() {
    let (i1, i2, i3) = {
        let ss = (HoldingRefStrategy::default(), 0);
        let s1 = "hello";
        let s2 = "world";
        let i1 = ss.0.inject_str(s1);
        // Force reallocation. We do this to ensure that addresses are stable.
        unsafe {
            ss.0.store_mut().reserve(10);
        }
        let i2 = ss.0.inject_str(s2);
        let i3 = ss.0.inject_str(s2);

        assert!(ss.0.store().contains("hello"));
        assert!(ss.0.store().contains("world"));
        assert!(ss.0.store().len() == 2);

        (i1, i2, i3)
    };
    assert_eq!("hello", i1.as_ref());
    assert_eq!("world", i2.as_ref());
    assert_eq!("world", i3.as_ref());
    assert_eq!(i2.as_ptr(), i3.as_ptr());
    /*
    Won't compile since ArcStrategy is not Sync:
    let ss1 = std::sync::Arc::new(ArcStrategy::default());
    */
}

#[test]
fn str_strategy_arc() {
    let (i1, i2, i3) = {
        let ss = (ArcStrategy::default(), 0);
        let s1 = "hello";
        let s2 = "world";
        let i1 = ss.0.inject_str(s1);
        // Force reallocation. We do this to ensure that addresses are stable.
        unsafe {
            ss.0.store_mut().reserve(10);
        }
        let i2 = ss.0.inject_str(s2);
        let i3 = ss.0.inject_str(s2);

        assert!(ss.0.store().contains("hello"));
        assert!(ss.0.store().contains("world"));
        assert!(ss.0.store().len() == 2);

        (i1, i2, i3)
    };
    assert_eq!("hello", i1.as_ref());
    assert_eq!("world", i2.as_ref());
    assert_eq!("world", i3.as_ref());
    assert_eq!(i2.as_ptr(), i3.as_ptr());
    /*
    Won't compile since ArcStrategy is not Sync:
    let ss1 = std::sync::Arc::new(ArcStrategy::default());
    */
}

#[test]
fn str_strategy_rc() {
    let (i1, i2, i3) = {
        let ss = (RcStrategy::default(), 0);
        let s1 = "hello";
        let s2 = "world";
        let i1 = ss.0.inject_str(s1);
        // Force reallocation. We do this to ensure that addresses are stable.
        unsafe {
            ss.0.store_mut().reserve(10);
        }
        let i2 = ss.0.inject_str(s2);
        let i3 = ss.0.inject_str(s2);

        assert!(ss.0.store().contains("hello"));
        assert!(ss.0.store().contains("world"));
        assert!(ss.0.store().len() == 2);

        (i1, i2, i3)
    };
    assert_eq!("hello", i1.as_ref());
    assert_eq!("world", i2.as_ref());
    assert_eq!("world", i3.as_ref());
    assert_eq!(i2.as_ptr(), i3.as_ptr());
    /*
    Won't compile since ArcStrategy is not Sync:
    let ss1 = std::sync::Arc::new(RcStrategy::default());
    */
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