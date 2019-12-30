//! # `another-option`
//!
//! This package provides `Opt<T>` as an alternative to `Option<T>`. Why would you want another
//! option? `Opt` provides advantages when:
//!
//! 1. the generic type, `T`, is expensive to allocate, and
//! 2. mutation between `None` and `Some(...)` is frequent.
//!
//! ## Examples
//!
//! Since Rust's built-in `Option<T>` is an enum, it will drop its `Some(...)` value when `None`
//! is assigned.
//!
//! ```rust
//! let mut option: Option<String> = Some(String::with_capacity(1024));
//! option = None; // drops the string
//! option = Some(String::with_capacity(1024)); // allocation
//! ```
//!
//! Since `Opt<T>` always owns the value, even when empty, the value can be reused without drops
//! or allocations:
//!
//! ```rust
//! use crate::another_option::Opt;
//! let mut opt: Opt<String> = Opt::some(String::with_capacity(1024));
//! opt.map_in_place(|v| v.push_str("value"));
//! opt.set_none(); // does *not* drop the string
//! opt.set_some(); // does *not* drop the string
//! assert_eq!(opt.unwrap(), String::from("value"));
//! ```

#[derive(Copy, Clone, PartialOrd, Eq, Ord, Debug, Hash)]
pub struct Opt<T> {
    empty: bool,
    value: T,
}

impl<T> PartialEq for Opt<T>
where
    T: std::cmp::PartialEq,
{
    fn eq(&self, other: &Self) -> bool {
        if self.empty && other.empty {
            true
        } else if !self.empty && !other.empty {
            self.value == other.value
        } else {
            false
        }
    }
}

impl<T> Opt<T> {
    /// Construct an option with no value.
    ///
    /// Note: perhaps unexpectedly, this function accepts a `value` argument. This is necessary
    /// given the underlying data structure.
    pub fn none(value: T) -> Opt<T> {
        Opt { empty: true, value }
    }

    /// Construct an option with 'some' value.
    pub fn some(value: T) -> Opt<T> {
        Opt {
            empty: false,
            value,
        }
    }
}

impl<T> Opt<T> {
    // ===== querying the contained value =====

    pub fn is_none(&self) -> bool {
        self.empty
    }

    pub fn is_some(&self) -> bool {
        !self.empty
    }

    // ===== setters =====

    pub fn set_none(&mut self) {
        self.empty = true;
    }

    pub fn set_some(&mut self) {
        self.empty = false;
    }

    pub fn set_some_value(&mut self, value: T) {
        self.empty = false;
        self.value = value;
    }

    // ===== working with references =====

    /// Converts from `&Opt<T>` to `Opt<&T>`.
    pub fn as_ref(&self) -> Opt<&T> {
        Opt {
            empty: self.empty,
            value: &self.value,
        }
    }

    /// Converts from `&mut Opt<T>` to `Opt<&mut T>`.
    pub fn as_mut(&mut self) -> Opt<&mut T> {
        Opt {
            empty: self.empty,
            value: &mut self.value,
        }
    }

    // ===== convert to/from `Option<T>` =====

    // TODO: Does this make sense?
    //  - if yes, do it and test it.
    //  - if no, explain why not.

    // ===== accessing the contained value =====

    pub fn expect(self, msg: &str) -> T {
        if !self.empty {
            self.value
        } else {
            panic!("{}", msg);
        }
    }

    pub fn unwrap(self) -> T {
        if !self.empty {
            self.value
        } else {
            panic!("called `unwrap()` on an empty value")
        }
    }

    pub fn unwrap_or(self, default: T) -> T {
        if !self.empty {
            self.value
        } else {
            default
        }
    }

    pub fn unwrap_or_else<F: FnOnce() -> T>(self, f: F) -> T {
        if !self.empty {
            self.value
        } else {
            f()
        }
    }

    // ===== transforming the contained value =====

    /// Applies the function `f` to the value; regardless if `Opt<T>` is empty or not. Does not
    /// modify the 'emptiness' of the option. (Note: This behavior, though consistent, may seem
    /// strange at first.)
    pub fn map<U, F: FnOnce(T) -> U>(self, f: F) -> Opt<U> {
        Opt {
            empty: self.empty,
            value: f(self.value),
        }
    }

    pub fn map_in_place<F: FnOnce(&mut T)>(&mut self, f: F) {
        f(&mut self.value);
    }

    pub fn map_or<U, F: FnOnce(T) -> U>(self, default: U, f: F) -> U {
        if !self.empty {
            f(self.value)
        } else {
            default
        }
    }

    pub fn map_or_else<U, D: FnOnce() -> U, F: FnOnce(T) -> U>(self, default: D, f: F) -> U {
        if !self.empty {
            f(self.value)
        } else {
            default()
        }
    }

    pub fn ok_or<E>(self, err: E) -> Result<T, E> {
        if !self.empty {
            Ok(self.value)
        } else {
            Err(err)
        }
    }

    pub fn ok_or_else<E, F: FnOnce() -> E>(self, err: F) -> Result<T, E> {
        if !self.empty {
            Ok(self.value)
        } else {
            Err(err())
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    // ===== equality tests =====

    #[test]
    fn test_eq_none() {
        let none_1: Opt<String> = Opt::none(String::with_capacity(22));
        let none_2: Opt<String> = Opt::none(String::with_capacity(44));
        assert_eq!(none_1, none_2);
    }

    #[test]
    fn test_eq_some() {
        let some_thing_1: Opt<String> = Opt::some(String::from("thing"));
        let some_thing_2: Opt<String> = Opt::some(String::from("thing"));
        assert_eq!(some_thing_1, some_thing_2);
    }

    #[test]
    fn test_ne_some() {
        let some_day: Opt<String> = Opt::some(String::from("day"));
        let some_where: Opt<String> = Opt::some(String::from("where"));
        assert_ne!(some_day, some_where);
    }

    #[test]
    fn test_ne_some_none() {
        let some: Opt<String> = Opt::some(String::from("future"));
        let none: Opt<String> = Opt::none(String::with_capacity(22));
        assert_ne!(some, none);
    }

    // ===== `is_some` and `is_none` tests =====

    #[test]
    fn test_is_some_some() {
        let opt: Opt<i16> = Opt::some(42);
        assert_eq!(opt.is_none(), false);
        assert_eq!(opt.is_some(), true);
    }

    #[test]
    fn test_is_none_none() {
        let opt: Opt<i16> = Opt::none(13);
        assert_eq!(opt.is_none(), true);
        assert_eq!(opt.is_some(), false);
    }

    // ===== setter tests =====

    #[test]
    fn test_set_none_1() {
        let mut opt: Opt<i16> = Opt::none(13);
        opt.set_none();
        assert_eq!(opt.is_none(), true);
        assert_eq!(opt.is_some(), false);
    }

    #[test]
    fn test_set_none_2() {
        let mut opt: Opt<i16> = Opt::some(42);
        opt.set_none();
        assert_eq!(opt.is_none(), true);
        assert_eq!(opt.is_some(), false);
    }

    #[test]
    fn test_set_some_1() {
        let mut opt: Opt<i16> = Opt::none(13);
        opt.set_some();
        assert_eq!(opt.is_none(), false);
        assert_eq!(opt.is_some(), true);
        assert_eq!(opt.unwrap(), 13);
    }

    #[test]
    fn test_set_some_2() {
        let mut opt: Opt<i16> = Opt::some(13);
        opt.set_some();
        assert_eq!(opt.is_none(), false);
        assert_eq!(opt.is_some(), true);
        assert_eq!(opt.unwrap(), 13);
    }

    #[test]
    fn test_set_some_value_1() {
        let mut opt: Opt<i16> = Opt::none(13);
        opt.set_some_value(7);
        assert_eq!(opt.is_none(), false);
        assert_eq!(opt.is_some(), true);
        assert_eq!(opt.unwrap(), 7);
    }

    #[test]
    fn test_set_some_value_2() {
        let mut opt: Opt<i16> = Opt::some(13);
        opt.set_some_value(7);
        assert_eq!(opt.is_none(), false);
        assert_eq!(opt.is_some(), true);
        assert_eq!(opt.unwrap(), 7);
    }

    // ===== `as_ref` tests =====

    #[test]
    fn test_as_ref_some() {
        let opt: Opt<i16> = Opt::some(42);
        assert_eq!(opt.as_ref(), Opt::some(&42));
    }

    #[test]
    fn test_as_ref_none() {
        let opt: Opt<i16> = Opt::none(53);
        assert_eq!(opt.as_ref(), Opt::none(&7));
    }

    // ===== `as_mut` tests =====

    #[test]
    fn test_as_mut_some() {
        let mut opt: Opt<i16> = Opt::some(42);
        assert_eq!(opt.as_mut(), Opt::some(&mut 42));
    }

    #[test]
    fn test_as_mut_none() {
        let mut opt: Opt<i16> = Opt::none(53);
        assert_eq!(opt.as_mut(), Opt::none(&mut 7));
    }

    // ===== `expect` tests =====

    #[test]
    fn test_expect_some() {
        assert_eq!(Opt::some(42).expect("error"), 42);
    }

    #[test]
    #[should_panic(expected = "Douglas Adams")]
    fn test_expect_none() {
        Opt::none(29).expect("Douglas Adams");
    }

    // ===== `unwrap` tests =====

    #[test]
    fn test_unwrap_some() {
        assert_eq!(Opt::some(42).unwrap(), 42);
    }

    #[test]
    #[should_panic]
    fn test_unwrap_none() {
        Opt::none(31).unwrap();
    }

    // ===== `unwrap_or` tests =====

    #[test]
    fn test_unwrap_or_some() {
        assert_eq!(Opt::some(42).unwrap_or(99), 42);
    }

    #[test]
    fn test_unwrap_or_none() {
        assert_eq!(Opt::none(-97).unwrap_or(99), 99);
    }

    // ===== `unwrap_or_else` tests =====

    #[test]
    fn test_unwrap_or_else_some() {
        assert_eq!(Opt::some(42).unwrap_or_else(|| -1), 42);
    }

    #[test]
    fn test_unwrap_or_else_none() {
        assert_eq!(Opt::none(-37).unwrap_or_else(|| -1), -1);
    }

    // ===== `map` tests =====

    #[test]
    fn test_map_some_1() {
        assert_eq!(Opt::some(42).map(|x| x + 1), Opt::some(43));
    }

    #[test]
    fn test_map_some_2() {
        let opt_1: Opt<String> = Opt::some(String::from("A"));
        let opt_2 = opt_1.map(|mut s| {
            s.push_str("B");
            s
        });
        assert_eq!(opt_2, Opt::some(String::from("AB")));
    }

    #[test]
    fn test_map_none_1() {
        assert_eq!(Opt::none(431).map(|x| x + 1), Opt::none(0));
    }

    #[test]
    fn test_map_none_2() {
        let opt_1: Opt<String> = Opt::none(String::from("A"));
        let opt_2 = opt_1.map(|mut s| {
            s.push_str("B");
            s
        });
        assert_eq!(opt_2, Opt::none(String::from("AB")));
    }

    // ===== `map_in_place` tests =====

    #[test]
    fn test_map_in_place_some() {
        let mut opt = Opt::some(String::from("A"));
        opt.map_in_place(|s| s.push_str("B"));
        assert_eq!(opt, Opt::some(String::from("AB")));
    }

    #[test]
    fn test_map_in_place_none() {
        let mut opt = Opt::none(String::from("A"));
        opt.map_in_place(|s| s.push_str("B"));
        assert_eq!(opt, Opt::none(String::from("AB")));
    }
}
