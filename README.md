## `another-option`

This package provides `Opt<T>` as an alternative to `Option<T>`. Why would you want another option? `Opt` provides advantages when:

1. the generic type, `T`, is expensive to allocate, and
2. mutation between `None` and `Some(...)` is frequent.

### Examples

Since Rust's built-in `Option<T>` is an enum, it will drop its `Some(...)` value when `None` is assigned.

```rust
let mut option: Option<String> = Some(String::with_capacity(1024));
option = None; // drops the string
option = Some(String::with_capacity(1024)); // allocation
```

Since `Opt<T>` always owns the value, even when empty, the value can be reused without drops or allocations:

```rust
use crate::another_option::Opt;
let mut opt: Opt<String> = Opt::some(String::with_capacity(1024));
opt.map_in_place(|v| v.push_str("value"));
opt.set_none(); // does *not* drop the string
opt.set_some();
assert_eq!(opt.unwrap(), String::from("value"));
```