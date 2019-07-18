# saturating-rs

`Saturating<T>` is an intentionally-saturating arithmetic wrapper, similar to [`std::num::Wrapping`](https://doc.rust-lang.org/std/num/struct.Wrapping.html).

## Examples

```rust
use saturating::Saturating;

let foo = Saturating(253u8);
let bar = Saturating(100u8);

assert_eq!(std::u8::MAX, (foo + bar).0);
```
