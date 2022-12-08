# libeither
An Either struct, that allows serialization to more formats (specifically TOML).

This library is heavily influenced by the [Either](https://docs.rs/either/latest) enum library.  If you don't need struct specific
serialization, you may want to use the enum Either instead.

## Features
* `serde` - Enable serialization (on by default)
* `unstable` - Enable unstable options (nightly only, off by default)

## Current Version
[![Crates.io](https://img.shields.io/crates/v/libeither.svg)](https://crates.io/crates/libeither)
[![Crates.io](https://img.shields.io/crates/l/libeither.svg)](https://crates.io/crates/libeither)
[![Crates.io](https://img.shields.io/crates/d/libeither.svg)](https://crates.io/crates/libeither)

## Build Status
[![CI](https://github.com/rustyhorde/libeither/actions/workflows/main.yml/badge.svg)](https://github.com/rustyhorde/libeither/actions/workflows/main.yml)

## Code Coverage
[![codecov](https://codecov.io/gh/rustyhorde/libeither/branch/master/graph/badge.svg)](https://codecov.io/gh/rustyhorde/libeither)

## License
Licensed under either of
 * Apache License, Version 2.0 ([LICENSE-APACHE](LICENSE-APACHE) or http://www.apache.org/licenses/LICENSE-2.0)
 * MIT license ([LICENSE-MIT](LICENSE-MIT) or http://opensource.org/licenses/MIT)
at your option.

## Contribution
Unless you explicitly state otherwise, any contribution intentionally submitted
for inclusion in the work by you, as defined in the Apache-2.0 license, shall be dual licensed as above, without any
additional terms or conditions.