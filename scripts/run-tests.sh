#!/bin/bash
set -ev
echo ${TRAVIS_RUST_VERSION}
cargo build --features serde
cargo test --features serde
cargo doc --features serde
