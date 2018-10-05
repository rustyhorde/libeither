#!/bin/bash
set -ev
echo ${TRAVIS_RUST_VERSION}

if [ "${TRAVIS_RUST_VERSION}" = "stable" ]; then
    cargo build --features serde
    cargo test --features serde
    cargo doc --features serde
elif [ "${TRAVIS_RUST_VERSION}" = "beta" ]; then
    cargo build --features serde
    cargo test --features serde
    cargo doc --features serde
else
    cargo build --features serde,unstable
    cargo test --features serde,unstable
    cargo doc --features serde,unstable
fi
