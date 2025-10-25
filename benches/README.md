Benchmarks provide a way to test the performance of your code using the
`cargo bench` command. They follow the same structure as tests,
with each benchmark function annotated with the `#[bench]` attribute.
Similarly to tests:

* Benchmarks are placed in the `benches` directory.
* Benchmark functions defined in libraries and binaries have access to the
  *private* API within the target they are defined in. Benchmarks in the
  `benches` directory may use the *public* API.
* The `bench` field can be used to define which targets are benchmarked
  by default.
* The `harness` field can be used to disable the built-in harness.

> **Note**: The `#[bench]` attribute is currently unstable and only
> available on the nightly channel. There are some packages available
> on [crates.io](https://crates.io/keywords/benchmark) that may
> help with running benchmarks on the stable channel, such as
> [Criterion](https://crates.io/crates/criterion).
