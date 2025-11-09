Files located under the `examples` directory are example uses of
the functionality provided by the library.
When compiled, they are placed in the `target/debug/examples`
directory.

Examples can use the public API of the package's library. They are also linked
with the `[dependencies]` and
`[dev-dependencies]` defined in `Cargo.toml`.

By default, examples are executable binaries (with a `main()`
function). You can specify the `crate-type` field to make an example
be compiled as a library:

```toml
[[example]]
name = "foo"
crate-type = ["staticlib"]
```

You can run individual executable examples with the `cargo run` command with
the `--example <example-name>` option. Library examples can be built with
`cargo build` with the `--example <example-name>` option. `cargo install`
with the `--example <example-name>` option can be used to copy executable
binaries to a common location. Examples are compiled by `cargo test` by
default to protect them from bit-rotting. Set the `test`
field to `true` if you have `#[test]` functions in the
example that you want to run with `cargo test`.
