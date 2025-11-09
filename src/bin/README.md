Binary targets are executable programs that can be run after being
compiled.  A binary's source can be `src/main.rs` and/or stored in
the `src/bin/` directory. For `src/main.rs`, the default binary
name is the package name. The settings for each binary can be
customized in the`[[bin]]` tables in `Cargo.toml`.

Binaries can use the public API of the package's library. They are also linked
with the `[dependencies]` defined in `Cargo.toml`.

You can run individual binaries with the `cargo run` command with the `--bin
<bin-name>` option. `cargo install` can be used to copy the executable to a
common location.

```toml
# Example of customizing binaries in Cargo.toml.
[[bin]]
name = "cool-tool"
test = false
bench = false

[[bin]]
name = "frobnicator"
required-features = ["frobnicate"]
```
