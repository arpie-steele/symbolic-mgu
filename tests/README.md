There are two styles of tests within a Cargo project:

* *Unit tests* which are functions marked with the `#[test]` attribute
  located within your library or binaries (or any target enabled
  with the `test` field). These tests have access to private APIs
  located within the target they are defined in.
* *Integration tests* which is a separate executable binary, also containing
  `#[test]` functions, which is linked with the project's library and has
  access to its *public* API.

Tests are run with the `cargo test` command. By default, Cargo and
`rustc` use the libtest harness which is responsible for collecting
functions annotated with the `#[test]` attribute and executing them
in parallel, reporting the success and failure of each test.  See
the `harness` field if you want to use a different harness or test
strategy.

> **Note**: There is another special style of test in Cargo:
> documentation tests They are handled by `rustdoc` and have a
> slightly different execution model.  For more information, please
> see `cargo test`.
