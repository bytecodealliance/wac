<div align="center">
  <h1><code>WebAssembly Compositions (WAC)</code></h1>

<strong>A <a href="https://bytecodealliance.org/">Bytecode Alliance</a> project</strong>

  <p>
    <strong>A tool for composing <a href="https://github.com/WebAssembly/component-model/">WebAssembly components</a> together.</strong>
  </p>

  <p>
    <a href="https://github.com/bytecodealliance/wac/actions?query=workflow%3ACI"><img src="https://github.com/bytecodealliance/wac/workflows/CI/badge.svg" alt="build status" /></a>
    <a href="https://crates.io/crates/wac-parser"><img src="https://img.shields.io/crates/v/wac-cli.svg?style=flat-square" alt="Crates.io version" /></a>
    <a href="https://crates.io/crates/wac-cli"><img src="https://img.shields.io/crates/d/wac-cli.svg?style=flat-square" alt="Download" /></a>
    <a href="https://docs.rs/wac-parser/"><img src="https://img.shields.io/badge/docs-latest-blue.svg?style=flat-square" alt="docs.rs docs" /></a>
  </p>
</div>

## Overview

`wac` is a tool for composing [WebAssembly Components](https://github.com/WebAssembly/component-model)
together.

The tool uses the WAC (pronounced "whack") language to define how components
composed together.

## The `wac` Language

The `wac` language is a declarative superset of [`wit`](https://component-model.bytecodealliance.org/design/wit.html) 
for describing how components are composed together.

As an example, imagine two components name.wasm and greeter.wasm.

The wit for name.wasm is:

```wit
package example:name;

world name {
  /// Exporting a 'name' function that returns a name to greet.
  export name: func() -> string;
}
```

And the wit for greeter.wasm is:

```wit
package example:greeter;

world greeter {
  /// Importing a 'name' function that returns the name to greet.
  import name: func() -> string;
  /// Exporting a 'greet' function that returns a greeting using the name.
  export greet: func() -> string;
}
```

The following is an example of a wac file that composes these two components together 
by plugging name.wasm's "name" export into greeter.wasm's "name" import.

```wac
package example:composition;

// Instantiate the `name` component
let n = new example:name {};

// Instantiate the `greeter` component by plugging its `name`
// import with the `name` export of the `name` component.
let greeter = new example:greeter {
  name: n.name,
};

// Export the greet function from the greeter component
export greeter.greet;
```

The result of encoding this composition is a single component that
does not import anything and only exports the "greet" function.

For a full description of the `wac` language see [the language guide](LANGUAGE.md).

## Installation

To install the `wac` CLI from source, run the following command:

```
cargo install wac-cli
```

If you have the [cargo-binstall](https://github.com/cargo-bins/cargo-binstall)
utility installed, `wac` CLI can also be installed via a prebuilt
release artifact, saving time on the installation:

```
cargo binstall wac-cli
```

## Usage

The `wac` CLI tool has the following commands:

* `wac plug` - Plugs the imports of a component with one or more other components.
* `wac compose` - Compose WebAssembly components using the provided WAC source file.
* `wac targets` - Determines whether a given component conforms to the supplied wit world.
* `wac parse` - Parses a composition into a JSON representation of the AST.
* `wac resolve` - Resolves a composition into a JSON representation.

### Quick & Easy Compositions

To do simple compositions, use the `wac plug` command:

```
wac plug my-socket.wasm --plug my-plug.wasm -o plugged.wasm
```

Or mixing in packages published to a Warg registry:

```
wac plug my-namespace:package-name --plug some-namespace:other-package-name -o plugged.wasm
```

### Checking Whether a Component Implements a World

To see whether a given component implements a given world, use the `wac targets` command:

```
wac targets my-component.wasm my-wit.wit
```

If `my-component.wasm` implements the world defined in `my-wit.wit` then the command will succeed. Otherwise, an error will be returned.

If `my-wit.wit` has multiple world definitions, you can disambiguate using the `--world` flag.

### Encoding Compositions

To perform a composition, use the `wac compose` command:

```
wac compose -t input.wac
```

This will use `input.wac` to perform the composition and write the text
representation of the component to stdout.

```
wac compose -o output.wasm input.wac
```

This will perform the composition specified in `input.wac` and output a WebAssembly component named `output.wasm`.

#### Dependencies

By default, `wac` will create a component that embeds its dependencies (i.e. packages
referenced in a WAC source file) inside of itself rather than importing those dependencies;
to cause dependencies to be imported in the output component, use the
`--import-dependencies` flag:

```
wac compose --import-dependencies -o output.wasm input.wac
```

Dependencies may be located within a `deps` subdirectory, with an expected structure of:

```
deps/
├─ <namespace>/
│  ├─ <package>.wasm
``````

The dependency may be also be a WIT file or a directory containing a WIT package:

```
deps/
├─ <namespace>/
│  ├─ <package>/
│  │  ├─ a.wit
│  │  ├─ ...
```

The `--deps-dir` CLI option may be used to specify a different directory to
search for dependencies.

The location of specific dependencies may also be specified with the `--dep` CLI option:

```
wac compose --dep foo:bar=./baz.wasm -o output.wasm input.wac
```

By default, dependencies must be binary-encoded WebAssembly components; to
enable support for WAT files, use the `wat` build-time feature.

If built with default features, then dependencies may be
automatically resolved from a Warg registry and do not need to exist in the
`deps` subdirectory or specified via the `--dep` CLI option.
