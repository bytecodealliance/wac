<div align="center">
  <h1><code>WebAssembly Compositions (WAC)</code></h1>

<strong>A <a href="https://bytecodealliance.org/">Bytecode Alliance</a> project</strong>

  <p>
    <strong>A tool for composing <a href="https://github.com/WebAssembly/component-model/">WebAssembly components</a> together.</strong>
  </p>

  <p>
    <a href="https://github.com/bytecodealliance/wasm-tools/actions?query=workflow%3ACI"><img src="https://github.com/bytecodealliance/wasm-tools/workflows/CI/badge.svg" alt="build status" /></a>
    <a href="https://crates.io/crates/wasm-tools"><img src="https://img.shields.io/crates/v/wac-cli.svg?style=flat-square" alt="Crates.io version" /></a>
    <a href="https://crates.io/crates/wac-cli"><img src="https://img.shields.io/crates/d/wac-cli.svg?style=flat-square" alt="Download" /></a>
    <a href="https://docs.rs/wac-cli/"><img src="https://img.shields.io/badge/docs-latest-blue.svg?style=flat-square" alt="docs.rs docs" /></a>
  </p>
</div>

## Overview

`wac` is a tool for composing [WebAssembly Components](https://github.com/WebAssembly/component-model)
together.

The tool uses the WAC (pronounced "whack") language to define how components
composed together.

## Language

See the [language documentation](LANGUAGE.md) for more information on the
syntax of WAC.

## Installation

```
cargo install --git https://github.com/peterhuene/wac --locked
```

To enable support Warg component registries, specify the `registry` feature:

```
cargo install --git https://github.com/peterhuene/wac --locked --features registry
```

## Usage

The `wac` CLI tool has three commands:

* `wac parse` - Parses a composition into a JSON representation of the AST.
* `wac resolve` - Resolves a composition into a JSON representation.
* `wac encode` - Encodes a WAC source file as a WebAssembly component.

### Encoding Compositions

To encode a composition, use the `wac encode` command:

```
wac encode -t input.wac
```

This will encode `input.wac` as a WebAssembly component and write the text
representation of the component to stdout.

```
wac encode -o output.wasm input.wac
```

This will encode `input.wac` as a WebAssembly component named `output.wasm`.

By default, `wac` will import dependencies rather than defining  (i.e.
embedding) them in the output component; to define dependencies in the output
component, use the `--define` flag:

```
wac encode --define -o output.wasm input.wac
```

#### Dependencies

Dependencies (i.e. packages referenced in a WAC source file) may be located
within a `deps` subdirectory, with an expected structure of:

```
deps/
├─ <namespace>/
│  ├─ <package>.wasm
``````
If the `wit` build-time feature is enabled, the dependency may be a directory
containing a WIT package:

```
deps/
├─ <namespace>/
│  ├─ <package>/
│  │  ├─ a.wit
│  │  ├─ ...
```

The `--deps-dir` CLI option may be used to specify a different directory to
search for dependencies.

If the `registry` build-time feature is enabled, then dependencies may be
automatically resolved from a Warg registry and do not need to exist in the
`deps` subdirectory.
