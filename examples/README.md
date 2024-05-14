# Examples

This example is composed of three different but equal ways for composing two example components together
* two ways using the `wac` CLI
* using the `wac-graph` library crate

The example uses two input components (both located in the `deps` directory) that will be composed together:

The `hello` component exports a function `hello` which returns a string:

```bash
# Print the wit for the hello component
$ wasm-tools component wit deps/example/hello.wasm 
package root:component;

world root {
  export hello: func() -> string;
}
```

The `hello` exported function from `hello.wasm` will be plugged into the `hello` import of the `greeter` component which has the same signature as the `hello` exported function: 

```bash
# Print the wit for the greeter component
$ wasm-tools component wit deps/example/greeter.wasm 
package root:component;

world root {
  import hello: func() -> string;

  export greet: func() -> string;
}
```

The resulting composed component will therefore only have the exported `greet` function originally from the `greeter` component.

## `wac encode`

`wac` can be used as a CLI tool. The `wac encode` command takes a wac script as input which defines how two components are composed together.

Running the following command should produce a new component that is the composition of the `hello` and `greeter` components.

```bash
wac encode script.wac -o composed.wasm
```

*Note*: `wac encode` expects to find any input components inside of a `deps` folder in a directory named after the namespace part of the input component's name (however, this is configurable with the `--deps-dir` option). In our example, the wac script uses the `example:greeter` and `example:hello` input components so `wac encode` expects to find those components in the `deps/example` directory.

## `wac plug`

`wac` also comes with an opinionated CLI option called `wac plug` which will "plug" the exports of one component (the "plug") into equivalently named imports of another component (the "socket").

In this example, we can do this with the following invocation:

```bash
wac plug --plug deps/example/hello.wasm deps/example/greeter.wasm -o composed.wasm
```

## Programmatic Graph API

You can also build the composition using the programmatic API used by the `programmatic` example binary. This can be done by running the following inside the `programmatic` directory:

```bash
cargo run
```
