use wac_graph::{types::Package, CompositionGraph, EncodeOptions};

fn main() {
    let mut graph = CompositionGraph::new();

    // Register the package dependencies into the graph
    let package = Package::from_file(
        "hello",
        None,
        "../deps/example/hello.wasm",
        graph.types_mut(),
    )
    .unwrap();
    let hello = graph.register_package(package).unwrap();
    let package = Package::from_file(
        "greeter",
        None,
        "../deps/example/greeter.wasm",
        graph.types_mut(),
    )
    .unwrap();
    let greeter = graph.register_package(package).unwrap();

    // Instantiate the hello instance which does not have any arguments
    let hello_instance = graph.instantiate(hello);

    // Instantiate the greeter instance which has a single argument "hello" which is exported by the hello instance
    let greeter_instance = graph.instantiate(greeter);
    let hello_export = graph
        .alias_instance_export(hello_instance, "hello")
        .unwrap();
    graph
        .set_instantiation_argument(greeter_instance, "hello", hello_export)
        .unwrap();

    // Alias the "greet" export from the greeter instance
    let greet_export = graph
        .alias_instance_export(greeter_instance, "greet")
        .unwrap();
    // Export the "greet" function from the composition
    graph.export(greet_export, "greet").unwrap();

    // Encode the graph into a WASM binary
    let encoding = graph.encode(EncodeOptions::default()).unwrap();
    std::fs::write("composition.wasm", encoding).unwrap();
}
