use anyhow::{bail, Context, Result};
use pretty_assertions::assert_eq;
use semver::Version;
use serde::Deserialize;
use std::{
    collections::HashMap,
    fs::{self, File},
    path::{Path, PathBuf},
};
use wac_graph::{CompositionGraph, EncodeOptions, NodeId, PackageId};
use wac_types::Package;

#[derive(Deserialize)]
#[serde(rename_all = "camelCase", tag = "type")]
enum Node {
    Import { name: String, path: String },
    Instantiation { package: usize },
    Alias { source: usize, export: String },
}

#[derive(Deserialize)]
#[serde(rename_all = "camelCase")]
struct Argument {
    source: usize,
    target: usize,
    name: String,
}

#[derive(Deserialize)]
#[serde(rename_all = "camelCase")]
struct WatPackage {
    name: String,
    version: Option<Version>,
    path: PathBuf,
}

#[derive(Deserialize)]
#[serde(rename_all = "camelCase")]
struct Name {
    node: usize,
    name: String,
}

#[derive(Deserialize)]
#[serde(rename_all = "camelCase")]
struct Export {
    node: usize,
    name: String,
}

#[derive(Deserialize)]
#[serde(rename_all = "camelCase")]
struct GraphFile {
    #[serde(default)]
    packages: Vec<WatPackage>,
    #[serde(default)]
    nodes: Vec<Node>,
    #[serde(default)]
    arguments: Vec<Argument>,
    #[serde(default)]
    names: Vec<Name>,
    #[serde(default)]
    exports: Vec<Export>,
}

impl GraphFile {
    pub fn into_composition_graph(self, root: &Path, test_case: &str) -> Result<CompositionGraph> {
        let mut graph = CompositionGraph::new();
        let packages = self.register_packages(root, test_case, &mut graph)?;
        let nodes = self.add_nodes(test_case, &packages, &mut graph)?;
        self.add_arguments(test_case, &nodes, &mut graph)?;

        for (index, export) in self.exports.iter().enumerate() {
            let id = nodes
                .get(&export.node)
                .with_context(|| format!("invalid node index {export} referenced in export {index} for test case `{test_case}`", export = export.node))
                .copied()?;

            graph.export_node(id, &export.name).with_context(|| {
                format!(
                    "failed to export node {node} in export {index} for test case `{test_case}`",
                    node = export.node
                )
            })?;
        }

        for (index, name) in self.names.iter().enumerate() {
            let id = nodes
                .get(&name.node)
                .with_context(|| format!("invalid node index {node} referenced in name {index} for test case `{test_case}`", node = name.node))
                .copied()?;

            graph
                .set_node_name(id, &name.name)
                .with_context(|| format!("failed to set node name for node {node} in name {index} for test case `{test_case}`", node = name.node))?;
        }

        Ok(graph)
    }

    fn register_packages(
        &self,
        root: &Path,
        test_case: &str,
        graph: &mut CompositionGraph,
    ) -> Result<HashMap<usize, PackageId>> {
        let mut packages = HashMap::new();

        for (index, package) in self.packages.iter().enumerate() {
            let path = root.join(&package.path);
            let bytes = wat::parse_file(&path).with_context(|| {
                format!(
                    "failed to parse package `{path}` for test case `{test_case}`",
                    path = path.display()
                )
            })?;

            let package = Package::from_bytes(&package.name, package.version.as_ref(), bytes)
                .with_context(|| {
                    format!(
                        "failed to decode package `{path}` for test case `{test_case}`",
                        path = path.display()
                    )
                })?;

            let id = graph.register_package(package).with_context(|| {
                format!(
                    "failed to register package `{path}` for test case `{test_case}`",
                    path = path.display()
                )
            })?;

            packages.insert(index, id);
        }

        Ok(packages)
    }

    fn add_nodes(
        &self,
        test_case: &str,
        packages: &HashMap<usize, PackageId>,
        graph: &mut CompositionGraph,
    ) -> Result<HashMap<usize, NodeId>> {
        let mut nodes = HashMap::new();
        for (index, node) in self.nodes.iter().enumerate() {
            let id = match node {
                Node::Import { name, path } => graph
                    .add_import_node_by_path(name, path, ())
                    .with_context(|| {
                        format!("failed to add import node {index} for test case `{test_case}`")
                    })?,
                Node::Instantiation { package } => {
                    let package = packages
                        .get(package)
                        .with_context(|| {
                            format!("invalid package index {package} referenced in node {index} for test case `{test_case}`")
                        })
                        .copied()?;

                    graph.add_instantiation_node(package, ()).with_context(|| {
                        format!(
                            "failed to add instantiation node {index} for test case `{test_case}`"
                        )
                    })?
                }
                Node::Alias { source, export } => {
                    let source = nodes.get(source).with_context(|| {
                        format!("invalid source node index {source} referenced in node {index} for test case `{test_case}`")
                    })
                    .copied()?;

                    graph.add_alias_node(source, export, ()).with_context(|| {
                        format!("failed to add alias node {index} for test case `{test_case}`")
                    })?
                }
            };

            nodes.insert(index, id);
        }

        Ok(nodes)
    }

    fn add_arguments(
        &self,
        test_case: &str,
        nodes: &HashMap<usize, NodeId>,
        graph: &mut CompositionGraph,
    ) -> Result<()> {
        for (index, argument) in self.arguments.iter().enumerate() {
            let source = nodes.get(&argument.source).with_context(|| {
                format!("invalid source node index {source} referenced in argument {index} for test case `{test_case}`", source = argument.source)
            }).copied()?;

            let target = nodes.get(&argument.target).with_context(|| {
                format!("invalid target node index {target} referenced in argument {index} for test case `{test_case}`", target = argument.target)
            }).copied()?;

            graph.add_argument_edge(source, target, &argument.name).with_context(|| {
                format!("failed to add argument edge from source node {source} to target node {target} referenced in argument {index} for test case `{test_case}`", source = argument.source, target = argument.target)
            })?;
        }

        Ok(())
    }
}

/// Tests the encoding of composition graphs.
///
/// This test looks in the `graphs/` directory for test cases.
///
/// The expected input files for a test case are:
/// * [required] `graph.json` - a JSON representation of a composition graph
///   (see above for serialization format).
/// * [optional] `*.wat` - packages (i.e. components) referenced from `graph.json`.
///
/// And the output files are one of the following:
///
/// * `encoded.wat` - the encoded component if the encoding is expected to succeed.
/// * `error.txt` - the expected error message if the encoding is expected to fail.
///
/// The test builds a composition graph from the JSON representation and attempts to
/// encode it. If the encoding succeeds, it expects the output to match `encoded.wat`.
/// If the encoding fails, it expects the output to match `error.txt`.
///
/// Run the test with the environment variable `BLESS` set to update
/// either `encoded.wat` or `error.txt` depending on the outcome of the encoding.
#[test]
fn encoding() -> Result<()> {
    for entry in fs::read_dir("tests/graphs")? {
        let path = entry?.path();
        if !path.is_dir() {
            continue;
        }

        let test_case = path.file_stem().unwrap().to_str().unwrap();
        println!("================ test: {test_case} ================");
        let graph = path.join("graph.json");
        let output_path = path.join("encoded.wat");
        let error_path = path.join("error.txt");

        let file = File::open(&graph).with_context(|| {
            format!("failed to read graph file `{path}`", path = graph.display())
        })?;

        let r = serde_json::from_reader::<_, GraphFile>(file)
            .with_context(|| {
                format!(
                    "failed to deserialize graph file `{path}` for test case `{test_case}`",
                    path = graph.display()
                )
            })?
            .into_composition_graph(&path, test_case)
            .and_then(|graph| {
                graph
                    .encode(EncodeOptions::default())
                    .context("failed to encode the graph")
            });

        let (output, baseline_path) = if error_path.is_file() {
            match r {
                Ok(_) => bail!("expected a test failure for test case `{test_case}`"),
                Err(e) => (format!("{e:?}\n").replace('\\', "/"), &error_path),
            }
        } else {
            let bytes =
                r.with_context(|| format!("failed to encode for test case `{test_case}`"))?;

            (
                wasmprinter::print_bytes(&bytes).with_context(|| {
                    format!("failed to print encoded bytes for test case `{test_case}`")
                })?,
                &output_path,
            )
        };

        if std::env::var_os("BLESS").is_some() {
            fs::write(baseline_path, output)?;
        } else {
            assert_eq!(
                fs::read_to_string(baseline_path)
                    .with_context(|| format!(
                        "failed to read test baseline `{path}`",
                        path = baseline_path.display()
                    ))?
                    .replace("\r\n", "\n"),
                output,
                "failed baseline comparison for test case `{test_case}` ({path})",
                path = baseline_path.display(),
            );
        }
    }

    Ok(())
}
