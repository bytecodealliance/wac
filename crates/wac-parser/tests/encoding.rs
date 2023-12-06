use anyhow::{anyhow, bail, Context, Result};
use owo_colors::OwoColorize;
use pretty_assertions::StrComparison;
use rayon::prelude::*;
use std::{
    env,
    ffi::OsStr,
    fs,
    path::{Path, PathBuf},
    process::exit,
    sync::atomic::{AtomicUsize, Ordering},
};
use support::fmt_err;
use wac_parser::{ast::Document, Composition, EncodingOptions};
use wac_resolver::{packages, FileSystemPackageResolver};

mod support;

fn find_tests() -> Vec<PathBuf> {
    let mut tests = Vec::new();
    find_tests("tests/encoding", &mut tests);
    tests.sort();
    return tests;

    fn find_tests(path: impl AsRef<Path>, tests: &mut Vec<PathBuf>) {
        for entry in path.as_ref().read_dir().unwrap() {
            let path = entry.unwrap().path();
            if path.is_dir() {
                continue;
            }

            match path.extension().and_then(|s| s.to_str()) {
                Some("wac") => {}
                _ => continue,
            }

            tests.push(path);
        }
    }
}

fn normalize(s: &str) -> String {
    // Normalize line endings
    s.replace("\r\n", "\n")
}

fn compare_result(test: &Path, result: &str) -> Result<()> {
    let path = test.with_extension("wat.result");

    let result = normalize(result);
    if env::var_os("BLESS").is_some() {
        fs::write(&path, &result).with_context(|| {
            format!(
                "failed to write result file `{path}`",
                path = path.display()
            )
        })?;
        return Ok(());
    }

    let expected = fs::read_to_string(&path)
        .with_context(|| format!("failed to read result file `{path}`", path = path.display()))?
        .replace("\r\n", "\n");

    if expected != result {
        bail!(
            "result is not as expected:\n{}",
            StrComparison::new(&expected, &result),
        );
    }

    Ok(())
}

fn run_test(test: &Path, ntests: &AtomicUsize) -> Result<()> {
    let source = std::fs::read_to_string(test)?.replace("\r\n", "\n");

    let document = Document::parse(&source).map_err(|e| anyhow!(fmt_err(e, test, &source)))?;

    let resolver = FileSystemPackageResolver::new(
        test.parent().unwrap().join(test.file_stem().unwrap()),
        Default::default(),
        true,
    );

    let packages = resolver.resolve(&packages(&document)?)?;

    let bytes = Composition::from_ast(&document, packages)
        .map_err(|e| anyhow!(fmt_err(e, test, &source)))?
        .encode(EncodingOptions::default())
        .with_context(|| {
            format!(
                "failed to encode the composition `{path}`",
                path = test.display()
            )
        })?;

    wasmparser::Validator::new_with_features(wasmparser::WasmFeatures {
        component_model: true,
        ..Default::default()
    })
    .validate_all(&bytes)
    .with_context(|| {
        format!(
            "failed to validate the encoded composition `{path}`",
            path = test.display()
        )
    })?;

    let result = wasmprinter::print_bytes(bytes).with_context(|| {
        format!(
            "failed to convert binary wasm output to text `{path}`",
            path = test.display()
        )
    })?;

    compare_result(test, &result)?;

    ntests.fetch_add(1, Ordering::SeqCst);
    Ok(())
}

fn main() {
    pretty_env_logger::init();

    let tests = find_tests();
    println!("running {} tests\n", tests.len());

    let ntests = AtomicUsize::new(0);
    let errors = tests
        .par_iter()
        .filter_map(|test| {
            let test_name = test.file_stem().and_then(OsStr::to_str).unwrap();
            match std::panic::catch_unwind(|| {
                match run_test(test, &ntests)
                    .with_context(|| format!("failed to run test `{path}`", path = test.display()))
                    .err()
                {
                    Some(e) => {
                        println!("test {test_name} ... {failed}", failed = "failed".red());
                        Some((test_name, e))
                    }
                    None => {
                        println!("test {test_name} ... {ok}", ok = "ok".green());
                        None
                    }
                }
            }) {
                Ok(result) => result,
                Err(e) => {
                    println!(
                        "test {test_name} ... {panicked}",
                        panicked = "panicked".red()
                    );
                    Some((
                        test_name,
                        anyhow!(
                            "test panicked: {e:?}",
                            e = e
                                .downcast_ref::<String>()
                                .map(|s| s.as_str())
                                .or_else(|| e.downcast_ref::<&str>().copied())
                                .unwrap_or("no panic message")
                        ),
                    ))
                }
            }
        })
        .collect::<Vec<_>>();

    if !errors.is_empty() {
        eprintln!(
            "\n{count} test(s) {failed}:",
            count = errors.len(),
            failed = "failed".red()
        );

        for (name, msg) in errors.iter() {
            eprintln!("{name}: {msg:?}", msg = msg.red());
        }

        exit(1);
    }

    println!(
        "\ntest result: ok. {} passed\n",
        ntests.load(Ordering::SeqCst)
    );
}
