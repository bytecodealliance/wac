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
use wac_parser::{ast::Document, Composition};
use wac_resolver::{packages, FileSystemPackageResolver};

mod support;

fn find_tests() -> Vec<PathBuf> {
    let mut tests = Vec::new();
    find_tests("tests/resolution", &mut tests);
    find_tests("tests/resolution/fail", &mut tests);
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

fn normalize(s: &str, should_fail: bool) -> String {
    if should_fail {
        // Normalize paths in any error messages
        return s.replace('\\', "/").replace("\r\n", "\n");
    }

    // Otherwise, just normalize line endings
    s.replace("\r\n", "\n")
}

fn compare_result(test: &Path, result: &str, should_fail: bool) -> Result<()> {
    let path = test.with_extension("wac.result");

    let result = normalize(result, should_fail);
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
    let should_fail = test.parent().map(|p| p.ends_with("fail")).unwrap_or(false);
    let source = std::fs::read_to_string(test)?.replace("\r\n", "\n");

    let document = Document::parse(&source).map_err(|e| anyhow!(fmt_err(e, test, &source)))?;

    let resolve = || {
        let resolver = FileSystemPackageResolver::new(
            test.parent().unwrap().join(test.file_stem().unwrap()),
            Default::default(),
            true,
        );

        let packages = resolver
            .resolve(&packages(&document).map_err(|e| fmt_err(e, test, &source))?)
            .map_err(|e| fmt_err(e, test, &source))?;

        Composition::from_ast(&document, packages).map_err(|e| fmt_err(e, test, &source))
    };

    let result = match resolve() {
        Ok(doc) => {
            if should_fail {
                bail!("the resolution was successful but it was expected to fail");
            }

            serde_json::to_string_pretty(&doc)?
        }
        Err(e) => {
            if !should_fail {
                return Err(anyhow!(e))
                    .context("the resolution failed but it was expected to succeed");
            }

            e
        }
    };

    compare_result(test, &result, should_fail)?;

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
