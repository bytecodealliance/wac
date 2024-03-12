use crate::support::{publish_component, publish_wit, spawn_server};
use anyhow::Result;
use pretty_assertions::assert_eq;
use tempdir::TempDir;
use wac_parser::{ast::Document, Composition, EncodingOptions};
use wac_resolver::{packages, RegistryPackageResolver};

mod support;

#[tokio::test(flavor = "multi_thread", worker_threads = 1)]
async fn it_resolves_registry_packages() -> Result<()> {
    let root = TempDir::new("test")?;
    let (_server, config) = spawn_server(root.path()).await?;
    config.write_to_file(&root.path().join("warg-config.json"))?;

    publish_component(
        &config,
        "test:comp",
        "0.1.0",
        r#"
(component
  (import "test:wit/foo" (instance (export "bar" (func))))
  (export "test:wit/foo" (instance 0))
)
"#,
        true,
    )
    .await?;

    publish_wit(
        &config,
        "test:wit",
        "0.1.0",
        r#"
package test:wit;

interface foo {
    bar: func();
}
"#,
        true,
    )
    .await?;

    let document = Document::parse(
        r#"
package test:composition;

import x: test:wit/foo;
import y: interface {
    bar: func();
};

let i1 = new test:comp { x };
let i2 = new test:comp { "test:wit/foo": y };

export i1.foo;
export i2.foo as "bar";

"#,
    )?;

    let resolver = RegistryPackageResolver::new_with_config(None, &config, None)?;
    let packages = resolver.resolve(&packages(&document)?).await?;

    let composition = Composition::from_ast(&document, packages)?;
    let bytes = composition.encode(EncodingOptions::default())?;

    assert_eq!(
        wasmprinter::print_bytes(bytes)?,
        r#"(component
  (type (;0;)
    (instance
      (type (;0;) (func))
      (export (;0;) "bar" (func (type 0)))
    )
  )
  (import "test:wit/foo" (instance (;0;) (type 0)))
  (type (;1;)
    (instance
      (type (;0;) (func))
      (export (;0;) "bar" (func (type 0)))
    )
  )
  (import "y" (instance (;1;) (type 1)))
  (type (;2;)
    (component
      (type (;0;)
        (instance
          (type (;0;) (func))
          (export (;0;) "bar" (func (type 0)))
        )
      )
      (import "test:wit/foo" (instance (;0;) (type 0)))
      (export (;1;) "test:wit/foo" (instance (type 0)))
    )
  )
  (import "unlocked-dep=<test:comp>" (component (;0;) (type 2)))
  (instance (;2;) (instantiate 0
      (with "test:wit/foo" (instance 0))
    )
  )
  (instance (;3;) (instantiate 0
      (with "test:wit/foo" (instance 1))
    )
  )
  (alias export 2 "test:wit/foo" (instance (;4;)))
  (alias export 3 "test:wit/foo" (instance (;5;)))
  (export (;6;) "test:wit/foo" (instance 4))
  (export (;7;) "bar" (instance 5))
  (@producers
    (processed-by "wac-parser" "0.1.0")
  )
)
"#
    );

    Ok(())
}
