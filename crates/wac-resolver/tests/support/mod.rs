use anyhow::{Context, Result};
use std::{path::Path, time::Duration};
use tokio::task::JoinHandle;
use tokio_util::sync::CancellationToken;
use warg_client::{
    storage::{ContentStorage, PublishEntry, PublishInfo},
    FileSystemClient,
};
use warg_crypto::signing::PrivateKey;
use warg_protocol::{operator::NamespaceState, registry::PackageName};
use warg_server::{policy::content::WasmContentPolicy, Config, Server};
use wit_parser::{Resolve, UnresolvedPackage};

pub fn test_operator_key() -> &'static str {
    "ecdsa-p256:I+UlDo0HxyBBFeelhPPWmD+LnklOpqZDkrFP5VduASk="
}

pub fn test_signing_key() -> &'static str {
    "ecdsa-p256:2CV1EpLaSYEn4In4OAEDAj5O4Hzu8AFAxgHXuG310Ew="
}

pub async fn publish_component(
    config: &warg_client::Config,
    name: &str,
    version: &str,
    wat: &str,
    init: bool,
) -> Result<()> {
    publish(
        config,
        &name.parse()?,
        version,
        wat::parse_str(wat).context("failed to parse component for publishing")?,
        init,
    )
    .await
}

pub async fn publish_wit(
    config: &warg_client::Config,
    name: &str,
    version: &str,
    wit: &str,
    init: bool,
) -> Result<()> {
    let mut resolve = Resolve::new();
    let pkg = resolve
        .push(
            UnresolvedPackage::parse(Path::new("foo.wit"), wit)
                .context("failed to parse wit for publishing")?,
        )
        .context("failed to resolve wit for publishing")?;

    let bytes = wit_component::encode(Some(true), &resolve, pkg)
        .context("failed to encode wit for publishing")?;

    publish(config, &name.parse()?, version, bytes, init).await
}

pub async fn publish(
    config: &warg_client::Config,
    name: &PackageName,
    version: &str,
    content: Vec<u8>,
    init: bool,
) -> Result<()> {
    let client = FileSystemClient::new_with_config(None, config, None)?;

    let digest = client
        .content()
        .store_content(
            Box::pin(futures::stream::once(async move { Ok(content.into()) })),
            None,
        )
        .await
        .context("failed to store component for publishing")?;

    let mut entries = Vec::with_capacity(2);
    if init {
        entries.push(PublishEntry::Init);
    }
    entries.push(PublishEntry::Release {
        version: version.parse().unwrap(),
        content: digest,
    });

    let record_id = client
        .publish_with_info(
            &PrivateKey::decode(test_signing_key().to_string()).unwrap(),
            PublishInfo {
                name: name.clone(),
                head: None,
                entries,
            },
        )
        .await
        .context("failed to publish component")?;

    client
        .wait_for_publish(name, &record_id, Duration::from_secs(1))
        .await?;

    Ok(())
}

pub struct ServerInstance {
    task: Option<JoinHandle<()>>,
    shutdown: CancellationToken,
}

impl Drop for ServerInstance {
    fn drop(&mut self) {
        futures::executor::block_on(async move {
            self.shutdown.cancel();
            self.task.take().unwrap().await.ok();
        });
    }
}

/// Spawns a server as a background task.
pub async fn spawn_server(root: &Path) -> Result<(ServerInstance, warg_client::Config)> {
    let shutdown = CancellationToken::new();
    let config = Config::new(
        PrivateKey::decode(test_operator_key().to_string())?,
        Some(vec![("test".to_string(), NamespaceState::Defined)]),
        root.join("server"),
    )
    .with_addr(([127, 0, 0, 1], 0))
    .with_shutdown(shutdown.clone().cancelled_owned())
    .with_checkpoint_interval(Duration::from_millis(100))
    .with_content_policy(WasmContentPolicy::default());

    let server = Server::new(config).initialize().await?;
    let addr = server.local_addr()?;

    let task = tokio::spawn(async move {
        server.serve().await.unwrap();
    });

    let instance = ServerInstance {
        task: Some(task),
        shutdown,
    };

    let config = warg_client::Config {
        home_url: Some(format!("http://{addr}")),
        registries_dir: Some(root.join("registries")),
        content_dir: Some(root.join("content")),
        namespace_map_path: Some(root.join("namespaces")),
        keyring_auth: false,
        keys: Default::default(),
        ignore_federation_hints: false,
        auto_accept_federation_hints: false,
    };

    Ok((instance, config))
}
