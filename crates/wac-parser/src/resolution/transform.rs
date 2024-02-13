use crate::resolution::Error;
use anyhow::{anyhow, bail, ensure, Result};
use miette::SourceSpan;
use wasm_wave::{untyped::UntypedValue, wasm::WasmValue};
use wasmtime::{
    component::{Component, Linker, Type, Val},
    Config, Engine, Store,
};
use wasmtime_wasi::preview2::{self, ResourceTable, WasiCtx, WasiCtxBuilder, WasiView};

const TRANSFORM_FUNC_NAME: &str = "transform";

/// Transforms a component using the provided transformer and configuration value.
pub fn transform(
    transformer_span: SourceSpan,
    transformer_bytes: &[u8],
    _component_span: SourceSpan,
    component_bytes: &[u8],
    untyped_value: &UntypedValue,
) -> Result<Vec<u8>> {
    let engine =
        Engine::new(Config::new().wasm_component_model(true)).expect("could not configure engine"); // TODO: handle error
    let transformer = Component::from_binary(&engine, transformer_bytes)
        .expect("parsing transformer component bytes"); // TODO: handle error

    let mut linker: Linker<Data> = Linker::new(&engine);
    preview2::command::sync::add_to_linker(&mut linker)?;

    let table = Default::default();
    let ctx = WasiCtxBuilder::new().build();
    let data = Data { ctx, table };
    let mut store = Store::new(&engine, data);

    let instance = linker
        .instantiate(&mut store, &transformer)
        .expect("instantiating transformer"); // TODO: handle error

    let transform_func = instance
        .exports(&mut store)
        .root()
        .func(TRANSFORM_FUNC_NAME)
        .ok_or_else(|| Error::MissingTransformExport {
            span: transformer_span,
        })?;

    let params_ty = transform_func.params(&mut store);
    let result_ty = transform_func.results(&mut store);

    // Ensure params_ty have 2 arguments
    // First argument is list<u8>

    // Check result signature
    ensure!(
        result_ty.len() == 1,
        "result type has incorrect number of arguments"
    );

    let Type::Result(result_ty) = &result_ty[0] else {
        bail!("transform result has incorrect type");
    };

    ensure!(
        matches!(result_ty.err(), Some(Type::String)),
        "result type error has incorrect type"
    );
    let Some(Type::List(ok_ty)) = result_ty.ok() else {
        bail!("transform result has wrong type")
    };
    ensure!(
        matches!(ok_ty.ty(), Type::U8),
        "result type ok has incorrect type"
    );

    let arg0 = params_ty[0].unwrap_list().new_val(
        component_bytes
            .into_iter()
            .map(|b| Val::U8(*b))
            .collect::<Vec<_>>()
            .into_boxed_slice(),
    )?;

    let arg1 = untyped_value
        .to_wasm_value::<Val>(&params_ty[1])
        .map_err(|err| anyhow!("{err}"))?;

    let mut result_vals = vec![Val::U32(0xfefefefe)];

    transform_func.call(&mut store, &[arg0, arg1], &mut result_vals)?;

    // check result_vals is len 1 and type is result<list<u8>> and return list<u8>

    let result_val = result_vals[0].unwrap_result();

    match result_val {
        Ok(ok_val) => Ok(ok_val
            .unwrap()
            .unwrap_list()
            .map(|val| val.unwrap_u8())
            .collect::<Vec<_>>()),
        Err(err_val) => {
            let err = err_val.as_ref().unwrap().unwrap_string();
            bail!("failed to transform: {err}");
        }
    }
}

struct Data {
    ctx: WasiCtx,
    table: ResourceTable,
}

impl WasiView for Data {
    fn table(&self) -> &ResourceTable {
        &self.table
    }

    fn table_mut(&mut self) -> &mut ResourceTable {
        &mut self.table
    }

    fn ctx(&self) -> &WasiCtx {
        &self.ctx
    }

    fn ctx_mut(&mut self) -> &mut WasiCtx {
        &mut self.ctx
    }
}
