//! Shared, long-lived server state.
//!
//! The server is meant to run persistently ("prompt as you go"), so state is
//! shared across every stdio session and HTTP connection via an `Arc`.

use std::{collections::BTreeMap, path::PathBuf, sync::Mutex};

use anyhow::{Result, anyhow};
use objdiff_core::{
    build::BuildConfig,
    diff::{DiffObjConfig, MappingConfig},
};
use typed_path::Utf8UnixPathBuf;

use super::project::{LoadedProject, resolve_inputs};

#[derive(Default)]
pub struct AppState {
    inner: Mutex<Inner>,
}

#[derive(Default)]
struct Inner {
    /// Baseline diff config; project/unit options and per-call overrides layer on top.
    config: DiffObjConfig,
    /// Currently loaded project, if any.
    project: Option<LoadedProject>,
}

/// Everything needed to run one diff, resolved off-lock.
pub struct DiffInputs {
    pub target: PathBuf,
    pub base: PathBuf,
    pub config: DiffObjConfig,
    /// Manual symbol mappings and symbol addresses from the project / unit config.
    pub mapping_config: MappingConfig,
}

impl AppState {
    pub fn new() -> Self { Self::default() }

    /// Apply a single config override onto the persistent baseline config.
    pub fn set_config(&self, key: &str, value: &str) -> Result<()> {
        let mut inner = self.inner.lock().unwrap();
        inner.config.set_option_str(key, value)
    }

    pub fn open_project(&self, dir: &str) -> Result<String> {
        let project = LoadedProject::load(dir)?;
        let summary = format!(
            "Loaded {} ({} units)",
            project.info.path.display(),
            project.config.units().len()
        );
        self.inner.lock().unwrap().project = Some(project);
        Ok(summary)
    }

    pub fn list_units(&self, filter: Option<&str>) -> Result<String> {
        let inner = self.inner.lock().unwrap();
        let project = inner.project.as_ref().ok_or_else(no_project)?;
        Ok(project.list_units(filter))
    }

    /// Resolve target/base paths and the final diff config for one diff.
    pub fn prepare_diff(
        &self,
        unit: Option<&str>,
        target: Option<&str>,
        base: Option<&str>,
        overrides: &BTreeMap<String, String>,
    ) -> Result<DiffInputs> {
        let inner = self.inner.lock().unwrap();
        let (target, base) = resolve_inputs(inner.project.as_ref(), unit, target, base)?;
        let mut config = inner.config.clone();
        if let Some(project) = inner.project.as_ref() {
            project.apply_options(unit, &mut config)?;
        }
        let mut mapping_config = MappingConfig::default();
        if let Some(project) = inner.project.as_ref() {
            if let Some(unit) = unit {
                mapping_config.mappings = project.symbol_mappings(unit)?;
            }
            mapping_config.symbol_addresses = project.symbol_addresses(unit)?;
        }
        for (key, value) in overrides {
            config.set_option_str(key, value)?;
        }
        Ok(DiffInputs { target, base, config, mapping_config })
    }

    /// Add/remove/clear a unit's manual symbol mappings and persist them.
    pub fn set_symbol_mapping(
        &self,
        unit: &str,
        target: Option<&str>,
        base: Option<&str>,
    ) -> Result<String> {
        let mut inner = self.inner.lock().unwrap();
        let project = inner.project.as_mut().ok_or_else(no_project)?;
        project.set_symbol_mapping(unit, target, base)
    }

    pub fn list_symbol_mappings(&self, unit: &str) -> Result<String> {
        let inner = self.inner.lock().unwrap();
        let project = inner.project.as_ref().ok_or_else(no_project)?;
        project.list_symbol_mappings(unit)
    }

    /// Prepare a build invocation for a unit (off-lock execution by the caller).
    pub fn build_invocation(
        &self,
        unit: &str,
        target: bool,
    ) -> Result<(BuildConfig, Utf8UnixPathBuf)> {
        let inner = self.inner.lock().unwrap();
        let project = inner.project.as_ref().ok_or_else(no_project)?;
        project.build_invocation(unit, target)
    }
}

fn no_project() -> anyhow::Error { anyhow!("No project loaded; call open_project first") }
