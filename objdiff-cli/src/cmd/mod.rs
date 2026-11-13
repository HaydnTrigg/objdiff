pub mod diff;
pub mod mcp;
pub mod report;

use anyhow::{Context, Result};
use objdiff_core::diff::DiffObjConfig;

pub fn apply_config_args(diff_config: &mut DiffObjConfig, args: &[String]) -> Result<()> {
    for config in args {
        let (key, value) = config.split_once('=').context("--config expects \"key=value\"")?;
        diff_config.set_option_str(key, value)?;
    }
    Ok(())
}
