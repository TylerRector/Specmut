//! Configuration file (`specmut.toml`) loader.  See §7.3.

use std::path::Path;

use serde::Deserialize;
use thiserror::Error;

/// Top-level configuration loaded from a TOML file.
#[derive(Debug, Deserialize)]
pub struct Config {
    /// Project section.
    pub project: ProjectConfig,
    /// Pipeline parameters.
    #[serde(default)]
    pub parameters: ParameterConfig,
    /// Output settings.
    #[serde(default)]
    pub output: OutputConfig,
}

/// `[project]` section.
#[derive(Debug, Deserialize)]
pub struct ProjectConfig {
    /// Display name.  Reserved for richer report headers.
    #[allow(dead_code)]
    pub name: String,
    /// Path to the input spec file.
    pub spec_file: String,
    /// Implementation model files.
    #[serde(default)]
    pub implementations: Vec<String>,
}

/// `[parameters]` section.
#[derive(Debug, Deserialize, Clone)]
pub struct ParameterConfig {
    /// Maximum domain size.
    #[serde(default = "default_model_bound")]
    pub model_bound: usize,
    /// Maximum quantifier rank.
    #[serde(default = "default_quantifier_rank")]
    pub quantifier_rank: usize,
    /// Neighborhood radius.
    #[serde(default = "default_epsilon")]
    pub epsilon: f64,
    /// Random seed.
    #[serde(default = "default_seed")]
    pub seed: u64,
}

impl Default for ParameterConfig {
    fn default() -> Self {
        Self {
            model_bound: default_model_bound(),
            quantifier_rank: default_quantifier_rank(),
            epsilon: default_epsilon(),
            seed: default_seed(),
        }
    }
}

/// `[output]` section.
#[derive(Debug, Deserialize, Clone)]
pub struct OutputConfig {
    /// `"text"` or `"json"`.
    #[serde(default = "default_format")]
    pub report_format: String,
    /// Directory for additional report artifacts (unused in Phase 5).
    #[allow(dead_code)]
    #[serde(default)]
    pub output_dir: Option<String>,
}

impl Default for OutputConfig {
    fn default() -> Self {
        Self {
            report_format: default_format(),
            output_dir: None,
        }
    }
}

fn default_model_bound() -> usize {
    2
}
fn default_quantifier_rank() -> usize {
    2
}
fn default_epsilon() -> f64 {
    0.15
}
fn default_seed() -> u64 {
    42
}
fn default_format() -> String {
    "text".into()
}

/// Errors raised while loading the configuration.
#[derive(Debug, Error)]
pub enum ConfigError {
    /// File I/O error.
    #[error("could not read config file '{path}': {source}")]
    Io {
        /// Path that failed to open.
        path: String,
        /// Underlying error.
        #[source]
        source: std::io::Error,
    },
    /// TOML decode error.
    #[error("could not parse config file '{path}': {source}")]
    Toml {
        /// Path that failed to parse.
        path: String,
        /// Underlying error.
        #[source]
        source: toml::de::Error,
    },
}

impl Config {
    /// Load a `Config` from the given path.
    pub fn load(path: &Path) -> Result<Self, ConfigError> {
        let text = std::fs::read_to_string(path).map_err(|e| ConfigError::Io {
            path: path.display().to_string(),
            source: e,
        })?;
        toml::from_str(&text).map_err(|e| ConfigError::Toml {
            path: path.display().to_string(),
            source: e,
        })
    }
}
