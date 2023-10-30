#![deny(missing_docs)]
#![forbid(unsafe_code)]

//! Figment [`figment::Provider`] for optionally file-based env config values.
//!
//! ```rust
//! use serde::Deserialize;
//! use figment::{Figment, providers::{Env, Format, Toml}};
//! use figment_file_provider_adapter::FileAdapter;
//!
//! #[derive(Deserialize)]
//! struct Config {
//!   frobnicate: String,
//!   foo: u64,
//! }
//!
//! # figment::Jail::expect_with(|jail| {
//! # jail.create_file("secret_file", "32")?;
//! # jail.set_env("APP_FROBNICATE", "with gusto");
//! # jail.set_env("APP_FOO_FILE", "secret_file");
//! # jail.create_file("config.toml", "")?;
//! let config: Config = Figment::new()
//!     .merge(FileAdapter::wrap(Env::prefixed("APP_")))
//!     .merge(FileAdapter::wrap(Toml::file("config.toml")))
//!     .extract()?;
//! # Ok(())
//! # });
//! ```
//!
//! # Overview
//!
//! This crate contains the [`FileAdapter`] provider for [`figment`], to allow loading
//! configuration values from either environment variables or files. This is especially useful
//! for secret management in combination with containers.
//!
//! For instance, to pass an API key to the configuration, you could use either the config
//! value `API_KEY=abc123deadbeef`, or you could write that API key to a file
//! `/secrets/api_key` and pass the config value `API_KEY_FILE=/secrets/api_key`.
//!
//! Note that if both are specified, the non-`_FILE` one wins.
//!
//! # Recommendations
//!
//! ## Environment variables namespacing
//!
//! The provider will try to read any config value with a key that ends with `_FILE` (or the
//! custom suffix) and will error if the file cannot be read. As such, for environment variables,
//! it is usually necessary to have a namespace in the form of a unique prefix, to avoid conficts
//! or unexpected interactions: `FileAdapter::wrap(Env::prefixed("MY_APP_"))`
//! (see [`figment::providers::Env::prefixed`]).
//!
//! Since it is built on top of [`figment::providers::Env`], you can set it up so that only some
//! variables accept the `_FILE` variant and the rest are read normally with [`FileAdapter::only`]:
//!
//! ```rust
//! # use serde::Deserialize;
//! # use figment::{Figment, providers::Env};
//! # use figment_file_provider_adapter::FileAdapter;
//! #
//! # #[derive(Deserialize)]
//! # struct Config {
//! #   frobnicate: String,
//! #   foo: u64,
//! # }
//! #
//! # figment::Jail::expect_with(|jail| {
//! # jail.create_file("secret_file", "32")?;
//! # jail.set_env("APP_FROBNICATE", "with gusto");
//! # jail.set_env("APP_FOO_FILE", "secret_file");
//! let file_keys = ["foo", "bar"];
//! let env = Env::prefixed("APP_");
//! // Call `.only` on the FileAdapter, not the Env.
//! let config: Config = Figment::new()
//!     .merge(FileAdapter::wrap(env.clone()).only(&file_keys))
//!     .merge(env.ignore(&file_keys))
//!     .extract()?;
//! # Ok(())
//! # });
//! ```
//!
//! Similarly for other providers, you can usually merge with and without the wrapper to restrict
//! the wrapper to some keys only:
//!
//! ```rust
//! # use serde::Deserialize;
//! # use figment::{Figment, providers::{Format, Toml}};
//! # use figment_file_provider_adapter::FileAdapter;
//! #
//! # #[derive(Deserialize)]
//! # struct Config {
//! #   frobnicate: String,
//! #   foo: u64,
//! # }
//! #
//! # figment::Jail::expect_with(|jail| {
//! # jail.create_file("secret_file", "32")?;
//! # jail.create_file("config.toml", r#"frobnicate = "with gusto"
//! #                                    foo_file = "secret_file""#)?;
//! let file_keys = ["foo", "bar"];
//! let config: Config = Figment::new()
//!     .merge(FileAdapter::wrap(Toml::file("config.toml")).only(&file_keys))
//!     .merge(Toml::file("config.toml"))
//!     .extract()?;
//! # Ok(())
//! # });
//! ```
//!
//! ## Changing the suffix
//!
//! You can also specify the suffix to use. For instance, to use "_PATH" instead of "_FILE":
//!
//! ```rust
//! # use serde::Deserialize;
//! # use figment::{Figment, providers::Env};
//! # use figment_file_provider_adapter::FileAdapter;
//! #
//! # #[derive(Deserialize)]
//! # struct Config {
//! #   frobnicate: String,
//! #   foo: u64,
//! # }
//! #
//! # figment::Jail::expect_with(|jail| {
//! # jail.create_file("secret_file", "32")?;
//! # jail.set_env("APP_FROBNICATE", "with gusto");
//! # jail.set_env("APP_FOO_PATH", "secret_file");
//! let config: Config = Figment::new()
//!     .merge(FileAdapter::wrap(Env::prefixed("APP_")).with_suffix("_PATH"))
//!     .extract()?;
//! # Ok(())
//! # });
//! ```

use figment::{
    error::{Kind, Result},
    value::{Dict, Map, Tag, Value},
    Profile, Provider,
};
use std::{
    collections::HashSet,
    path::{Path, PathBuf},
};

/// Provider that reads config values from a given provider, and reads the values from the
/// pointed file for each key that ends in "_FILE".
///
/// The config value `foo` will be read either from the config value `FOO` if present or from the
/// file pointed to by `FOO_FILE`.
///
/// ```rust
/// # use serde::Deserialize;
/// # use figment::{Figment, providers::Env};
/// # use figment_file_provider_adapter::FileAdapter;
/// #
/// #[derive(Deserialize)]
/// struct Config {
///   foo: String,
///   bar: String,
/// }
///
/// # figment::Jail::expect_with(|jail| {
/// # jail.create_file("secret_file", "bar_value")?;
/// # jail.set_env("APP_FOO", "foo_value");
/// # jail.set_env("APP_BAR_FILE", "secret_file");
/// // ENV:
/// // - `APP_FOO=foo_value`
/// // - `APP_BAR_FILE=./secret_file`
/// //
/// // Contents of the file `./secret_file`: `bar_value`
/// let config: Config = Figment::new()
///     .merge(FileAdapter::wrap(Env::prefixed("APP_")))
///     .extract()?;
/// assert_eq!(config.foo, "foo_value");
/// assert_eq!(config.bar, "bar_value");
/// # Ok(())
/// # });
/// ```
pub struct FileAdapter {
    provider: Box<dyn Provider>,
    suffix: String,
    relative_dir: PathBuf,
}

/// A [`FileAdapter`] whose suffix cannot be changed.
pub struct FileAdapterWithRestrictions {
    file_adapter: FileAdapter,
    include_keys: Option<HashSet<String>>,
    exclude_keys: Option<HashSet<String>>,
}

impl FileAdapter {
    /// Build from a [`figment::Provider`].
    ///
    /// Note that for environment variables, [`figment::providers::Env::only`] and
    /// [`figment::providers::Env::ignore`] should not be used. Use [`FileAdapter::only`] and
    /// [`FileAdapter::ignore`] instead.
    ///
    /// ```rust
    /// use figment::providers::Env;
    /// use figment_file_provider_adapter::FileAdapter;
    /// let file_adapter = FileAdapter::wrap(Env::prefixed("MY_APP_"));
    /// ```
    pub fn wrap<T: Provider + 'static>(provider: T) -> Self {
        Self {
            provider: Box::new(provider),
            suffix: "_file".to_string(),
            relative_dir: PathBuf::new(),
        }
    }

    /// Change the suffix used to detect config keys that point to files ("_FILE" by
    /// default).
    ///
    /// ```rust
    /// # use serde::Deserialize;
    /// # use figment::{Figment, providers::Env};
    /// # use figment_file_provider_adapter::FileAdapter;
    /// #
    /// # #[derive(Deserialize)]
    /// # struct Config {
    /// #   foo: u64,
    /// # }
    /// #
    /// # figment::Jail::expect_with(|jail| {
    /// # jail.create_file("secret_file", "32")?;
    /// # jail.set_env("APP_FOO_PATH", "secret_file");
    /// // ENV: `APP_FOO_PATH=./secret_file`
    /// // Contents of `./secret_file`: `32`
    /// let config: Config = Figment::new()
    ///     .merge(FileAdapter::wrap(Env::prefixed("APP_")).with_suffix("_PATH"))
    ///     .extract()?;
    /// assert_eq!(config.foo, 32);
    /// # Ok(())
    /// # });
    /// ```
    ///
    /// Note that the suffix cannot be changed after calling [`FileAdapter::only`] or
    /// [`FileAdapter::ignore`].
    pub fn with_suffix(self, suffix: &str) -> Self {
        Self {
            suffix: suffix.to_lowercase(),
            ..self
        }
    }

    /// Provide a relative dir to be applied to the paths when finding files from which to read values
    ///
    /// ```rust
    /// use figment::providers::Env;
    /// use figment_file_provider_adapter::FileAdapter;
    /// // This provider will only at the variables prefixed with MY_APP_ and attempt to resolve them in the directory "foo".
    /// let file_adapter = FileAdapter::wrap(Env::prefixed("MY_APP_")).relative_dir("foo");
    /// ```
    pub fn relative_dir<P: AsRef<Path>>(self, path: P) -> Self {
        let mut relative_dir = self.relative_dir.clone();
        relative_dir.push(path);
        Self {
            relative_dir,
            ..self
        }
    }

    /// Restrict the provider to process only the given list of keys (and their "_FILE"
    /// counterparts).
    ///
    /// IMPORTANT: For environment variables, this should be used instead of
    /// [`figment::providers::Env::only`] otherwise the "_FILE" variants won't be supported.
    ///
    /// ```rust
    /// use figment::providers::Env;
    /// use figment_file_provider_adapter::FileAdapter;
    /// // This provider will only look at the variables FOO, FOO_FILE, BAR and BAR_FILE.
    /// let file_adapter = FileAdapter::wrap(Env::prefixed("MY_APP_")).only(&["foo", "bar"]);
    /// ```
    pub fn only(self, keys: &[&str]) -> FileAdapterWithRestrictions {
        FileAdapterWithRestrictions::new(self).only(keys)
    }

    /// Restrict the provider to ignore the given list of keys (and their "_FILE"
    /// counterparts).
    ///
    /// IMPORTANT: For environment variables, this should be used instead of
    /// [`figment::providers::Env::ignore`] otherwise the "_FILE" variants won't be ignored.
    ///
    /// ```rust
    /// use figment::providers::Env;
    /// use figment_file_provider_adapter::FileAdapter;
    /// // This provider will not look at the variables FOO, FOO_FILE, BAR and BAR_FILE.
    /// let file_adapter = FileAdapter::wrap(Env::prefixed("MY_APP_")).ignore(&["foo", "bar"]);
    /// ```
    pub fn ignore(self, keys: &[&str]) -> FileAdapterWithRestrictions {
        FileAdapterWithRestrictions::new(self).ignore(keys)
    }
}

impl FileAdapterWithRestrictions {
    pub(crate) fn new(file_adapter: FileAdapter) -> Self {
        Self {
            file_adapter,
            include_keys: None,
            exclude_keys: None,
        }
    }

    /// See [`FileAdapter::only`].
    pub fn only(mut self, keys: &[&str]) -> Self {
        let mut include_keys = self.include_keys.take().unwrap_or_default();
        include_keys.extend(
            keys.iter().map(|s| s.to_string()).chain(
                keys.iter()
                    .map(|s| s.to_string() + &self.file_adapter.suffix),
            ),
        );
        FileAdapterWithRestrictions {
            include_keys: Some(include_keys),
            ..self
        }
    }

    /// See [`FileAdapter::ignore`].
    pub fn ignore(mut self, keys: &[&str]) -> Self {
        let mut exclude_keys = self.exclude_keys.take().unwrap_or_default();
        exclude_keys.extend(
            keys.iter().map(|s| s.to_string()).chain(
                keys.iter()
                    .map(|s| s.to_string() + &self.file_adapter.suffix),
            ),
        );
        FileAdapterWithRestrictions {
            exclude_keys: Some(exclude_keys),
            ..self
        }
    }
}

impl Provider for FileAdapterWithRestrictions {
    fn metadata(&self) -> figment::Metadata {
        self.file_adapter.metadata()
    }

    fn data(&self) -> Result<Map<Profile, Dict>> {
        self.file_adapter
            .provider
            .data()?
            .into_iter()
            .map(|(profile, dict)| {
                Ok((
                    profile,
                    process_dict(
                        &self.file_adapter.relative_dir,
                        dict,
                        &self.file_adapter.suffix,
                        &self.include_keys,
                        &self.exclude_keys,
                    )?,
                ))
            })
            .collect()
    }
}

impl Provider for FileAdapter {
    fn metadata(&self) -> figment::Metadata {
        self.provider.metadata()
    }

    fn data(&self) -> Result<Map<Profile, Dict>> {
        self.provider
            .data()?
            .into_iter()
            .map(|(profile, dict)| {
                Ok((
                    profile,
                    process_dict(&self.relative_dir, dict, &self.suffix, &None, &None)?,
                ))
            })
            .collect()
    }
}

fn process_string(
    relative_dir: &PathBuf,
    key: String,
    value: String,
    tag: Tag,
    suffix: &str,
    include_keys: &Option<HashSet<String>>,
    exclude_keys: &Option<HashSet<String>>,
    all_keys: &HashSet<String>,
) -> Result<Option<(String, Value)>> {
    let mut skip = false;
    if let Some(set) = include_keys {
        if !set.contains(&key) {
            skip = true;
        }
    }
    if let Some(set) = exclude_keys {
        if set.contains(&key) {
            skip = true;
        }
    }
    if !skip {
        if let Some(stripped_key) = key.as_str().strip_suffix(suffix) {
            if all_keys.contains(stripped_key) {
                return Ok(None);
            }
            let mut target_file = relative_dir.clone();
            target_file.push(&value);
            let contents = std::fs::read_to_string(target_file).map_err(|e| {
                Kind::Message(format!(
                    "Could not open `{}` from config value `{}`: {:#}",
                    &value, &key, e
                ))
            })?;
            return Ok(Some((
                stripped_key.to_string(),
                contents.parse().expect("infallible"),
            )));
        }
    }
    Ok(Some((key, Value::String(tag, value))))
}

fn process_dict(
    relative_dir: &PathBuf,
    provider_dict: Dict,
    suffix: &str,
    include_keys: &Option<HashSet<String>>,
    exclude_keys: &Option<HashSet<String>>,
) -> Result<Dict> {
    let keys = provider_dict
        .keys()
        .map(String::clone)
        .collect::<HashSet<_>>();
    let process_key_value = |(key, value): (String, Value)| {
        Ok(match value {
            Value::String(tag, v) => process_string(
                relative_dir,
                key,
                v,
                tag,
                suffix,
                include_keys,
                exclude_keys,
                &keys,
            )?,
            figment::value::Value::Dict(tag, d) => Some((
                key,
                Value::Dict(
                    tag,
                    process_dict(relative_dir, d, suffix, include_keys, exclude_keys)?,
                ),
            )),
            v => Some((key, v)),
        })
    };
    provider_dict
        .into_iter()
        .filter_map(|kv| process_key_value(kv).transpose())
        .collect()
}

#[cfg(test)]
mod tests {
    use super::*;
    use figment::providers::{Env, Format, Toml};

    #[derive(serde::Deserialize)]
    struct Config {
        foo: String,
    }

    #[derive(serde::Deserialize)]
    struct IntConfig {
        foo: i32,
    }

    #[test]
    fn basic_data() {
        figment::Jail::expect_with(|_| {
            let config = figment::Figment::new()
                .merge(FileAdapter::wrap(Toml::string(
                    r#"foo = "bar"
                       baz = "qux""#,
                )))
                .extract::<Config>()?;

            assert_eq!(config.foo, "bar");
            Ok(())
        });
    }

    #[test]
    fn basic_data_file() {
        figment::Jail::expect_with(|jail| {
            jail.create_file("secret", "bar")?;

            let config = figment::Figment::new()
                .merge(FileAdapter::wrap(Toml::string(
                    r#"foo_file = "secret"
                       baz = "qux""#,
                )))
                .extract::<Config>()?;

            assert_eq!(config.foo, "bar");
            Ok(())
        });
    }

    #[test]
    fn basic_env() {
        figment::Jail::expect_with(|jail| {
            jail.set_env("FIGMENT_TEST_FOO", "bar");
            jail.set_env("FIGMENT_TEST_BAZ", "put");

            let config = figment::Figment::new()
                .merge(FileAdapter::wrap(Env::prefixed("FIGMENT_TEST_")))
                .extract::<Config>()?;

            assert_eq!(config.foo, "bar");
            Ok(())
        });
    }

    #[test]
    fn basic_env_file() {
        figment::Jail::expect_with(|jail| {
            jail.set_env("FIGMENT_TEST_FOO_FILE", "secret");
            jail.create_file("secret", "bar")?;

            let config = figment::Figment::new()
                .merge(FileAdapter::wrap(Env::prefixed("FIGMENT_TEST_")))
                .extract::<Config>()?;

            assert_eq!(config.foo, "bar");
            Ok(())
        });
    }

    #[test]
    fn basic_env_file_with_relative_dir() {
        figment::Jail::expect_with(|jail| {
            jail.set_env("FIGMENT_TEST_FOO_FILE", "secret");
            jail.create_directory("subdir")?;
            jail.create_file("subdir/secret", "bar")?;

            let config = figment::Figment::new()
                .merge(FileAdapter::wrap(Env::prefixed("FIGMENT_TEST_")).relative_dir("subdir"))
                .extract::<Config>()?;

            assert_eq!(config.foo, "bar");
            Ok(())
        });
    }

    #[test]
    fn basic_env_file_with_absolute_dir() {
        figment::Jail::expect_with(|jail| {
            jail.set_env("FIGMENT_TEST_FOO_FILE", "secret");
            let abs_dir = jail.create_directory("subdir")?;
            jail.create_file("subdir/secret", "bar")?;

            let config = figment::Figment::new()
                .merge(FileAdapter::wrap(Env::prefixed("FIGMENT_TEST_")).relative_dir(abs_dir))
                .extract::<Config>()?;

            assert_eq!(config.foo, "bar");
            Ok(())
        });
    }
    #[test]
    fn integer() {
        figment::Jail::expect_with(|jail| {
            jail.create_file("secret", "32")?;

            let config = figment::Figment::new()
                .merge(FileAdapter::wrap(Toml::string(
                    r#"foo_file = "secret"
                       baz = "qux""#,
                )))
                .extract::<IntConfig>()?;

            assert_eq!(config.foo, 32);
            Ok(())
        });
    }

    #[test]
    fn basic_both() {
        figment::Jail::expect_with(|jail| {
            jail.set_env("FIGMENT_TEST_FOO_FILE", "secret");
            jail.set_env("FIGMENT_TEST_FOO", "env");
            jail.create_file("secret", "file")?;

            let config = figment::Figment::new()
                .merge(FileAdapter::wrap(Env::prefixed("FIGMENT_TEST_")))
                .extract::<Config>()?;

            assert_eq!(config.foo, "env");
            Ok(())
        });
    }

    #[test]
    fn with_suffix() {
        figment::Jail::expect_with(|jail| {
            jail.set_env("FIGMENT_TEST_FOO_path", "secret");
            jail.create_file("secret", "bar")?;

            let config = figment::Figment::new()
                .merge(FileAdapter::wrap(Env::prefixed("FIGMENT_TEST_")).with_suffix("_PATH"))
                .extract::<Config>()?;

            assert_eq!(config.foo, "bar");
            Ok(())
        });
    }

    #[test]
    fn missing_file() {
        figment::Jail::expect_with(|jail| {
            jail.set_env("FIGMENT_TEST_BAR_FILE", "secret");
            jail.set_env("FIGMENT_TEST_FOO", "bar");

            let config = figment::Figment::new()
                .merge(FileAdapter::wrap(Env::prefixed("FIGMENT_TEST_")))
                .extract::<Config>();

            assert!(config.is_err());
            Ok(())
        });
    }

    #[test]
    fn only() {
        figment::Jail::expect_with(|jail| {
            jail.set_env("FIGMENT_TEST_BAR_FILE", "secret");
            jail.set_env("FIGMENT_TEST_FOO", "bar");

            let config = figment::Figment::new()
                .merge(FileAdapter::wrap(Env::prefixed("FIGMENT_TEST_")).only(&["foo"]))
                .extract::<Config>()?;

            assert_eq!(config.foo, "bar");
            Ok(())
        });
    }

    #[test]
    fn ignore() {
        figment::Jail::expect_with(|jail| {
            jail.set_env("FIGMENT_TEST_BAR_FILE", "secret");
            jail.set_env("FIGMENT_TEST_FOO", "bar");

            let config = figment::Figment::new()
                .merge(FileAdapter::wrap(Env::prefixed("FIGMENT_TEST_")).ignore(&["bar"]))
                .extract::<Config>()?;

            assert_eq!(config.foo, "bar");
            Ok(())
        });
    }

    #[test]
    fn only_ignore() {
        figment::Jail::expect_with(|jail| {
            jail.set_env("FIGMENT_TEST_BAR_FILE", "secret");
            jail.set_env("FIGMENT_TEST_BAZ_FILE", "secret");
            jail.set_env("FIGMENT_TEST_FOO", "bar");

            let config = figment::Figment::new()
                .merge(
                    FileAdapter::wrap(Env::prefixed("FIGMENT_TEST_"))
                        .ignore(&["bar"])
                        .only(&["foo"]),
                )
                .extract::<Config>()?;

            assert_eq!(config.foo, "bar");
            Ok(())
        });
    }
}
