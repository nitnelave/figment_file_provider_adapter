# Figment File Provider Adapter &thinsp; [![ci.svg]][ci] [![crates.io]][crate] [![docs.rs]][docs]

[crates.io]: https://img.shields.io/crates/v/figment_file_provider_adapter.svg
[crate]: https://crates.io/crates/figment_file_provider_adapter
[docs.rs]: https://docs.rs/figment_file_provider_adapter/badge.svg
[docs]: https://docs.rs/figment_file_provider_adapter
[ci.svg]: https://github.com/nitnelave/figment_file_provider_adapter/workflows/CI/badge.svg
[ci]: https://github.com/nitnelave/figment_file_provider_adapter/actions

[Figment](https://docs.rs/figment/latest/figment/) provider for optionally file-based config values, working with any provider.

```rust
use serde::Deserialize;
use figment::{Figment, providers::{Env, Format, Toml}};
use figment_file_provider_adapter::FileAdapter;

#[derive(Deserialize)]
struct Config {
  frobnicate: String,
  foo: u64,
}

let config: Config = Figment::new()
    .merge(FileAdapter::wrap(Env::prefixed("APP_")))
    .merge(FileAdapter::wrap(Toml::file("config.toml")))
    .extract()?;
```

# Overview

This crate contains the `FileAdapter` provider for `Figment`, to allow loading
configuration values from either direct values or files. It wraps around an existing provider,
and for every key that ends in "_FILE" it replaces the value with reading the file mentioned.
This is especially useful for secret management in combination with containers.

For instance, to pass an API key to the configuration, you could use either the config value `API_KEY=abc123deadbeef`, or you could write that API key to a file
`/secrets/api_key` and pass the config value `API_KEY_FILE=/secrets/api_key`.

See the [documentation][docs] for a detailed usage guide and
more information.

# Usage

Add the following to your `Cargo.toml`:

```toml
[dependencies]
figment = { version = "0.10" }
figment_file_provider_adapter = { version = "0.1" }
```

## License

figment_file_provider_adapter is licensed under either of the MIT License ([LICENSE-MIT](LICENSE-MIT)
or http://opensource.org/licenses/MIT).
