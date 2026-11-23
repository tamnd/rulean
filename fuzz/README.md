# rulean-fuzz

The byte fuzz targets of spec 11.5.1. Each target gives an input to one reader of hostile input. The reader must give a result or an error, and never a panic, a hang or a large allocation.

| Target | Reader | Input |
|---|---|---|
| `olean` | `rulean_olean::decode_parts` | the parts of one module, in the layout of `src/lib.rs` |
| `ndjson` | `rulean_format::parse_export` | an NDJSON export |
| `rlb` | `rulean_format::rlb::decode` | a `.rlb` file |

libFuzzer is C++. So this package is a workspace of its own, and it is not in the dependency graph of rulean. The no-C check of `cargo xtask nonc` and `deny.toml` do not apply to it. The shipped build does not use it.

## Run

You need a nightly toolchain and `cargo install cargo-fuzz`.

```sh
cd fuzz
cargo +nightly run --release --bin seeds -- corpus/olean
cargo +nightly fuzz run olean corpus/olean -- -max_total_time=600 -rss_limit_mb=2048 -timeout=10
```

`seeds` writes the module `Init.Control.Do` of the fixtures of `rulean-olean` as seed inputs. For `ndjson`, small exports are good seeds, for example the `tutorial` tests of the Lean Kernel Arena. For `rlb`, pack these exports with `rulean pack`. The workflow `.github/workflows/fuzz.yml` makes the seeds in this way. Each week, it runs 2 shards of each target for 4 hours with 4 workers, about 96 CPU-hours in total, and it keeps the corpus of each shard in the Actions cache.

A crash goes to `artifacts/TARGET/`. Each find becomes a regression test in the crate of the reader (spec 11.5.1).
