# Derived codecs: measurement prototype

Measurement prototype for `compiler-rust/docs/DERIVED_CODECS.md` (question
Q2, option b). Not production code and not meant to be merged.

- `derived-postpass-dump.patch` applies to pull request #194 at `1898b21000`.
  It adds the bound name and the declared-name tables of each generated
  binding to the census record, and, when `RESCRIPT_DERIVED_POSTPASS=<file>`
  is set, appends one line per top-level binding with its Lambda after the
  passes (`simplify_in_arena`), preceded by one line naming the unit. The dump
  relies on one worker for its ordering.
- `derived_postpass_compare.py` joins the two files and reports, for every
  template with two or more bindings, whether all instances have the same
  Lambda after the passes once declared names, identifier stamps and static
  exit numbers are normalized.

```sh
git apply compiler-rust/docs/prototypes/derived-codecs/derived-postpass-dump.patch
cargo build --manifest-path rewatch/Cargo.toml
export RESCRIPT_RUNTIME="$PWD/packages/@rescript/runtime"
rewatch/target/debug/rescript clean tests/ppx_spice
RAYON_NUM_THREADS=1 RESCRIPT_DERIVED_CENSUS=/tmp/derived.jsonl \
  RESCRIPT_DERIVED_POSTPASS=/tmp/postpass.tsv \
  rewatch/target/debug/rescript build tests/ppx_spice
python3 compiler-rust/docs/prototypes/derived-codecs/derived_postpass_compare.py \
  /tmp/derived.jsonl /tmp/postpass.tsv tests/ppx_spice/
```

Result on `tests/ppx_spice`:

```
bindings 386, joined 378, templates 226, templates with 2+ joined bindings 113, of which fixed 113, not fixed 0
```

The eight bindings not joined are names bound twice in one unit (nested
modules), which the dump cannot tell apart.
