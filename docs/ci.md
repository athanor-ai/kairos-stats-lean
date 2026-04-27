# CI: Lean build cache

The `Lean Build + Axiom Audit` workflow (`.github/workflows/lean-build.yml`)
uses a three-tier cache so most PRs do not rebuild Mathlib or re-clone the
dependency tree.

## The three tiers

1. **`~/.elan/`** (toolchain). Keyed on `lean-toolchain` content. Cache hit
   skips the elan curl + install. Invalidates only on a toolchain bump.
2. **`.lake/packages/`** (resolved dependency tree). Keyed on
   `lake-manifest.json`. Holds the cloned mathlib + transitive deps.
   Invalidates only on `lake update`.
3. **`.lake/build/`** (compiled olean output). Keyed on
   `(lean-toolchain, lake-manifest.json, OS)`. Invalidates whenever the
   toolchain or any dep bumps.

Each cache step pins `actions/cache@v4` for reproducibility.

## Restore-keys

Tier 3 has a layered restore-keys fallback so a near-miss still seeds most
of the cache:

```
pythia-lake-build-${{ runner.os }}-${{ hashFiles('lean-toolchain', 'lake-manifest.json') }}
  -> pythia-lake-build-${{ runner.os }}-${{ hashFiles('lean-toolchain') }}-
  -> pythia-lake-build-${{ runner.os }}-
```

The `lake exe cache get` step still runs after restore so any olean files
not present locally get pulled from the Mathlib bucket.

## Expected timing

- Cold cache (toolchain bump or `lake update`): about 17 min.
- Warm cache (most PRs): about 2 to 3 min.

Cold time is dominated by Mathlib elaboration. Warm time is bounded by
checkout + `lake build` re-elaborating the pythia layer plus the per-file
sweep.

## Interaction with branch protection

The job name `build` is referenced by the branch protection rule on
`main`. Renaming the job breaks merges. Cache steps live inside `build`,
so the contract holds.

## When caches go stale

- Bump `lean-toolchain` -> all three tiers invalidate; first run after the
  bump pays the full cold cost.
- `lake update` -> tier 2 (packages) and tier 3 (build) invalidate; tier 1
  stays.
- Edits under `Pythia/` -> all three tiers stay warm; only the local
  pythia layer re-elaborates.

## Manual cache flush

GitHub: Actions -> Caches -> select keys with prefix `pythia-lake-` or
`pythia-elan-` -> delete. Useful if a partial cache poisons a build.

## Reference

The configuration follows the pattern documented at
<https://github.com/leanprover/lean-action> for hand-rolled multi-key
caching. `leanprover/lean-action@v1.5.0` is an alternative single-action
path; we use the hand-rolled form so we can split toolchain caching out
of the build cache and tune restore-keys directly.
