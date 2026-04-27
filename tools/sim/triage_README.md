# Pythia Module Triage

ATH-790 output. Every `.lean` file under `Pythia/` (excluding `*Test.lean`) is classified into one of three tiers.

## Files

| File | Purpose |
|------|---------|
| `triage.json` | 127-entry classification record |
| `triage_schema.json` | JSON Schema draft 2020-12 for strict validation |

## Tier definitions

**Tier-A** — User-facing applied-math results. The theorem statement is a claim a practitioner would test empirically (a bound, formula, or convergence rate). Eligible for sim pairing in `theorem_manifest.py`.

**Tier-B** — Statistics-spine infrastructure. Theorems with empirical content that serve as building blocks for Tier-A results rather than being directly user-facing. Organized into spine-sim clusters.

**Tier-C** — Pure Lean structural. Tactic plumbing, attribute registries, umbrella import modules, trivial lemmas (`True := by trivial`). No empirical content; no sim needed.

## Spine-sim clusters (Tier-B)

| Cluster key | Module examples |
|-------------|-----------------|
| `confidence_sequence` | `AnytimeCS`, `AsymptoticSharpness`, `eBernstein`, `eLIL`, `eMixture`, `OneD` (and ~15 others) |
| `concentration_iid_bounded` | `BoundedDifferences`, `ChernoffBinomial`, `SubGamma`, `MGFBoundedSubGamma`, `HoeffdingLemma` |
| `martingale_concentration` | `BDG`, `ConditionalJensen`, `SubGaussianMG`, `VilleSupermartingale`, `GaussianRandomWalk`, `OptionalStoppingUnbounded`, `PathMeasureRN` |
| `stochastic_approximation` | `RobbinsSiegmund`, `RobbinsMonro`, `Dvoretzky` |
| `time_series` | `NeweyWest`, `WoldDecomposition` |

## Symmetry vocabulary

Tags used in the `symmetries` field for Tier-A/B entries:

| Tag | Meaning |
|-----|---------|
| `homogeneous(param, exponent=k)` | Result scales as `param^k` under rescaling |
| `permutation_invariant(inputs)` | Result invariant under reordering of named inputs |
| `time_reversal` | Result invariant under t -> T-t transformation |
| `bilinear` | Linear in each of two named arguments |
| `subadditive` | f(X+Y) <= f(X) + f(Y) |
| `limit_case(condition)` | Degenerate / boundary regime |
| `scale_invariant(param)` | Result unchanged when param is rescaled |
| `monotone` | Monotone in a named argument |
| `power_law(param)` | Result is a power function of param |
| `translation_invariant` | Invariant under additive shift |

## Validation

```
pip install jsonschema
python3 -m jsonschema -i tools/sim/triage.json tools/sim/triage_schema.json
```

Exit 0 means valid.

## Updating when new Lean modules land

1. Add an entry to `triage.json` keyed by the module's path relative to the repo root (e.g. `"Pythia/NewModule.lean"`).
2. Choose a tier (A, B, or C). Tier-A requires `symmetries`, `regime`, `shared_spine_sim`, and `differential_candidate`. Tier-C requires only `tier`, `theorem_names`, and `rationale`.
3. If the module is Tier-A and has a corresponding sim, also add it to `tools/sim/theorem_manifest.py`.
4. Run the validation command above to confirm the new entry is schema-valid.
5. CI will reject PRs if `triage.json` fails schema validation (once the gate is wired).

## Counts (ATH-790 baseline, 2026-04-27)

| Tier | Count |
|------|-------|
| A | 57 |
| B | 23 |
| C | 47 |
| **Total** | **127** |

## Borderline cases flagged for research review

| Module | Issue |
|--------|-------|
| `Pythia/EquivalenceBreak.lean` | Main theorem is documented as provably FALSE in the file header; classified Tier-B (spine) but may warrant removal or renaming |
| `Pythia/Bio/Phylogenetics.lean` | Only real theorem is `True := by trivial`; classified Tier-C but the module stub may grow |
| `Pythia/MathlibTags.lean` | Pre-paired in `theorem_manifest.py` as Tier-A; contains only attribute declarations, no theorem bodies — classified Tier-A per manifest precedence |
