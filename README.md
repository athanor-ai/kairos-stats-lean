# Kairos-Stats

Lean 4 library for finite-precision anytime-valid statistics: sub-Gaussian martingales, Ville's inequality, per-family quantization slack rates for confidence sequences (CS).

## Modules

- `Kairos.Stats.Basic` — `BitPrecision`, `Time`, shared primitives.
- `Kairos.Stats.Quantization` — scalar quantization-transport lemma + per-family slack rates `etaHR`, `etaVector`, `etaAsymptotic`, `etaBetting` + the arithmetic ranking `η_betting ≤ η_aCS ≤ η_HR ≤ η_vector`.
- `Kairos.Stats.SubGaussianMG` — measure-theoretic sub-Gaussian martingale structure, exponential supermartingale, Ville's inequality (finite horizon) on top of `ProbabilityTheory.HasCondSubgaussianMGF`.
- `Kairos.Stats.GaussianSmallBall` — Gaussian small-ball lower bound on the boundary-grazing event (not in Mathlib).
- `Kairos.Stats.BettingStrategy` — wealth-process machinery for betting confidence sequences.
- `Kairos.Stats.HowardRamdasCS` — self-normalized CS admissibility at a telescoping-boundary refinement of Howard et al. 2021.
- `Kairos.Stats.BettingCS` — betting CS admissibility via infinite-horizon Ville + measure continuity from below.
- `Kairos.Stats.GaussianRandomWalk`, `StoppingRule`, `Sharpness`, `PowerAnalysis`, `DeploymentDesign`, `SubGamma` — supporting modules for per-family rate derivations and deployment-design inverses.

## Build

```bash
lake exe cache get
lake build
```

## Lean toolchain

Pinned to `leanprover/lean4:v4.30.0-rc2`.  Mathlib pinned via `lake-manifest.json`.

## Axiom audit

Most theorems close with `{propext, Classical.choice, Quot.sound}`.  A single `sorryAx` residual on `bettingStoppingRule_admissible` traces to a specification-incompatibility field (`monotone_once_fired`) that is unprovable on principle for strictly-increasing thresholds, not from the admissibility proof itself.

## License

Apache-2.0.
