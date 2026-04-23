# Kairos-Stats

Internal Lean 4 library for finite-precision statistics, Mathlib-style.

Namespace: `Kairos.Stats.*`

## Modules

- `Kairos.Stats.Basic` — `BitPrecision`, `Time`, shared primitives.
- `Kairos.Stats.Quantization` — quantization-transport lemma + per-family slack rates `etaHR`, `etaVector`, `etaAsymptotic`, `etaBetting` + ranking.
- `Kairos.Stats.SubGaussianMG` — measure-theoretic sub-Gaussian martingale structure, exponential supermartingale, Ville's inequality. Built on `Mathlib.Probability.Moments.SubGaussian.HasCondSubgaussianMGF`.
- `Kairos.Stats.GaussianSmallBall` — Gaussian small-ball lower bound (not in Mathlib; state + prove here).
- `Kairos.Stats.BettingStrategy` — wealth-process machinery for betting confidence sequences (not in Mathlib; define `BettingStrategy` type + wealth process + martingale property).

## Internal use

This library is internal to athanor-ai. Content that matures may be cherry-picked for upstream contribution to Mathlib later. Do not contribute upstream without founder approval.

## Lean toolchain

Pinned to `leanprover/lean4:v4.30.0-rc2` for parity with the ATH-512 scaffold.  Mathlib pinned via `lake-manifest.json` on the same commit as the NeurIPS 2026 paper's Lean formalisation (`ee3a540`).
