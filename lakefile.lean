-- Kairos-Stats: Lean 4 library for finite-precision statistics.
-- Mathlib-style supermartingale + Ville + sub-Gaussian concentration
-- + per-family CS slack rates under bit-width quantization.

import Lake
open Lake DSL

package «KairosStats» where

-- Pinned to Mathlib v4.28.0 so every file we write can be sanity-checked by
-- Aristotle without toolchain drift. Verified against Aristotle submission
-- tarballs 2026-04-24. Never bump ahead of Aristotle.
require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.28.0"

@[default_target]
lean_lib «Kairos» where
