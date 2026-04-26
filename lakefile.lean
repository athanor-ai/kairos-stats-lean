-- Pythia: Lean 4 stats automation library.
-- Tactics + theorems for anytime-valid CS, sequential statistics,
-- concentration inequalities, and finite-precision quantization.

import Lake
open Lake DSL

package «Pythia» where

-- Pinned to Mathlib v4.28.0 for toolchain stability.
require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.28.0"

@[default_target]
lean_lib «Pythia» where
