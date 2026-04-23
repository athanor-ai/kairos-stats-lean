-- Kairos-Stats: Lean 4 library for finite-precision statistics.
-- Mathlib-style; internal to athanor-ai. Cherry-pick later.

import Lake
open Lake DSL

package «KairosStats» where

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "master"

@[default_target]
lean_lib «Kairos» where
