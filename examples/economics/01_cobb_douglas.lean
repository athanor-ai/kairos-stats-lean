/-
Pythia starter pack: economics / production functions.

Two foundational closed-form facts for the Cobb-Douglas production
function `Y(K, L, α) = K^α · L^(1-α)`, exposed in pythia as
`Pythia.Economics.cobbDouglas`. Both theorems below are tagged
`@[stat_lemma]` so the headline `pythia!` tactic finds them via
the @[stat_lemma] aesop ruleset.

Run via:
    lake env lean examples/economics/01_cobb_douglas.lean
-/
import Pythia.Economics.CobbDouglas
import Pythia.Tactic.PythiaBang

open Pythia.Economics

/-! ## Constant returns to scale

Doubling both inputs doubles output: `Y(c·K, c·L, α) = c · Y(K, L, α)`.
A named property in growth theory; the standard derivation hinges on
the exponent identity `α + (1-α) = 1` plus a real-power algebra step.

(`c` not `λ`: `λ` is reserved for lambda expressions in Lean 4.) -/
example {K L α c : ℝ} (hK : 0 < K) (hL : 0 < L) (hc : 0 < c) :
    cobbDouglas (c * K) (c * L) α = c * cobbDouglas K L α := by
  pythia!

-- Alternative: when you already know the closed-form theorem name,
-- you can apply it directly without invoking the cascade.
example {K L α c : ℝ} (hK : 0 < K) (hL : 0 < L) (hc : 0 < c) :
    cobbDouglas (c * K) (c * L) α = c * cobbDouglas K L α :=
  cobb_douglas_crts hK hL hc

/-! ## Positivity of output

`Y(K, L, α) > 0` whenever both inputs are strictly positive — used
throughout growth-equilibrium arguments to justify dividing by `Y`. -/
example {K L α : ℝ} (hK : 0 < K) (hL : 0 < L) :
    0 < cobbDouglas K L α := by
  pythia!
