/-
Pythia starter pack — economics / production functions.

Two foundational closed-form facts for the Cobb-Douglas production
function `Y(K, L) = K^α · L^(1-α)`: constant returns to scale and
positivity. Both close via the registered @[stat_lemma]s.

Run via:
    lake env lean examples/economics/01_cobb_douglas.lean
-/
import Pythia.Economics.CobbDouglas
import Pythia.Tactic.PythiaBang

open Pythia

/-! ## Constant returns to scale

Doubling both inputs doubles output: `Y(λK, λL) = λ · Y(K, L)`. A
named property in growth theory; the standard textbook derivation
hinges on the exponent identity `α + (1-α) = 1` plus a real-power
algebra step. -/
example (K L α λ : ℝ) (hK : 0 < K) (hL : 0 < L) (hλ : 0 < λ)
    (hα0 : 0 < α) (hα1 : α < 1) :
    (λ * K) ^ α * (λ * L) ^ (1 - α) = λ * (K ^ α * L ^ (1 - α)) :=
  cobb_douglas_crts hK hL hλ hα0 hα1

/-! ## Positivity of output

`Y(K, L) > 0` whenever both inputs are strictly positive. Used
constantly in growth-equilibrium arguments to justify dividing
through by `Y`. -/
example (K L α : ℝ) (hK : 0 < K) (hL : 0 < L)
    (hα0 : 0 < α) (hα1 : α < 1) :
    0 < K ^ α * L ^ (1 - α) :=
  cobb_douglas_pos hK hL hα0 hα1
