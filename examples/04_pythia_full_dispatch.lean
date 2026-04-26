/-
examples/04_pythia_full_dispatch.lean — the full `pythia` orchestrator.

Showcases what the `pythia` cascade does that no single tactic does on
its own. Each example drops into a different rung of the dispatch
ladder. See `docs/sledgehammer_dispatch.md` for the full routing table.

The cascade order:

  1. `anytime_valid`      Ville-bound shapes
  2. `stats_ineq`         concentration tails
  3. `prob_simp`          measure rewriting
  4. `z3_check`           QF_LRA over ℝ
  5. `aesop` + `Pythia` ruleset (registered `@[stat_lemma]` rules)
  6. generic Mathlib chain (`simp; omega; linarith; positivity`)
  7. `aesop` default ruleset
-/
import Pythia.Tactic.Pythia

open Pythia MeasureTheory

namespace Pythia.Examples.FullDispatch

/-! ### Rung 1: anytime_valid (Ville-bound). -/

example
    {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω}
    [IsFiniteMeasure μ] {f : ℕ → Ω → ℝ} {𝓕 : Filtration ℕ m0}
    (hsup : Supermartingale f 𝓕 μ) (hnn : ∀ t ω, 0 ≤ f t ω)
    (hint : Integrable (f 0) μ) {c : ℝ} (hc : 0 < c) :
    μ {ω : Ω | ∃ t : ℕ, f t ω ≥ c}
      ≤ (∫ ω, f 0 ω ∂μ).toNNReal / c.toNNReal := by
  pythia

/-! ### Rung 4: z3_check (QF_LRA falls through to linarith). -/

example (x y z : ℝ) (h1 : x ≤ y) (h2 : y ≤ z) : x ≤ z := by
  pythia

example (a b : ℝ) (ha : 0 < a) (hb : 0 < b) : 0 < a + b := by
  pythia

/-! ### Rung 5: registered @[stat_lemma]. -/

@[stat_lemma]
theorem nonneg_pair_sum_dispatch (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    0 ≤ a + b := by linarith

example (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) : 0 ≤ a + b := by
  pythia

/-! ### Rung 6: generic Mathlib chain. -/

example (n : ℕ) : n + 0 = n := by pythia

example (n : ℕ) (h : 5 ≤ n) : 3 ≤ n := by pythia

end Pythia.Examples.FullDispatch
