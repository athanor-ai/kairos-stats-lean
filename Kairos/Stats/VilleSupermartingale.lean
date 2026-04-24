/-
Kairos.Stats.VilleSupermartingale — Ville's inequality for non-negative supermartingales.

**ATH-591 first Mathlib PR target.** This module is the upstream contribution
candidate. The theorem extends Mathlib's existing
`MeasureTheory.maximal_ineq` (which covers non-negative submartingales) to the
supermartingale direction used throughout anytime-valid CS work.

**Theorem:** For a non-negative supermartingale `M` on filtration `𝓕` with
`M_0` integrable, and any `c > 0`:
    `μ{ω : ∃ t, M_t(ω) ≥ c} ≤ E[M_0] / c`

**Proof sketch (paper-ready):**
1. Define the stopping time `τ = inf{t : M_t ≥ c}`.
2. On `{τ < ∞}`, `M_τ ≥ c` by definition of τ.
3. By optional stopping, `E[M_{τ∧N}] ≤ E[M_0]` for any horizon N.
4. Markov: `c · μ(τ ≤ N) ≤ E[M_{τ∧N} · 1_{τ≤N}] ≤ E[M_{τ∧N}] ≤ E[M_0]`.
5. Take N → ∞ by monotone convergence to conclude.

**Downstream usage in kairos-stats-lean:**
- `BettingCS.lean`: log-wealth supermartingale admissibility
- `HowardRamdasCS.lean`: sub-Gaussian self-normalized tail bound
- Any future sub-gamma or PAC-Bayes anytime-valid CS construction

**Status:** stub with sorry. First attempt: local Mathlib tactic search via
`lean_multi_attempt`. Fallback: Aristotle on structural optional-stopping step.

**Mathlib PR target:** port this theorem + corollaries to
`Mathlib.Probability.Martingale.Maximal` once axiom-clean and tested on
downstream kairos-stats-lean usage.
-/

import Mathlib
import Kairos.Stats.Basic

namespace Kairos.Stats

open MeasureTheory ProbabilityTheory

/-- **Ville's inequality for non-negative supermartingales.**

For a non-negative supermartingale `f` on filtration `𝓕` with finite measure
space, and any threshold `c > 0`, the probability that the supermartingale
ever exceeds `c` is bounded by `E[f_0] / c`.

This is the supermartingale extension of Mathlib's `maximal_ineq` (which is
stated for non-negative submartingales). The standard reference is Ville's
1939 thesis on martingales applied to game-theoretic probability. -/
theorem ville_supermartingale
    {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω} [IsFiniteMeasure μ]
    {f : ℕ → Ω → ℝ} {𝓕 : @Filtration Ω ℕ _ m0}
    (hsup : Supermartingale f 𝓕 μ) (hnonneg : ∀ t ω, 0 ≤ f t ω)
    (hint : Integrable (f 0) μ)
    {c : ℝ} (hc : 0 < c) :
    μ {ω : Ω | ∃ t : ℕ, f t ω ≥ c} ≤ (∫ ω, f 0 ω ∂μ).toNNReal / c.toNNReal := by
  sorry

end Kairos.Stats
