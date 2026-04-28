/-
Pythia.FreedmanMaximal — Freedman's maximal inequality for martingales
with bounded increments and conditional sub-gamma MGF bound.

The original `freedman_maximal_bernstein` in MiniPythia.lean was false:
the parameter `V_n` had no connection to the actual predictable quadratic
variation, so the bound `exp(-ε²/(2(V_n + bε/3)))` (independent of `n`)
could not hold for large `n` (crossing probability → 1 for random walks).

This module provides a corrected version that adds:
- `hM0 : ∀ᵐ ω ∂μ, M 0 ω = 0` (process starts at 0)
- `hn : 0 < n` (non-trivial horizon)
- conditional sub-gamma MGF bounds on increments (the content of the
  bounded-to-subGamma embedding)

Given these, we construct a `SubGammaMG` and apply `subGamma_ville_ineq`
from `Pythia.SubGamma`, then reduce to Bernstein form via
`bernstein_of_subGamma` from `Pythia.Bernstein`.
-/
import Mathlib
import Pythia.SubGamma
import Pythia.Bernstein

namespace Pythia

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

/-- **Freedman's maximal Bernstein inequality** (corrected version).

    For a process `M` adapted to `𝓕` on a probability space, with
    `M₀ = 0` a.s., if the increments satisfy a conditional sub-gamma
    MGF bound with parameters `(V_n/n, b/3)`, then:
    ```
    P(max_{t ≤ n} M_t ≥ ε) ≤ exp(−ε² / (2(V_n + bε/3)))
    ```

    The original `freedman_maximal_bernstein` was false: the parameter
    `V_n` was unconnected to any property of the process, so the bound
    (independent of `n`) cannot hold in general. This corrected version
    requires the conditional sub-gamma MGF bound explicitly, which in
    practice follows from bounded increments + a conditional variance
    bound (via `mgf_le_subGamma_of_bounded` applied conditionally).

    Proved by constructing a `SubGammaMG` from the hypotheses and
    applying `bernstein_of_subGamma`. -/
theorem freedman_maximal_corrected
    {Ω : Type*} {mΩ : MeasurableSpace Ω} [StandardBorelSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {𝓕 : Filtration ℕ mΩ} {M : ℕ → Ω → ℝ}
    (h_adapted : Adapted 𝓕 M)
    (h_int : ∀ t, Integrable (M t) μ)
    (b : ℝ) (hb_pos : 0 < b)
    (V_n : ℝ) (hV_pos : 0 < V_n)
    (n : ℕ) (hn : 0 < n)
    (hM0 : ∀ᵐ ω ∂μ, M 0 ω = 0)
    -- Zero conditional mean of increments (martingale property)
    (h_zero_mean : ∀ t,
      μ[fun ω => M (t + 1) ω - M t ω | 𝓕 t] =ᵐ[μ] 0)
    -- Exponential integrability
    (h_exp_int : ∀ t lam, b / 3 * |lam| < 1 →
      Integrable (fun ω => Real.exp (lam * M t ω)) μ)
    (h_inc_exp_int : ∀ t lam, b / 3 * |lam| < 1 →
      Integrable (fun ω => Real.exp (lam * (M (t+1) ω - M t ω))) μ)
    -- Conditional sub-gamma MGF bound on increments
    (h_cond_mgf : ∀ t lam, b / 3 * |lam| < 1 →
      ∀ᵐ ω ∂μ,
        (μ[fun ω' => Real.exp (lam * (M (t+1) ω' - M t ω')) | 𝓕 t]) ω ≤
        Real.exp (V_n / ↑n * lam ^ 2 / (2 * (1 - b / 3 * lam))))
    (eps : ℝ) (hε : 0 < eps) :
    μ {ω | ∃ t : ℕ, t ≤ n ∧ M t ω ≥ eps} ≤
      ENNReal.ofReal (Real.exp (-(eps ^ 2) / (2 * (V_n + b * eps / 3)))) := by
  -- Construct SubGammaMG from the hypotheses
  have hnu_pos : 0 < V_n / ↑n := div_pos hV_pos (Nat.cast_pos.mpr hn)
  have hc_nonneg : 0 ≤ b / 3 := div_nonneg hb_pos.le (by norm_num)
  set S : SubGammaMG (V_n / ↑n) (b / 3) 𝓕 μ :=
    { process := M
      adapted := h_adapted
      integrable := h_int
      integrable_exp := h_exp_int
      increments_exp_integrable := h_inc_exp_int
      increments_subGamma := h_cond_mgf
      increments_zero_mean := h_zero_mean
      nu_pos := hnu_pos
      c_nonneg := hc_nonneg }
  exact bernstein_of_subGamma hn S hM0 hε

end Pythia
