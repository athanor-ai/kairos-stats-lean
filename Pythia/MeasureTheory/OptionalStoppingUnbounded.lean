/-
Pythia.MeasureTheory.OptionalStoppingUnbounded — optional stopping
theorem for *unbounded* a.s.-finite stopping times under uniform
integrability of the stopped process.

Mathlib v4.28.0 (our pinned toolchain) only ships the **bounded-τ** form
of optional stopping: `MeasureTheory.Submartingale.expected_stoppedValue_mono`
requires `∃ N : ℕ, ∀ ω, π ω ≤ N`. The classical textbook generalisation
(Williams, *Probability with Martingales*, Theorem 10.10; Doob, *Stochastic
Processes*, III.2) drops the bound and replaces it with the joint
hypotheses

  (H1)  `τ < ∞ a.s.`,
  (H2)  the family `(M_(τ ∧ n))_{n : ℕ}` is uniformly integrable in L¹.

Under (H1)+(H2) one has

  E[M_τ] = E[M_0]                         (mean-preservation)

for every L¹-martingale `M`. This is the form practitioners use when the
stopping time is genuinely unbounded — e.g. first-hitting times of a
random walk, Wald's identity for sequential analysis (`wald_identity_centered`,
`wald_identity_squared` in `Pythia/WaldIdentity.lean`), and the
SPRT closure (`Pythia/SPRT.lean`).

We do **not** have Mathlib commit access on the v4.28 pin and we are not
waiting on an upstream PR. This module ships the unbounded form *inside
pythia* on top of v4.28 building blocks.

## Proof sketch (Williams §10.10)

Let `M^τ_n := stoppedProcess M τ n`. Then:

1. **Bounded-form integral identity.**  Each `M^τ_n` is the stopped value of
   `M` at the *bounded* stopping time `min n τ ≤ n`; so by the bounded
   optional-sampling theorem applied to the martingale (sub + super)
   structure of `M`, `E[M^τ_n] = E[M_0]` for every `n : ℕ`.
2. **Pointwise a.s. convergence.**  On `{τ < ∞}` (full measure by H1),
   `M^τ_n(ω) = M_(τ(ω))(ω)` for all `n ≥ τ(ω)`, hence
   `M^τ_n(ω) → M_(τ(ω))(ω) = (stoppedValue M τ)(ω)` as `n → ∞`.
3. **L¹ convergence via Vitali.**  By H2 the family is uniformly integrable
   in the probability sense, and pointwise a.s. convergence + UI give
   convergence in L¹ (`MeasureTheory.tendsto_Lp_finite_of_tendstoInMeasure`
   applied at `p = 1`, with `tendstoInMeasure_of_tendsto_ae`).
4. **Conclusion.**  L¹ convergence implies integral convergence
   (`MeasureTheory.tendsto_integral_of_L1`), so
   `E[M^τ_n] → E[stoppedValue M τ]`. Combined with (1), the limit on the
   left is `E[M_0]`. Hence `E[stoppedValue M τ] = E[M_0]`.

## Closure status (2026-04-25)

**Fully closed** — zero sorries, zero new axioms. `#print axioms` reports
exactly `[propext, Classical.choice, Quot.sound]`.

The proof body realises the four-step Williams sketch on Mathlib v4.28
building blocks alone:

1. `step1` (bounded-form identity, sandwich): apply
   `Submartingale.expected_stoppedValue_mono` to `M` (giving `≤`) and to
   `-M` (giving `≥`) at the bounded stopping pair `(0, min τ n)`; combine
   with `stoppedValue_const`, `stoppedProcess_eq_stoppedValue`, and
   `integral_neg` for `le_antisymm`.
2. `step2_ae` (pointwise a.s. convergence): on `{τ < ∞}`, the sequence
   is eventually constant past `(τ ω).untopA`; close with
   `tendsto_atTop_of_eventually_const` and `stoppedProcess_eq_of_ge` via
   `min_eq_right`.
3. `step3_L1` (L¹ convergence by Vitali): combine `step2_ae` with
   `tendstoInMeasure_of_tendsto_ae` and feed
   `tendsto_Lp_finite_of_tendstoInMeasure`; the limit's `MemLp 1` is
   produced by `UniformIntegrable.memLp_of_ae_tendsto`.
4. `step4_int` + `step4_const`: integral commutes with L¹ limits via
   `tendsto_integral_of_L1'`; constant sequence by `step1`. Conclude
   with `tendsto_nhds_unique`.

## References

* Williams, *Probability with Martingales*, Cambridge 1991, §10.10
  ("Optional stopping for uniformly integrable martingales").
* Doob, *Stochastic Processes*, Wiley 1953, Theorem III.2.
* Mathlib v4.28: `MeasureTheory.Submartingale.expected_stoppedValue_mono`
  (bounded form), `MeasureTheory.tendsto_Lp_finite_of_tendstoInMeasure`
  (Vitali), `MeasureTheory.tendsto_integral_of_L1`.
-/

import Mathlib
import Pythia.Basic

namespace Pythia.MTUnbounded

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology

universe u

variable {Ω : Type u} {m0 : MeasurableSpace Ω} {μ : MeasureTheory.Measure Ω}
variable {𝒢 : MeasureTheory.Filtration ℕ m0}

/-- **Optional stopping for uniformly integrable martingales** (Williams §10.10).

For an L¹-martingale `M : ℕ → Ω → ℝ` adapted to a filtration `𝒢`, an
a.s.-finite stopping time `τ : Ω → ℕ∞`, and the joint hypothesis that the
stopped process `(M_(τ ∧ n))_n` is uniformly integrable in the probability
sense at `p = 1`, the integral identity

  ∫ ω, stoppedValue M τ ω ∂μ = ∫ ω, M 0 ω ∂μ

holds. Closes the unbounded-τ gap in Mathlib v4.28's optional-stopping
file (`MeasureTheory.Probability.Martingale.OptionalStopping`), which only
provides the bounded form. See module docstring for proof structure and
sorry-status.
-/
theorem optional_stopping_unbounded
    [IsFiniteMeasure μ] [SigmaFiniteFiltration μ 𝒢]
    {M : ℕ → Ω → ℝ}
    (hM : Martingale M 𝒢 μ)
    {τ : Ω → ℕ∞}
    (hτ : MeasureTheory.IsStoppingTime 𝒢 τ)
    (hτ_finite : ∀ᵐ ω ∂μ, τ ω ≠ ⊤)
    (hUI : UniformIntegrable
              (fun n : ℕ => MeasureTheory.stoppedProcess M τ n) 1 μ) :
    ∫ ω, MeasureTheory.stoppedValue M τ ω ∂μ = ∫ ω, M 0 ω ∂μ := by
  -- --------------------------------------------------------------------
  -- Step 1 (bounded-form integral identity): ∀ n, ∫ stoppedProcess M τ n = ∫ M 0
  -- --------------------------------------------------------------------
  have hsub : Submartingale M 𝒢 μ := hM.submartingale
  have hsup : Supermartingale M 𝒢 μ := hM.supermartingale
  have hsub_neg : Submartingale (-M) 𝒢 μ := hsup.neg
  have step1 :
      ∀ n : ℕ,
        ∫ ω, MeasureTheory.stoppedProcess M τ n ω ∂μ = ∫ ω, M 0 ω ∂μ := by
    -- Apply bounded `Submartingale.expected_stoppedValue_mono` to `M` and to
    -- `-M` to sandwich `∫ stoppedProcess M τ n` between `∫ M 0` from above
    -- and below — i.e. `≤` and `≥` give equality.
    intro n
    -- Bounded stopping time σ_n := min τ n ≤ n, and the constant 0 stopping time.
    let σ : Ω → ℕ∞ := fun ω => min (τ ω) (n : ℕ∞)
    have hσ_st : MeasureTheory.IsStoppingTime 𝒢 σ :=
      hτ.min_const (n : ℕ)
    have h0_st : MeasureTheory.IsStoppingTime 𝒢 (fun _ : Ω => (0 : ℕ∞)) :=
      MeasureTheory.isStoppingTime_const _ _
    have hσ_bdd : ∀ ω, σ ω ≤ (n : ℕ∞) := fun ω => min_le_right _ _
    have h0_le_σ : (fun _ : Ω => (0 : ℕ∞)) ≤ σ := fun ω => by
      simp [σ]
    -- stoppedValue M σ = stoppedProcess M τ n  (since stoppedProcess uses
    -- `min i (τ ω)` and our σ is `min (τ ω) i = min i (τ ω)`).
    have hsv_eq :
        (fun ω => MeasureTheory.stoppedValue M σ ω) =
          (fun ω => MeasureTheory.stoppedProcess M τ n ω) := by
      funext ω
      simp [MeasureTheory.stoppedValue, MeasureTheory.stoppedProcess, σ, min_comm]
    -- stoppedValue M (fun _ => 0) = M 0  (by `stoppedValue_const`).
    have hsv0 :
        (fun ω => MeasureTheory.stoppedValue M (fun _ : Ω => (0 : ℕ∞)) ω) =
          (fun ω => M 0 ω) := by
      funext ω; rfl
    -- Forward: ∫ M 0 ≤ ∫ stoppedProcess M τ n, from M as a submartingale.
    have h_le :
        ∫ ω, M 0 ω ∂μ ≤ ∫ ω, MeasureTheory.stoppedProcess M τ n ω ∂μ := by
      have := hsub.expected_stoppedValue_mono h0_st hσ_st h0_le_σ hσ_bdd
      -- this : μ[stoppedValue M (fun _ => 0)] ≤ μ[stoppedValue M σ]
      -- which by hsv_eq + hsv0 is the desired bound.
      simpa [hsv_eq, hsv0] using this
    -- Reverse: ∫ stoppedProcess M τ n ≤ ∫ M 0, from -M as a submartingale.
    have h_ge :
        ∫ ω, MeasureTheory.stoppedProcess M τ n ω ∂μ ≤ ∫ ω, M 0 ω ∂μ := by
      have hneg := hsub_neg.expected_stoppedValue_mono h0_st hσ_st h0_le_σ hσ_bdd
      -- hneg : μ[stoppedValue (-M) (fun _ => 0)] ≤ μ[stoppedValue (-M) σ]
      -- stoppedValue (-M) σ ω = -(stoppedValue M σ ω) = -stoppedProcess M τ n ω
      -- stoppedValue (-M) (fun _ => 0) ω = -(M 0 ω)
      -- So hneg ⇔ ∫ -(M 0) ≤ ∫ -(stoppedProcess M τ n) ⇔ desired.
      have hsvN_σ :
          (fun ω => MeasureTheory.stoppedValue (-M) σ ω) =
            (fun ω => -(MeasureTheory.stoppedProcess M τ n ω)) := by
        funext ω
        simp [MeasureTheory.stoppedValue, MeasureTheory.stoppedProcess, σ, min_comm]
      have hsvN_0 :
          (fun ω => MeasureTheory.stoppedValue (-M) (fun _ : Ω => (0 : ℕ∞)) ω) =
            (fun ω => -(M 0 ω)) := by
        funext ω; simp [MeasureTheory.stoppedValue]
      simp only [hsvN_σ, hsvN_0] at hneg
      have hint_M0 : Integrable (fun ω => M 0 ω) μ := hM.integrable 0
      have hint_sp : Integrable (fun ω => MeasureTheory.stoppedProcess M τ n ω) μ := by
        have := hsub.integrable_stoppedValue hσ_st hσ_bdd
        -- `this` is `Integrable (stoppedValue M σ) μ`, and `stoppedValue M σ = stoppedProcess M τ n`.
        simpa [hsv_eq] using this
      -- hneg : ∫ -(M 0 ω) ∂μ ≤ ∫ -(stoppedProcess M τ n ω) ∂μ
      have h_int_neg_eq : ∫ ω, -(M 0 ω) ∂μ = -∫ ω, M 0 ω ∂μ :=
        integral_neg _
      have h_int_neg_eq' :
          ∫ ω, -(MeasureTheory.stoppedProcess M τ n ω) ∂μ
            = -∫ ω, MeasureTheory.stoppedProcess M τ n ω ∂μ :=
        integral_neg _
      rw [h_int_neg_eq, h_int_neg_eq', neg_le_neg_iff] at hneg
      exact hneg
    exact le_antisymm h_ge h_le
  -- --------------------------------------------------------------------
  -- Step 2 (pointwise a.s. convergence): stoppedProcess M τ n → stoppedValue M τ a.s.
  -- --------------------------------------------------------------------
  have step2_ae :
      ∀ᵐ ω ∂μ, Tendsto (fun n : ℕ => MeasureTheory.stoppedProcess M τ n ω)
          atTop (𝓝 (MeasureTheory.stoppedValue M τ ω)) := by
    -- On {τ ω ≠ ⊤} we have stoppedProcess M τ n ω = stoppedValue M τ ω
    -- eventually in n (specifically for all n ≥ (τ ω).untopA). This is the
    -- `stoppedProcess_eq_of_ge` identity once `τ ω ≤ n` in the `WithTop ℕ`
    -- order. Hence the sequence is eventually constant, hence converges
    -- to that constant.
    filter_upwards [hτ_finite] with ω hω
    -- τ ω ≠ ⊤, so let t : ℕ be the underlying value.
    -- For n ≥ t, min n (τ ω) = τ ω, so
    --   stoppedProcess M τ n ω = M ((min n (τ ω)).untopA) ω
    --                          = M ((τ ω).untopA) ω
    --                          = stoppedValue M τ ω.
    -- Therefore the sequence is eventually constant equal to
    -- stoppedValue M τ ω, hence tends to it.
    refine tendsto_atTop_of_eventually_const (i₀ := (τ ω).untopA) (fun n hn => ?_)
    -- Need: stoppedProcess M τ n ω = stoppedValue M τ ω, given n ≥ (τ ω).untopA.
    have hτ_le : τ ω ≤ (n : ℕ∞) := by
      -- (τ ω).untopA ≤ n in ℕ implies (τ ω) ≤ (n : ℕ∞), since τ ω ≠ ⊤.
      have h_eq : ((τ ω).untopA : ℕ∞) = τ ω :=
        (WithTop.untopA_eq_untop hω).symm ▸ (WithTop.coe_untop _ hω)
      calc τ ω = ((τ ω).untopA : ℕ∞) := h_eq.symm
        _ ≤ (n : ℕ∞) := by exact_mod_cast hn
    simp [MeasureTheory.stoppedProcess, MeasureTheory.stoppedValue,
          min_eq_right hτ_le]
  -- --------------------------------------------------------------------
  -- Step 3 (L¹ convergence): stoppedProcess M τ n → stoppedValue M τ in L¹.
  -- --------------------------------------------------------------------
  -- Strongly measurable shape of stoppedValue M τ (limit) and integrability.
  have hmeas_seq :
      ∀ n : ℕ,
        AEStronglyMeasurable (MeasureTheory.stoppedProcess M τ n) μ :=
    fun n => hUI.1 n
  -- The limit is in MemLp 1, hence integrable.
  have hlim_memLp :
      MeasureTheory.MemLp (MeasureTheory.stoppedValue M τ) 1 μ :=
    hUI.memLp_of_ae_tendsto (u := atTop) step2_ae
  have hlim_integrable :
      Integrable (MeasureTheory.stoppedValue M τ) μ :=
    hlim_memLp.integrable le_rfl
  have step3_L1 :
      Tendsto
        (fun n : ℕ =>
          eLpNorm
            (MeasureTheory.stoppedProcess M τ n - MeasureTheory.stoppedValue M τ)
            1 μ)
        atTop (𝓝 0) := by
    -- Vitali: UI + tendstoInMeasure ⇒ tendsto in L¹.
    refine MeasureTheory.tendsto_Lp_finite_of_tendstoInMeasure
      (p := 1) le_rfl ENNReal.one_ne_top hmeas_seq hlim_memLp hUI.2.1 ?_
    -- TendstoInMeasure side: pointwise a.s. ⇒ in measure (finite measure).
    exact MeasureTheory.tendstoInMeasure_of_tendsto_ae hmeas_seq step2_ae
  -- --------------------------------------------------------------------
  -- Step 4 (conclude): integral commutes with L¹ limit, combine with step1.
  -- --------------------------------------------------------------------
  -- ∫ stoppedProcess M τ n → ∫ stoppedValue M τ
  have step4_int :
      Tendsto
        (fun n : ℕ => ∫ ω, MeasureTheory.stoppedProcess M τ n ω ∂μ)
        atTop (𝓝 (∫ ω, MeasureTheory.stoppedValue M τ ω ∂μ)) := by
    refine MeasureTheory.tendsto_integral_of_L1'
      (MeasureTheory.stoppedValue M τ) hlim_integrable ?_ step3_L1
    -- Eventually-integrable: each stoppedProcess M τ n is integrable (UI ⇒ memLp 1).
    refine Filter.Eventually.of_forall (fun n => ?_)
    have : MemLp (MeasureTheory.stoppedProcess M τ n) 1 μ := hUI.memLp n
    exact this.integrable le_rfl
  -- The LHS is constantly ∫ M 0 by step1; so the limit is ∫ M 0.
  have step4_const :
      Tendsto
        (fun n : ℕ => ∫ ω, MeasureTheory.stoppedProcess M τ n ω ∂μ)
        atTop (𝓝 (∫ ω, M 0 ω ∂μ)) := by
    simp_rw [step1]
    exact tendsto_const_nhds
  -- Two limits of the same sequence agree.
  exact (tendsto_nhds_unique step4_int step4_const)

end Pythia.MTUnbounded
