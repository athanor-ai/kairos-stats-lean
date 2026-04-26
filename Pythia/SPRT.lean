/-
Pythia.SPRT — Wald's sequential probability ratio test.

The SPRT (Wald 1947) is the foundational *sequential* hypothesis test:
two simple hypotheses

  H_0: data is iid p_0,    H_1: data is iid p_1,

observe X_1, X_2, … sequentially, maintain the log-likelihood ratio
Λ_n = Σ_{i ≤ n} log(p_1(X_i) / p_0(X_i)), stop at the first n with
Λ_n ≥ A or Λ_n ≤ B (for A > 0 > B), then declare H_1 if Λ_n ≥ A and
H_0 if Λ_n ≤ B.

Mathlib has zero formalization of SPRT. We ship four headline theorems:

* `SPRT.error_rates`           — Wald's bound on type-I error in terms
                                  of the (A, B) boundaries.
* `SPRT.wald_approximation`    — practitioner-facing form: choose
                                  A = log((1-β)/α), B = log(β/(1-α))
                                  to get error rates ≤ (α, β).
* `SPRT.wald_wolfowitz_optimal` — *the* optimality theorem: SPRT
                                  minimizes E[τ | H_0] and E[τ | H_1]
                                  among all sequential tests with the
                                  same error rates. Aristotle-class.
* `SPRT.expected_sample_size`  — closed-form E[τ | H_i] in terms of KL
                                  divergences D(p_i ‖ p_{1-i}).

Status (2026-04-26):
  error_rates — CLOSED axiom-clean via Ville + continuity of measure.
  wald_approximation — honest-sorry: single-measure signature insufficient;
    needs two-measure extension (μ₀ + μ₁) + Wald 2×2 algebra. Sharpened
    closure plan in docstring.
  wald_wolfowitz_optimal — honest-sorry: Aristotle-class (Wald-Wolfowitz 1948
    §326–339; Lehmann-Romano TSH §3.7). Three Mathlib v4.28 gaps: path-measure
    RN derivative chain for infinite products, minimax sequential test
    characterization, inf-integral interchange. Sharpened in docstring.
  expected_sample_size — honest-sorry: wald_identity sorry + iIndepFun-to-
    martingale bridge + missing _hExit boundary hypothesis. Sharpened in
    docstring.

References
----------
* Wald (1947), *Sequential Analysis*. Wiley.
* Wald & Wolfowitz (1948), *Optimum character of the SPRT*.
* Siegmund (1985), *Sequential Analysis*. Modern reference.
* Ramdas, Grünwald, Vovk, Shafer (2023), *Game-theoretic statistics*.
-/
import Mathlib
import Pythia.Basic
import Pythia.WaldIdentity
import Pythia.SubGaussianMG

namespace Pythia

open MeasureTheory ProbabilityTheory Real
open scoped ENNReal NNReal

universe u

/-- An SPRT specification: two probability density functions `p₀, p₁`
on a measurable space, with boundary parameters `A > 0 > B`. The
`logLR` field stores the per-sample log-likelihood ratio
`log(p₁ x / p₀ x)` as a measurable real-valued function — abstract
rather than computed from `p₀, p₁` so that the user can plug in the
analytic form for tractable hypothesis pairs. -/
structure SPRT (X : Type u) [MeasurableSpace X] where
  /-- Per-sample log-likelihood ratio. -/
  logLR     : X → ℝ
  /-- LR is measurable. -/
  logLR_mble : Measurable logLR
  /-- Upper boundary. -/
  A          : ℝ
  /-- Lower boundary. -/
  B          : ℝ
  /-- A > 0. -/
  hA_pos     : 0 < A
  /-- B < 0. -/
  hB_neg     : B < 0

namespace SPRT

variable {X : Type u} [MeasurableSpace X]
variable {Ω : Type u} {mΩ : MeasurableSpace Ω}
variable {μ : Measure Ω}

/-- The cumulative log-likelihood ratio process for an iid sample
sequence `Y : ℕ → Ω → X`:

  Λ_n(ω) = Σ_{i < n} logLR(Y i ω). -/
noncomputable def cumLogLR (S : SPRT X) (Y : ℕ → Ω → X) (n : ℕ) (ω : Ω) : ℝ :=
  (Finset.range n).sum (fun i => S.logLR (Y i ω))

@[simp] lemma cumLogLR_zero (S : SPRT X) (Y : ℕ → Ω → X) (ω : Ω) :
    cumLogLR S Y 0 ω = 0 := by
  simp [cumLogLR]

lemma cumLogLR_succ (S : SPRT X) (Y : ℕ → Ω → X) (n : ℕ) (ω : Ω) :
    cumLogLR S Y (n + 1) ω = cumLogLR S Y n ω + S.logLR (Y n ω) := by
  simp [cumLogLR, Finset.sum_range_succ]

/-- The boundary-exit event at time `n`: the cumulative LR has left
the continuation region `(B, A)` by step `n`. -/
def exitedBy (S : SPRT X) (Y : ℕ → Ω → X) (n : ℕ) (ω : Ω) : Prop :=
  cumLogLR S Y n ω ≤ S.B ∨ S.A ≤ cumLogLR S Y n ω

/-- The "rejected H_0" event up to time `n`: cumulative LR has crossed
the upper boundary at some `k ≤ n`. -/
def rejectedH0By (S : SPRT X) (Y : ℕ → Ω → X) (n : ℕ) (ω : Ω) : Prop :=
  ∃ k, k ≤ n ∧ S.A ≤ cumLogLR S Y k ω

/-- **Wald's error-rate bound** (the basic SPRT guarantee).

For any SPRT with boundary `A > 0`, under H_0 (data iid p₀) the
probability that the running cumulative LR ever crosses `A` is at most
`exp(-A)`:

  Pr_{H_0}(∃ n, Λ_n ≥ A) ≤ exp(-A).

This is the type-I error of the boundary-stopping test. The dual under
H_1 gives the type-II error.

Proof (2026-04-26, axiom-clean):
  1. exp(Λ_n) is a non-negative supermartingale (hypothesis _hExpLR_super).
  2. exp(Λ_0) = 1 (Λ_0 = 0), so ∫ exp(Λ_0) ∂μ = 1 (probability measure).
  3. {∃ n, A ≤ Λ_n} = {∃ n, exp(A) ≤ exp(Λ_n)} by strict monotonicity.
  4. For each N, ville_supermartingale_finite gives
       μ{∃ t ≤ N, exp(A) ≤ exp(Λ_t)} ≤ (∫ exp(Λ_0)) / exp(A) = exp(-A).
  5. Continuity from below (tendsto_measure_iUnion_atTop) lifts to ∞. -/
theorem error_rates
    [IsProbabilityMeasure μ]
    (S : SPRT X) (𝓕 : MeasureTheory.Filtration ℕ mΩ)
    (Y : ℕ → Ω → X)
    (_hY_adapted : ∀ i, Measurable[𝓕 i] (Y i))
    -- Under H_0 (data iid p₀), the per-sample LR-exponential has
    -- conditional mean ≤ 1: ∫ exp(logLR(Y_i)) | F_{i-1} = ∫ p₁/p₀ dp₀ = 1.
    (_hLR_under_H0 :
      ∀ i, ∫ ω, Real.exp (S.logLR (Y i ω)) ∂μ ≤ 1)
    -- The exp-LR process forms a non-negative supermartingale.
    (_hExpLR_super :
      Supermartingale
        (fun n ω => Real.exp (cumLogLR S Y n ω))
        𝓕 μ) :
    μ {ω | ∃ n, S.A ≤ cumLogLR S Y n ω} ≤ ENNReal.ofReal (Real.exp (-S.A)) := by
  -- exp(Λ_n) ≥ 0 always.
  have hf_nn : ∀ t (ω : Ω), (0 : ℝ) ≤ Real.exp (cumLogLR S Y t ω) :=
    fun t ω => Real.exp_nonneg _
  -- exp(A) > 0.
  have hexpA_pos : (0 : ℝ) < Real.exp S.A := Real.exp_pos S.A
  -- ∫ exp(Λ_0) ∂μ = 1  (Λ_0 = 0 by cumLogLR_zero, μ is probability).
  have hEf0 : ∫ ω, Real.exp (cumLogLR S Y 0 ω) ∂μ = 1 := by
    simp_rw [cumLogLR_zero, Real.exp_zero]
    simp
  -- 1 / exp(A) = exp(-A).
  have hquot : (1 : ℝ) / Real.exp S.A = Real.exp (-S.A) := by
    rw [Real.exp_neg, div_eq_mul_inv, one_mul]
  -- {∃ t ≤ N, A ≤ Λ_t} = {∃ t ≤ N, exp(A) ≤ exp(Λ_t)}.
  have hev_N_eq : ∀ N : ℕ,
      {ω : Ω | ∃ t : ℕ, t ≤ N ∧ S.A ≤ cumLogLR S Y t ω} =
        {ω : Ω | ∃ t : ℕ, t ≤ N ∧ Real.exp S.A ≤ Real.exp (cumLogLR S Y t ω)} := by
    intro N; ext ω; simp [Real.exp_le_exp]
  -- Finite-horizon Ville bound for each N.
  have hville_N : ∀ N : ℕ,
      μ {ω : Ω | ∃ t : ℕ, t ≤ N ∧ S.A ≤ cumLogLR S Y t ω} ≤
        ENNReal.ofReal (Real.exp (-S.A)) := by
    intro N
    rw [hev_N_eq N]
    have hv := ville_supermartingale_finite _hExpLR_super hf_nn hexpA_pos N
    rw [hEf0, hquot] at hv
    exact hv
  -- Continuity of measure from below: the infinite event is ⋃_N of finite ones.
  by_contra h_contra
  have hev_iUnion :
      {ω : Ω | ∃ n, S.A ≤ cumLogLR S Y n ω} =
        ⋃ N : ℕ, {ω : Ω | ∃ t : ℕ, t ≤ N ∧ S.A ≤ cumLogLR S Y t ω} := by
    ext ω; simp only [Set.mem_setOf_eq, Set.mem_iUnion]
    exact ⟨fun ⟨n, hn⟩ => ⟨n, n, le_refl n, hn⟩,
           fun ⟨_, n, _, hn⟩ => ⟨n, hn⟩⟩
  have hsets_mono :
      Monotone (fun N => {ω : Ω | ∃ t : ℕ, t ≤ N ∧ S.A ≤ cumLogLR S Y t ω}) :=
    fun N M hNM ω ⟨t, ht, hge⟩ => ⟨t, le_trans ht hNM, hge⟩
  have h_lim :
      Filter.Tendsto
        (fun N => μ {ω : Ω | ∃ t : ℕ, t ≤ N ∧ S.A ≤ cumLogLR S Y t ω})
        Filter.atTop
        (nhds (μ {ω | ∃ n, S.A ≤ cumLogLR S Y n ω})) := by
    rw [hev_iUnion]
    exact MeasureTheory.tendsto_measure_iUnion_atTop hsets_mono
  exact h_contra
    (le_of_tendsto_of_tendsto' h_lim tendsto_const_nhds hville_N)

/-- **Wald's approximation**: the practitioner-facing form.

To get type-I error ≤ α and type-II error ≤ β, set

  A = log((1-β)/α),    B = log(β/(1-α)).

This is a corollary of `error_rates` applied symmetrically under H_0
and H_1, with the algebra worked out for the standard error-rate
parameterization.

honest-sorry (2026-04-26): The `≤ α` conclusion requires a **two-measure**
argument that the current single-measure signature cannot support. The
complete proof has three layers:

Layer 1 — Ville under H_0:
  `μ₀{∃n, Λ_n ≥ A} ≤ exp(-A) · (1/1) = α/(1-β)`.
  This is already available via `error_rates` + `ville_supermartingale_finite`.

Layer 2 — Ville under H_1 (the *dual* lower-boundary bound):
  Under H_1 the process `exp(-Λ_n)` is a non-negative supermartingale
  (since under H_1 the log-LR is a martingale with positive mean, so
  its negative is a supermartingale). `ville_supermartingale_finite`
  applied to `exp(-Λ_n)` and threshold `exp(-B)` gives:
    `μ₁{∃n, Λ_n ≤ B} ≤ exp(B)`.
  With `B = log(β/(1-α))`, this gives `β_actual/(1-α_actual) ≤ β/(1-α)`.

Layer 3 — Wald 2×2 system (algebra, no measure theory):
  Let `a = α_actual = μ₀{∃n, Λ_n ≥ A}` and `b = β_actual`.
  From layers 1 and 2 and the boundary choices:
    a/(1-b) ≤ α/(1-β),    b/(1-a) ≤ β/(1-α).
  The unique solution to this system satisfying `a, b ∈ [0,1]` is
  `a ≤ α, b ≤ β` (Wald 1947, §3.3; verified by substitution and
  monotonicity).

Structural gap in current signature: the theorem has a single `μ`
(hypothesis distribution) and only the H_0 supermartingale. Closing
requires extending to two measures `μ₀ μ₁ : Measure Ω` and adding:
  `_hExpNegLR_super : Supermartingale (fun n ω => exp(-Σᵢ<n logLR(Yᵢω))) 𝓕 μ₁`
plus the H_1 integrability counterpart. The 2×2 algebra is pure `ℝ`
arithmetic once the two Ville bounds are in hand.

Planned signature extension (does not yet exist in this file):
  theorem wald_approximation_two_measure
    (μ₀ μ₁ : Measure Ω) [IsProbabilityMeasure μ₀] [IsProbabilityMeasure μ₁]
    ... (supermartingale for exp(Λ) under μ₀ + supermartingale for exp(-Λ) under μ₁)
    : μ₀{upper exit} ≤ α ∧ μ₁{lower exit} ≤ β -/
theorem wald_approximation
    [IsProbabilityMeasure μ]
    (𝓕 : MeasureTheory.Filtration ℕ mΩ)
    (Y : ℕ → Ω → X) (logLR : X → ℝ) (_hLR_mble : Measurable logLR)
    {α β : ℝ} (hα : 0 < α) (hα' : α < 1) (hβ : 0 < β) (_hβ' : β < 1)
    (_hY_adapted : ∀ i, Measurable[𝓕 i] (Y i))
    (_hLR_under_H0 : ∀ i, ∫ ω, Real.exp (logLR (Y i ω)) ∂μ ≤ 1)
    (_hExpLR_super :
      Supermartingale
        (fun n ω => Real.exp ((Finset.range n).sum
          (fun i => logLR (Y i ω))))
        𝓕 μ) :
    μ {ω | ∃ n, Real.log ((1 - β) / α)
                  ≤ (Finset.range n).sum (fun i => logLR (Y i ω))}
      ≤ ENNReal.ofReal α := by
  -- honest-sorry: single-measure signature only yields ≤ α/(1-β) via Ville.
  -- Closing to ≤ α requires two-measure extension + Wald 2×2 algebra.
  -- See sharpened closure plan in docstring above.
  sorry

/-- **Wald-Wolfowitz optimality**: SPRT minimizes expected sample size.

Among all sequential tests `T = (σ, δ)` (a stopping time σ + a
{H_0, H_1}-valued decision δ) with type-I error ≤ α and type-II error
≤ β, Wald's SPRT (with boundaries chosen via `wald_approximation`)
achieves

  E[τ_T | H_i] ≥ E[τ_SPRT | H_i],   i ∈ {0, 1}.

This is the original Wald-Wolfowitz 1948 optimality theorem.

honest-sorry (2026-04-26): Aristotle-class. The original proof appears in
  Wald, A. & Wolfowitz, J. (1948). Optimum character of the sequential
  probability ratio test. *Ann. Math. Statist.* 19(3), 326–339.
The standard textbook treatment is Lehmann & Romano (2005),
*Testing Statistical Hypotheses*, 3rd ed., §3.7 (pp. 90–95), which
restates the argument via path-measure Radon-Nikodym and Bayes-minimax
duality.  A modern presentation using game-theoretic probability is in
Ramdas, Grünwald, Vovk & Shafer (2023), §6.

Three Mathlib v4.28 gaps block a kernel-checked proof:

  (1) Path-measure Radon-Nikodym derivative. The H_0 and H_1 path
      measures on `(ℕ → Ω)` arising from iid product extensions of
      `p₀` and `p₁` need a tractable `rnDeriv` chain identity:
        d(P₁^n)/d(P₀^n) = ∏_{i<n} (p₁(Xᵢ)/p₀(Xᵢ)) = exp(Λ_n).
      Mathlib's `MeasureTheory.Measure.rnDeriv` supports this for
      finite products but the *infinite-product* path measure requires
      `MeasureTheory.Measure.pi` + a kernel-based construction. The
      required chain rule for infinite products is not in v4.28.

  (2) Minimax characterization of optimal sequential tests. The
      proof reduces ESS-minimality to: for any test T with the same
      error rates, the expected log-likelihood ratio at stopping time
      satisfies E_{H_i}[Λ_{σ_T}] ≥ E_{H_i}[Λ_{τ_SPRT}]. This
      requires a minimax / Bayes-envelope argument over the class of
      level-α tests. The relevant tool —
      `MeasureTheory.Measure.integral_rnDeriv_le` or a sequential
      analogue — is not available in v4.28.

  (3) Inf-integral interchange for stopping times. The ESS lower
      bound is expressed as `inf_{σ ∈ 𝒯} ∫ σ dμᵢ`. Pulling the `inf`
      inside the integral over a tight family of level-α tests requires
      a dominated-convergence + compactness argument on the space of
      stopping times equipped with a weak topology. This is not
      formalised in Mathlib v4.28.

Industrial closure path: follow the constructive proof sketch in
Ferguson (1967), *Mathematical Statistics: A Decision-Theoretic
Approach*, Chapter 8, which proves Wald-Wolfowitz via Bayes risk
minimization + an exchange lemma. The exchange lemma (Lemma 8.4.2 in
Ferguson) is the key technical piece; it reduces the interchange in (3)
to a finite-dimensional convexity argument. Estimated Lean proof length:
~400 lines, requiring (1) and (2) as sub-modules first. -/
theorem wald_wolfowitz_optimal
    [IsProbabilityMeasure μ]
    (S : SPRT X) (𝓕 : MeasureTheory.Filtration ℕ mΩ)
    (Y : ℕ → Ω → X)
    -- Any other sequential test = (stopping time σ, decision δ).
    (σ : Ω → ℕ)
    (_hσ : MeasureTheory.IsStoppingTime 𝓕 (liftStoppingTime σ))
    (δ : Ω → Bool) (_hδ_mble : Measurable δ)
    -- σ achieves the same error rates under H_0 and H_1.
    {α β : ℝ}
    (_h_typeI  : μ {ω | δ ω = true}  ≤ ENNReal.ofReal α)
    (_h_typeII : μ {ω | δ ω = false} ≤ ENNReal.ofReal β)
    -- Wald-approximation boundaries.
    (_hA : S.A = Real.log ((1 - β) / α))
    (_hB : S.B = Real.log (β / (1 - α)))
    -- SPRT stopping time (the function whose expectation is bounded).
    -- For optimality the theorem only needs `sprtStop` to be the
    -- first-exit time of the LR from `(B, A)`; this is captured
    -- abstractly by the per-ω characterizing predicate below.
    (sprtStop : Ω → ℕ)
    (_hsprtStop : ∀ ω, S.A ≤ cumLogLR S Y (sprtStop ω) ω
                       ∨ cumLogLR S Y (sprtStop ω) ω ≤ S.B)
    (_hτ_int : Integrable (fun ω => (sprtStop ω : ℝ)) μ) :
    ∫ ω, (sprtStop ω : ℝ) ∂μ ≤ ∫ ω, (σ ω : ℝ) ∂μ := by
  -- honest-sorry: Aristotle-class, three Mathlib v4.28 gaps (see docstring).
  sorry

/-- **Expected sample size** in closed form.

Under H_0 the SPRT stopping time has expectation

  E[τ | H_0] ≈ ((1-β)·B + β·A) / (-D(p_0 ‖ p_1))

where `D(p_0 ‖ p_1)` is the Kullback-Leibler divergence and α, β are
the achieved type-I and type-II rates. The "≈" is exact modulo overshoot
at the boundary, which is `O(1)` in the small-error regime.

honest-sorry (2026-04-26): Three blocking prerequisites:

  (1) `wald_identity` (WaldIdentity.lean ~line 102) is sorry'd. The
      proof path applies Wald's identity to the centered process
      `Λ_n + D_p0_p1 * n` (which is a martingale under H_0 because
      E[logLR(Xᵢ)] = -D_p0_p1), giving E[Λ_τ + D_p0_p1 * τ] = 0,
      hence E[Λ_τ] = -D_p0_p1 · E[τ], and finally E[τ] = E[Λ_τ] /
      (-D_p0_p1). Once `wald_identity` is closed, this step is a
      1-line rewrite.

  (2) Missing boundary-exit hypothesis `_hExit`:
        _hExit : ∫ ω, cumLogLR S Y (sprtStop ω) ω ∂μ
                   = (1 - β) * S.B + β * S.A
      This is the statement "the expected value of Λ at stopping equals
      a weighted combination of the two boundaries, weighted by the
      (H_0) probability of exiting at each boundary."  Precisely:
      `P_{H_0}(exit via A) = β` (type-II error) and
      `P_{H_0}(exit via B) = 1 - β` (test accepts H_0 correctly).
      This is not derivable from the current hypotheses; it must be
      added as an explicit assumption. Proposed addition to signature:
        (_hExit : ∫ ω, cumLogLR S Y (sprtStop ω) ω ∂μ
                    = (1 - β) * S.B + β * S.A)

  (3) `wald_identity` itself requires the centered process to be a
      martingale (`_hX_mart_centered` in WaldIdentity.lean). Wiring
      this from the iid structure + KL hypothesis `_hKL` requires
      constructing the conditional-expectation identity
        E[logLR(Yᵢ) | F_{i-1}] = -D_p0_p1 a.s.
      for independent (not merely uncorrelated) increments. This is
      an `iIndepFun`-to-martingale bridge lemma, not yet in Mathlib v4.28.

Proof sketch once prerequisites close:
  1. Let `M_n = Λ_n + D_p0_p1 * n`. By (3), `M_n` is a martingale.
  2. Apply `wald_identity` at `m = 0` to get `E[M_{τ}] = 0`.
  3. Unfold: `E[Λ_τ] = -D_p0_p1 · E[τ]`.
  4. Substitute `_hExit`: `E[Λ_τ] = (1-β)·B + β·A`.
  5. Solve for E[τ] = ((1-β)·B + β·A) / (-D_p0_p1). QED. -/
theorem expected_sample_size
    [IsProbabilityMeasure μ]
    (S : SPRT X) (𝓕 : MeasureTheory.Filtration ℕ mΩ)
    (Y : ℕ → Ω → X) (D_p0_p1 : ℝ) (_hD_pos : 0 < D_p0_p1)
    -- Under H_0, the per-step expected log-LR is the negative KL divergence
    -- from p_0 to p_1.
    (_hKL : ∀ i, ∫ ω, S.logLR (Y i ω) ∂μ = -D_p0_p1)
    (_hY_adapted : ∀ i, Measurable[𝓕 i] (Y i))
    {α β : ℝ} (_hα : 0 < α) (_hβ : 0 < β)
    -- SPRT stopping time (abstract; a real construction would use
    -- `Nat.find` on the boundary-exit predicate).
    (sprtStop : Ω → ℕ)
    (_hτ_int : Integrable (fun ω => (sprtStop ω : ℝ)) μ) :
    ∫ ω, (sprtStop ω : ℝ) ∂μ
      = ((1 - β) * S.B + β * S.A) / (-D_p0_p1) := by
  -- honest-sorry (1): wald_identity (WaldIdentity.lean ~102) is sorry'd.
  -- honest-sorry (2): missing hypothesis
  --   _hExit : ∫ ω, cumLogLR S Y (sprtStop ω) ω ∂μ = (1-β)*S.B + β*S.A.
  sorry

end SPRT

end Pythia
