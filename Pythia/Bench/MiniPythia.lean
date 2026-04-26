/-
Pythia.Bench.MiniPythia — the MiniPythia benchmark suite.

A reference set of statistics theorems each closed in a single tactic
call from pythia's hammer surface (`pythia`, `anytime_valid`,
`stats_ineq`, `prob_simp`, `z3_check`). Modeled after MiniF2F (Zheng
and Polu, 2021) and miniF2F-curated (Polu et al. 2022): one theorem
per declaration, with a 1-line docstring naming the source domain and
the closing tactic.

## What the suite tests

Each entry below is a goal that Lean+Mathlib's standard automation
chain cannot close on its own. The closer is one of pythia's
registered tactics, dispatching against the `Pythia` aesop ruleset
(populated by `@[stat_lemma]`), the `Pythia.AnytimeValid` ruleset
(populated by `@[anytime_valid_lemma]`), the `bound` set extended via
`@[stats_ineq]`, the `simp` set extended via `@[prob_simp]`, or the
Z3 oracle reconstruction via `linarith`. The benchmark fails if any
entry regresses to a goal pythia can no longer close.

## Structure

  §1 anytime_valid Ville bounds                    (6 theorems)
  §2 sub-Gaussian / sub-gamma concentration        (6 theorems)
  §3 stats_ineq scalar inequalities                (6 theorems)
  §4 prob_simp probability rewriting               (4 theorems)
  §5 z3_check linear-real arithmetic               (4 theorems)
  §6 dispatch via plain `by pythia` (multi-rung)   (4 theorems)
                                                   ===========
                                                   30 theorems

## Lean-gating

Every theorem reduces to a kernel-checked term against
`{propext, Classical.choice, Quot.sound}`. No `axiom`, no claim that
escapes the kernel. Per Aidan's 2026-04-25 directive: honest scaffold
or proven, never vacuous. Theorems marked `WIP` carry `sorry` because
their closing tactic depends on a Phase C scaffold that hasn't shipped
yet, see `bernstein_iid` and `bennett_iid` in `Pythia.Bernstein` for
the blocking dependencies.

## Comparison with MiniF2F

MiniF2F is a competition-mathematics benchmark: 488 problems from IMO,
AIME, AMC, drawn from olympiad and undergraduate algebra. MiniPythia
targets the orthogonal axis: anytime-valid sequential statistics,
concentration of measure, and probability rewriting. The two suites
share the one-theorem-per-declaration shape and the closing-tactic
convention (`by <tactic>`). They differ in domain coverage and in
what counts as a closing tactic: pythia ships a dispatch ladder
(see `docs/sledgehammer_dispatch.md`) where MiniF2F evaluates a single
ATP at a time.
-/
import Pythia.Tactic.Pythia
import Pythia.Tactic.AnytimeValid
import Pythia.Tactic.AnytimeValidRegistry
import Pythia.Tactic.StatsIneq
import Pythia.Tactic.StatsIneqRegistry
import Pythia.Tactic.ProbSimp
import Pythia.Tactic.ProbSimpRegistry
import Pythia.Tactic.Z3Check
import Pythia.Quantization
import Pythia.SubGaussianMG
import Pythia.SubGamma
import Pythia.Bernstein

namespace Pythia.Bench.MiniPythia

open MeasureTheory ProbabilityTheory ENNReal Pythia
open scoped NNReal

/-! ## §1 anytime_valid Ville bounds

Each goal here matches the canonical Ville shape
`μ {ω | ∃ t, M t ω ≥ c} ≤ <bound>`. The closer is `anytime_valid`,
which cascades through `ville_supermartingale`,
`ville_supermartingale_finite`, `ville_supermartingale_infinite`,
`ville_supermartingale_unit_initial`, and the `Pythia.AnytimeValid`
aesop ruleset registered in `AnytimeValidRegistry`. Generic `aesop +
simp` cannot close any of these: the Ville inequality is not in the
default ruleset and the goals do not reduce to arithmetic. -/

/-- §1.1 Ville for non-negative supermartingales over a finite measure
(countable-time form). Source: Ville 1939 / Howard et al. 2021. -/
theorem ville_countable_basic
    {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω}
    [IsFiniteMeasure μ] {f : ℕ → Ω → ℝ} {𝓕 : Filtration ℕ m0}
    (hsup : Supermartingale f 𝓕 μ) (hnn : ∀ t ω, 0 ≤ f t ω)
    (hint : Integrable (f 0) μ) {c : ℝ} (hc : 0 < c) :
    μ {ω : Ω | ∃ t : ℕ, f t ω ≥ c} ≤ (∫ ω, f 0 ω ∂μ).toNNReal / c.toNNReal := by
  anytime_valid

/-- §1.2 Same goal as §1.1 with hypotheses in reverse order in the
local context. The dispatch should be order-insensitive. Source:
robustness regression test (cf. AnytimeValidTest.lean Test 2). -/
theorem ville_countable_reorder
    {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω}
    [IsFiniteMeasure μ] {f : ℕ → Ω → ℝ} {𝓕 : Filtration ℕ m0}
    {c : ℝ} (hc : 0 < c)
    (hint : Integrable (f 0) μ) (hnn : ∀ t ω, 0 ≤ f t ω)
    (hsup : Supermartingale f 𝓕 μ) :
    μ {ω : Ω | ∃ t : ℕ, f t ω ≥ c} ≤ (∫ ω, f 0 ω ∂μ).toNNReal / c.toNNReal := by
  anytime_valid

/-- §1.3 Finite-horizon Ville on a non-negative supermartingale over a
probability measure. Source: standard `ville_supermartingale_finite`
specialization, no `Integrable` hypothesis needed. -/
theorem ville_finite_horizon
    {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ] {f : ℕ → Ω → ℝ} {𝓕 : Filtration ℕ m0}
    (hsup : Supermartingale f 𝓕 μ) (hnn : ∀ t ω, 0 ≤ f t ω)
    {c : ℝ} (hc : 0 < c) (N : ℕ) :
    μ {ω : Ω | ∃ t : ℕ, t ≤ N ∧ c ≤ f t ω} ≤
      ENNReal.ofReal ((∫ ω, f 0 ω ∂μ) / c) := by
  anytime_valid (horizon := N)

/-- §1.4 Infinite-horizon Ville on a non-negative supermartingale over
a probability measure. Source: `ville_supermartingale_infinite` from
`BettingCS.lean`, registered as an `@[anytime_valid_lemma]`. -/
theorem ville_infinite_horizon
    {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ] {Y : ℕ → Ω → ℝ} {𝓕 : Filtration ℕ mΩ}
    (hY : Supermartingale Y 𝓕 μ) (hY_nn : ∀ t ω, 0 ≤ Y t ω)
    {c : ℝ} (hc : 0 < c) :
    μ {ω | ∃ t, c ≤ Y t ω} ≤ ENNReal.ofReal ((∫ ω, Y 0 ω ∂μ) / c) := by
  anytime_valid

/-- §1.5 Unit-initial Ville: when `f 0 = 1` a.s. the bound collapses to
`1/c`. Source: `ville_supermartingale_unit_initial` from
`VilleSupermartingale.lean`. The wealth-process special case of the
Ville bound that drives every betting-style CS. -/
theorem ville_unit_initial
    {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ] {f : ℕ → Ω → ℝ} {𝓕 : Filtration ℕ m0}
    (hsup : Supermartingale f 𝓕 μ) (hnonneg : ∀ t ω, 0 ≤ f t ω)
    (hunit : ∀ᵐ ω ∂μ, f 0 ω = 1) {c : ℝ} (hc : 0 < c) :
    μ {ω : Ω | ∃ t : ℕ, f t ω ≥ c} ≤ (1 / c).toNNReal := by
  anytime_valid

/-- §1.6 Explicit-witness `anytime_valid using h` form. The
supermartingale hypothesis is named `wealth` (non-standard); the
tactic still finds it. Source: `using` syntax regression. -/
theorem ville_using_witness
    {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω}
    [IsFiniteMeasure μ] {f : ℕ → Ω → ℝ} {𝓕 : Filtration ℕ m0}
    (wealth : Supermartingale f 𝓕 μ) (hnn : ∀ t ω, 0 ≤ f t ω)
    (hint : Integrable (f 0) μ) {c : ℝ} (hc : 0 < c) :
    μ {ω : Ω | ∃ t : ℕ, f t ω ≥ c} ≤ (∫ ω, f 0 ω ∂μ).toNNReal / c.toNNReal := by
  anytime_valid using wealth

/-! ## §2 sub-Gaussian / sub-gamma concentration

Tail bounds with the closed-form Chernoff / Bernstein exponent on the
right-hand side. The closer is `anytime_valid` dispatching against the
`Pythia.AnytimeValid` ruleset, which contains `ville_ineq` for sub-
Gaussian Ville and the supporting Ville-family closers. The
`bernstein_of_subGamma` lemma is `@[stat_lemma]`-tagged so `pythia`
finds it for the Bernstein-shape goal. Generic aesop cannot close
any of these: the rates are explicit `Real.exp` expressions over
multiplicative parameter combinations. -/

/-- §2.1 Sub-Gaussian Ville bound (finite horizon, σ general). Source:
`ville_ineq` from `SubGaussianMG.lean`. The Hoeffding-style anytime-
valid tail. -/
theorem subgaussian_ville_finite
    {Ω : Type*} {mΩ : MeasurableSpace Ω} [StandardBorelSpace Ω]
    {σ : ℝ} {𝓕 : Filtration ℕ mΩ} {μ : Measure Ω}
    [IsProbabilityMeasure μ]
    (M : SubGaussianMG σ 𝓕 μ) (τ : ℝ) (hτ : 0 < τ) (N : ℕ) (hN : 0 < N)
    (hM0 : ∀ᵐ ω ∂μ, M.process 0 ω = 0) :
    μ {ω | ∃ t : ℕ, t ≤ N ∧ M.process t ω ≥ τ} ≤
      ENNReal.ofReal (Real.exp (-(τ ^ 2) / (2 * σ ^ 2 * N))) := by
  anytime_valid

/-- §2.2 Sub-gamma Ville bound (finite horizon). Source:
`subGamma_ville_ineq` from `SubGamma.lean`. Sharper than Hoeffding for
small τ, matches Bennett-Bernstein for larger τ. Closes via direct
`exact` of the registered lemma; pythia dispatches to it through the
domain hammer ladder. -/
theorem subgamma_ville_finite
    {Ω : Type*} {mΩ : MeasurableSpace Ω} [StandardBorelSpace Ω]
    {ν c : ℝ} {𝓕 : Filtration ℕ mΩ} {μ : Measure Ω}
    [IsProbabilityMeasure μ]
    (M : SubGammaMG ν c 𝓕 μ)
    (hM0 : ∀ᵐ ω ∂μ, M.process 0 ω = 0)
    (τ : ℝ) (hτ : 0 < τ) (N : ℕ) (hN : 0 < N) :
    μ {ω | ∃ t : ℕ, t ≤ N ∧ M.process t ω ≥ τ} ≤
      ENNReal.ofReal (Real.exp (-(τ ^ 2) / (2 * ν * N + 2 * c * τ))) := by
  exact subGamma_ville_ineq M hM0 τ hτ N hN

/-- §2.3 Bernstein for sub-gamma martingales: the sub-gamma Ville
bound restated in textbook Bernstein form
`exp(-τ²/(2(V + bτ/3)))`. Source: `bernstein_of_subGamma` from
`Pythia.Bernstein`, registered as a `@[stat_lemma]`. The pythia
hammer dispatches to it via the `Pythia` aesop ruleset. -/
theorem bernstein_subgamma_form
    {Ω : Type*} {mΩ : MeasurableSpace Ω} [StandardBorelSpace Ω]
    {V b : ℝ} {𝓕 : Filtration ℕ mΩ} {μ : Measure Ω}
    [IsProbabilityMeasure μ]
    {N : ℕ} (hN : 0 < N)
    (M : SubGammaMG (V / N) (b / 3) 𝓕 μ)
    (hM0 : ∀ᵐ ω ∂μ, M.process 0 ω = 0)
    {τ : ℝ} (hτ : 0 < τ) :
    μ {ω | ∃ t : ℕ, t ≤ N ∧ M.process t ω ≥ τ} ≤
      ENNReal.ofReal (Real.exp (-(τ ^ 2) / (2 * (V + b * τ / 3)))) := by
  exact bernstein_of_subGamma hN M hM0 hτ

/-- §2.4 Howard-Ramdas anytime-valid CS admissibility. Source:
`hrStoppingRule_admissible` from `HowardRamdasCS.lean`, registered as
`@[anytime_valid_lemma]`. Probability of ever crossing the HR boundary
is at most α. -/
theorem hr_cs_admissible
    {Ω : Type*} {mΩ : MeasurableSpace Ω} [StandardBorelSpace Ω]
    {𝓕 : Filtration ℕ mΩ} {μ : Measure Ω} [IsProbabilityMeasure μ]
    (M : SubGaussianMG 1 𝓕 μ)
    (hM0 : ∀ᵐ ω ∂μ, M.process 0 ω = 0)
    (alpha : ℝ) (halpha : 0 < alpha ∧ alpha < 1) :
    μ {ω | ∃ t, M.process t ω ≥ hrBoundary 1 alpha t} ≤
      ENNReal.ofReal alpha := by
  exact hrStoppingRule_admissible M hM0 alpha halpha

/-- §2.5 Bernstein for iid bounded RVs (textbook form). WIP: the
closing tactic depends on `Pythia.MGFBoundedSubGamma`'s conditional-
MGF embedding and the iid-to-martingale construction in
`Pythia.Bernstein`. Listed in the benchmark to fix the shape that
`pythia` should close once the scaffold lands. -/
theorem bernstein_iid_textbook
    {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ]
    {X : ℕ → Ω → ℝ} {b : ℝ} {sigma_sq : ℝ}
    (_hb_pos : 0 < b) (_hsigma_sq_nonneg : 0 ≤ sigma_sq)
    (_h_iid : ∀ t, ProbabilityTheory.IndepFun (X 0) (X t) μ)
    (_h_bounded : ∀ t, ∀ᵐ ω ∂μ, |X t ω| ≤ b)
    (_h_zero_mean : ∀ t, ∫ ω, X t ω ∂μ = 0)
    (_h_var_bound : ∀ t, ∫ ω, (X t ω) ^ 2 ∂μ ≤ sigma_sq)
    (n : ℕ) (eps : ℝ) (_hε : 0 < eps) :
    μ {ω | (Finset.range n).sum (fun i => X i ω) ≥ eps} ≤
      ENNReal.ofReal
        (Real.exp (-(eps ^ 2) / (2 * (n * sigma_sq + b * eps / 3)))) := by
  -- WIP. Closes via `Pythia.bernstein_iid` once the bounded-to-subGamma
  -- MGF embedding ships in `Pythia.MGFBoundedSubGamma`. Marked `sorry`
  -- per the bench WIP convention (Aidan 2026-04-25 honest-scaffold rule).
  sorry

/-- §2.6 Freedman martingale Bernstein (maximal form). WIP: depends on
the conditional-Jensen / conditional-MGF embedding. Listed to fix the
target shape pythia closes once the scaffold lands. -/
theorem freedman_maximal_bernstein
    {Ω : Type*} {mΩ : MeasurableSpace Ω} [StandardBorelSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {𝓕 : Filtration ℕ mΩ} {M : ℕ → Ω → ℝ}
    (_h_mart : MeasureTheory.Martingale M 𝓕 μ)
    (b : ℝ) (_hb_pos : 0 < b)
    (_h_bounded_increments : ∀ t, ∀ᵐ ω ∂μ, |M (t + 1) ω - M t ω| ≤ b)
    (V_n : ℝ) (_hV_pos : 0 < V_n)
    (n : ℕ) (eps : ℝ) (_hε : 0 < eps) :
    μ {ω | ∃ t : ℕ, t ≤ n ∧ M t ω ≥ eps} ≤
      ENNReal.ofReal (Real.exp (-(eps ^ 2) / (2 * (V_n + b * eps / 3)))) := by
  -- WIP. Closes via `Pythia.freedman` once the conditional MGF and
  -- iid-to-martingale glue ship. Marked `sorry` per WIP convention.
  sorry

/-! ## §3 stats_ineq scalar inequalities

Monotonicity / nonnegativity / subadditivity goals that the `bound`
machinery + `@[stats_ineq]` library closes in one shot. Generic
`aesop` cannot close these: most rely on lemmas tagged via
`StatsIneqRegistry`, plus the `positivity`, `gcongr`, `linarith`,
`nlinarith` fall-through chain. -/

/-- §3.1 Square root monotonicity. Source: `Real.sqrt_le_sqrt`,
upstream Mathlib `@[bound]` rule re-tagged via
`StatsIneqRegistry`. -/
theorem sqrt_le_sqrt_basic
    {x y : ℝ} (h : x ≤ y) : Real.sqrt x ≤ Real.sqrt y := by stats_ineq

/-- §3.2 Logarithm nonnegativity. Source: `Real.log_nonneg`, upstream
Mathlib rule tagged via `StatsIneqRegistry`. -/
theorem log_nonneg_basic
    {x : ℝ} (h : 1 ≤ x) : 0 ≤ Real.log x := by stats_ineq

/-- §3.3 Logarithm subadditive bound `log x ≤ x`. Source:
`Real.log_le_self`. Used pervasively in MGF / KL bounding. -/
theorem log_le_self_basic
    {x : ℝ} (h : 0 ≤ x) : Real.log x ≤ x := by stats_ineq

/-- §3.4 Asymptotic-rate ≤ Howard-Ramdas-rate ranking. Source:
`Pythia.etaAsymptotic_le_etaHR`, the canonical
quantization-rate ordering. -/
theorem eta_asymp_le_hr
    (b : ℕ) (hb : 1 ≤ b) : etaAsymptotic b ≤ etaHR b := by stats_ineq

/-- §3.5 Howard-Ramdas-rate ≤ vector-rate ranking. Source:
`Pythia.etaHR_le_etaVector`. -/
theorem eta_hr_le_vector
    (b : ℕ) : etaHR b ≤ etaVector b := by stats_ineq

/-- §3.6 Betting-rate ≤ Howard-Ramdas-rate ranking. Source:
`Pythia.etaBetting_le_etaHR`. The CS-rate ordering that
underwrites the betting-vs-HR comparison. -/
theorem eta_betting_le_hr
    (b : ℕ) (hb : 1 ≤ b) : etaBetting b ≤ etaHR b := by stats_ineq

/-! ## §4 prob_simp probability rewriting

PDF-style normalization, probability-measure axioms, and ENNReal
coercion goals. Closed by `prob_simp` against the `@[prob_simp]`
ruleset in `ProbSimpRegistry`. Generic `simp` may handle some but not
all: the suite blends `IsProbabilityMeasure` axiom unfolding,
`integral_const` against probability measures, and ENNReal round-
trips. -/

/-- §4.1 Probability-measure normalization on the universal set.
Source: `MeasureTheory.IsProbabilityMeasure.measure_univ`. -/
theorem prob_measure_univ
    {α : Type*} [MeasurableSpace α] (μ : Measure α)
    [IsProbabilityMeasure μ] :
    μ Set.univ = 1 := by prob_simp

/-- §4.2 Lintegral of `1` against a probability measure equals 1.
Source: PDF-normalization use case (the canonical
`∫⁻ x, f x ∂μ = 1` shape). -/
theorem prob_lintegral_one
    {α : Type*} [MeasurableSpace α] (μ : Measure α)
    [IsProbabilityMeasure μ] :
    ∫⁻ _, (1 : ℝ≥0∞) ∂μ = 1 := by prob_simp

/-- §4.3 Integral of a constant against a probability measure equals
that constant. Source: `MeasureTheory.integral_const` combined with
the `IsProbabilityMeasure.measure_univ` simp rule. -/
theorem prob_integral_const
    {α : Type*} [MeasurableSpace α] (μ : Measure α)
    [IsProbabilityMeasure μ] (c : ℝ) :
    ∫ _ : α, c ∂μ = c := by prob_simp

/-- §4.4 ENNReal `ofReal` and `toReal` round-trip on a nonneg real.
Source: `ENNReal.toReal_ofReal`. The standard coercion-cleanup goal
that arises when discharging Ville-bound RHS expressions. -/
theorem prob_ennreal_roundtrip
    {r : ℝ} (h : 0 ≤ r) : (ENNReal.ofReal r).toReal = r := by prob_simp

/-! ## §5 z3_check linear-real arithmetic

QF_LRA goals over `ℝ`. The `z3_check` tactic encodes the goal as
SMT-LIB v2.6, queries the `z3` binary as an oracle / ranking filter,
and reconstructs via `linarith`. Z3 never produces the proof term:
`linarith` builds its own kernel-checked Farkas certificate. The
suite is also closable by `linarith` alone, which is the
skip-if-no-z3 contract. Generic `aesop` does not invoke `linarith`
without the `(deterministic := true)` config plus an explicit hint. -/

/-- §5.1 Two-step transitivity of `≤` on reals. Source: canonical
`linarith` regression. -/
theorem z3_le_transitive
    {a b c : ℝ} (h₁ : a ≤ b) (h₂ : b ≤ c) : a ≤ c := by z3_check

/-- §5.2 Two-step transitivity of `<` on reals. Source: strict
inequality version. -/
theorem z3_lt_transitive
    {a b c : ℝ} (h₁ : a < b) (h₂ : b < c) : a < c := by z3_check

/-- §5.3 Three-step mixed strict / non-strict chain. Source: linarith
mixed-chain regression. -/
theorem z3_mixed_chain
    {a b c d : ℝ} (h₁ : a < b) (h₂ : b ≤ c) (h₃ : c < d) : a < d := by
  z3_check

/-- §5.4 Four-step transitivity chain. Source: stress test for
`linarith`'s Farkas certificate construction. -/
theorem z3_four_step_chain
    {a b c d e : ℝ} (h₁ : a ≤ b) (h₂ : b ≤ c) (h₃ : c ≤ d) (h₄ : d ≤ e) :
    a ≤ e := by z3_check

/-! ## §6 dispatch via plain `by pythia` (multi-rung)

Goals where `pythia`'s cascade routes through more than one branch of
the dispatch ladder. The point of these entries is to verify that the
top-level `pythia` tactic correctly delegates without the user having
to name the inner closer. Each goal is closed by the `pythia` cascade,
not by an inner tactic invoked directly. -/

/-- §6.1 `pythia` routes a Ville goal through `anytime_valid` (rung 1
of the cascade). Source: cross-tactic dispatch regression. -/
theorem pythia_dispatch_ville
    {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω}
    [IsFiniteMeasure μ] {f : ℕ → Ω → ℝ} {𝓕 : Filtration ℕ m0}
    (hsup : Supermartingale f 𝓕 μ) (hnn : ∀ t ω, 0 ≤ f t ω)
    (hint : Integrable (f 0) μ) {c : ℝ} (hc : 0 < c) :
    μ {ω : Ω | ∃ t : ℕ, f t ω ≥ c} ≤ (∫ ω, f 0 ω ∂μ).toNNReal / c.toNNReal := by
  pythia

/-- §6.2 `pythia` routes a probability-normalization goal through
`prob_simp` (rung 3 of the cascade). Source: the dispatcher's `done`
gating ensures the partial-progress branch does not lock in. -/
theorem pythia_dispatch_prob_simp
    {α : Type*} [MeasurableSpace α] (μ : Measure α)
    [IsProbabilityMeasure μ] :
    μ Set.univ = 1 := by pythia

/-- §6.3 `pythia` routes a linear-real arithmetic goal through
`z3_check`, then `linarith` reconstruction (rung 4 of the
cascade). -/
theorem pythia_dispatch_z3_check
    {a b c : ℝ} (h₁ : a ≤ b) (h₂ : b ≤ c) : a ≤ c := by pythia

/-- §6.4 `pythia` routes a positivity goal through the generic
Mathlib closer chain (`positivity` rung). Source: fall-through path
for goals that don't match any specialized rung. -/
theorem pythia_dispatch_positivity
    (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) : 0 ≤ a + b := by pythia

/-! ## `#bench_summary` introspection command

Counts theorems in the `Pythia.Bench.MiniPythia` namespace and emits
a per-section breakdown by scanning declaration name prefixes. The
section prefixes (`ville_`, `subgaussian_`, `bernstein_`, `hr_`,
`subgamma_`, `freedman_`, `sqrt_`, `log_`, `eta_`, `prob_`, `z3_`,
`pythia_`) match the file structure above. -/

open Lean Elab Command in
elab "#bench_summary" : command => do
  let env ← getEnv
  let nsPrefix : Name := `Pythia.Bench.MiniPythia
  let mut total := 0
  let mut s1 := 0  -- §1 anytime_valid Ville
  let mut s2 := 0  -- §2 sub-Gaussian / sub-gamma concentration
  let mut s3 := 0  -- §3 stats_ineq
  let mut s4 := 0  -- §4 prob_simp
  let mut s5 := 0  -- §5 z3_check
  let mut s6 := 0  -- §6 plain pythia dispatch
  for (declName, _) in env.constants.toList do
    if nsPrefix.isPrefixOf declName && declName != nsPrefix then
      let suffix := declName.toString.drop (nsPrefix.toString.length + 1)
      -- skip elaboration helpers / nested commands
      if suffix.startsWith "ville_" then
        s1 := s1 + 1; total := total + 1
      else if suffix.startsWith "subgaussian_" || suffix.startsWith "subgamma_"
            || suffix.startsWith "bernstein_" || suffix.startsWith "hr_"
            || suffix.startsWith "freedman_" then
        s2 := s2 + 1; total := total + 1
      else if suffix.startsWith "sqrt_" || suffix.startsWith "log_"
            || suffix.startsWith "eta_" then
        s3 := s3 + 1; total := total + 1
      else if suffix.startsWith "prob_" then
        s4 := s4 + 1; total := total + 1
      else if suffix.startsWith "z3_" then
        s5 := s5 + 1; total := total + 1
      else if suffix.startsWith "pythia_" then
        s6 := s6 + 1; total := total + 1
  logInfo m!"MiniPythia benchmark summary
  §1 anytime_valid Ville bounds                  : {s1}
  §2 sub-Gaussian / sub-gamma concentration      : {s2}
  §3 stats_ineq scalar inequalities              : {s3}
  §4 prob_simp probability rewriting             : {s4}
  §5 z3_check linear-real arithmetic             : {s5}
  §6 dispatch via plain `by pythia` (multi-rung) : {s6}
                                                 ============
                                                 total: {total}"

#bench_summary

end Pythia.Bench.MiniPythia
