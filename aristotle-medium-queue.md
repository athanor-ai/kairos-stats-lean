# Aristotle Medium-Tier Dispatch Queue : ATH-1267

**Scope**: general applied math, Aristotle-eligible per Aidan ts 1778764427 NDA-rule (no Annapurna / Trainium / Neuron content).

**Dispatch policy**: per `feedback_pythia_rules` : Aristotle is *last resort* after sonnet/kairos/own-proof attempt. Each target below has been pre-screened: easy-tier closures (algebraic + Real.log/exp manipulation) handled locally by sonnet subagents in batches 1-3 (33 closures on `research/ath-1267-fin-easy-batch`).

**Both accounts in parallel**: `ARISTOTLE_API_KEY_RESEARCH` + `ARISTOTLE_API_KEY_CTO` available on Azure-VM research workspace. Submit-and-watch per `feedback_aristotle_patience_1h_gate` : 1h+ stalls normal.

---

## Target 1 : Black-Scholes call-price intrinsic upper bound

**File target**: `Pythia/Finance/BlackScholesUpperBound.lean` (new)

**Statement**:
```lean
theorem callPayoff_le_spot {S K T r : ℝ} (hS : 0 ≤ S) (hK : 0 ≤ K) (hT : 0 ≤ T) (hr : 0 ≤ r) :
    callPayoff S K T r ≤ S
```

**Why medium-tier**: needs `max (S - K) 0 ≤ S` (which requires `0 ≤ K`) combined with `exp(-r·T) ≤ 1` (which requires `0 ≤ r·T`). Sonnet-attempt budget: 3 tries; if it fails on the `max` arithmetic, Aristotle.

**Dependencies**: `Pythia.Finance.PutCallParity` (callPayoff), `Real.exp_neg_le_one` or chain via `Real.exp_le_exp`.

**Decomposition hint** (if Aristotle requested): split into (a) `max_le_spot_when_K_nonneg : 0 ≤ K → max (S - K) 0 ≤ max S 0`, (b) `discount_le_one`, (c) compose.

---

## Target 2 : Sharpe ratio under linear pricing invariance (medium form)

**File target**: `Pythia/Finance/SharpeAffine.lean` (new)

**Statement**:
```lean
theorem sharpeRatio_affine_riskfree {μ σ rf β : ℝ} (hσ : 0 < σ) :
    sharpeRatio μ rf σ - sharpeRatio μ (rf + β) σ = β / σ
```

**Why medium-tier**: rearranges Sharpe under additive shift of risk-free rate. Algebraic but needs `div_sub_div_eq` / `sub_div` orchestration. Sonnet-budget: 2 tries.

**Dependencies**: `Pythia.Finance.SharpeRatio.sharpeRatio` (existing).

**Decomposition hint**: `unfold sharpeRatio; field_simp; ring`.

---

## Target 3 : Itô isometry (HARD-tier candidate; medium if scoped to deterministic-integrand case)

**File target**: `Pythia/Finance/ItoIsometryDeterministic.lean` (new)

**Statement (deterministic-integrand restriction, medium)**:
```lean
-- For a deterministic step function f : [0, T] → ℝ and Brownian motion W,
-- E[(∫₀ᵀ f dW)²] = ∫₀ᵀ f(t)² dt
theorem ito_isometry_deterministic_step
    (T : ℝ) (hT : 0 ≤ T) (f : ℝ → ℝ) (hf_step : ...) :
    ⟨∫₀ᵀ f dW, ∫₀ᵀ f dW⟩ = ∫₀ᵀ f² dt
```

**Why medium-tier (scoped)**: requires Mathlib `MeasureTheory.StochasticIntegral` infrastructure which may not exist in v4.28.0. Sonnet will hit `unknown identifier` immediately; deferred to Aristotle.

**Dependencies**: Mathlib `MeasureTheory.Probability.BrownianMotion` (if exists) or own-construction.

**Decomposition hint**: defer to hard-tier if Mathlib infra absent : decompose into (a) Brownian increments are independent normal, (b) E[ΔW²] = Δt, (c) sum of step-integrand contributions.

**STATUS**: defer-to-hard-tier unless Mathlib infrastructure verified. Mark as Aristotle-skip if infra missing.

---

## Target 4 : Girsanov measure-change (HARD-tier; explicitly scoped)

**File target**: `Pythia/Finance/GirsanovDriftRemoval.lean` (new)

**Statement (hard-tier, decomposition target)**:
```lean
-- Under Girsanov, the drift-removed process W̃_t = W_t + ∫₀ᵗ θ_s ds
-- is a Brownian motion under the equivalent measure Q with density Z_T = exp(...)
```

**Why hard-tier**: full Girsanov requires Radon-Nikodym, exponential martingale, change-of-measure. Decompose first per L1-L5 Trotter pattern:
- L1: definition of Z_t = exp(-∫θ dW - ½∫θ² dt)
- L2: Z is positive martingale under P
- L3: dQ/dP = Z_T defines equivalent probability measure
- L4: W̃ is Brownian under Q (the headline)
- L5: integrability conditions on θ (Novikov)

**Each sub-lemma**: submit independently to Aristotle; compose locally.

**STATUS**: not yet ready for dispatch : needs Pythia.MeasureTheory.RadonNikodym infrastructure first (already exists per Pythia.Frontier.MeasureTheory.PathMeasureRN).

---

## Target 5 : LP strong duality (medium under linearity, hard under general)

**File target**: `Pythia/Optimization/LPDuality.lean` (likely already drafted on `research/ath-1267-pythia-expansion` per asabi 13:00Z claim : VERIFY before re-drafting; that branch was retracted as confabulation 2026-05-14 13:30Z but the LP weak_duality lemma name surfaced reliably).

**Statement (strong-duality, medium under bounded-feasible)**:
```lean
-- For LP min cᵀx s.t. Ax = b, x ≥ 0 with primal and dual both feasible,
-- primal optimum = dual optimum.
theorem lp_strong_duality
    (c : Fin n → ℝ) (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ)
    (h_feasible_primal : ...) (h_feasible_dual : ...) :
    inf {cᵀ ⬝ x | A.mulVec x = b ∧ ∀ i, 0 ≤ x i} =
    sup {bᵀ ⬝ y | ∀ j, (Aᵀ.mulVec y) j ≤ c j}
```

**Why medium**: classical Farkas-lemma-based proof; sub-lemma decomposition known.

**Decomposition**: (a) weak duality (already standard, sonnet-closeable), (b) Farkas' lemma for inequality systems, (c) optimality + complementary slackness gives equality.

**STATUS**: pre-flight VERIFY existing `LPDuality.lean` not already drafted, then submit sub-lemma (b) Farkas-lemma to Aristotle.

---

## Dispatch protocol

1. Scaffold each target above as new file with theorem-statement + `sorry`.
2. Sonnet sub-agent attempt FIRST (per `feedback_close_easy_lemmas_locally`).
3. If sonnet fails after N tries OR target depends on missing Mathlib infra → Aristotle.
4. Both accounts fire in parallel for different targets (no single-target collision).
5. Per `feedback_aristotle_patience_1h_gate` : 1h+ stalls normal; don't cancel at 20m.
6. Receipt: capture Aristotle project-id + result-tarball per `reference_aristotle_results_location` convention.

## Skip list (do NOT submit to Aristotle)

- Anything Annapurna / Trainium / Neuron / customer-accelerator-related (NDA per Aidan ts 1778764427).
- Customer-replay corpus / Annapurna kernels / Neuron SDK content.
- Anything currently in `Pythia.Frontier.Networking` BBRv3 cluster (customer-bound bundle).

## Pre-flight checks before each dispatch

- `gh pr list --author @me --state open` : avoid duplicate work (per `feedback_check_fleet_state_before_starting_work`).
- Mathlib originality grep : confirm theorem name not already named in Mathlib namespace.
- Sonnet sub-agent attempt at least once first.
