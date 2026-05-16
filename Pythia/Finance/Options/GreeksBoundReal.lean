/-
Copyright (c) 2026 Pythia contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Option Greeks Bounds (real proofs)

Proves universal bounds on Black-Scholes Greeks using genuine Mathlib
machinery rather than axiom-only stubs.

Three theorems that practitioners use every day to validate a
pricing engine:

1. **Call delta in [0, 1]** and **put delta in [-1, 0]**.
   Combined: for any vanilla option |delta| <= 1.
   Proof: `abs_le.mpr` + the CDF axioms `0 <= Phi(x) <= 1`.

2. **Gamma nonneg** for vanilla options.
   Proof: `div_nonneg` + `mul_nonneg` + `sq_nonneg` / `positivity`.

3. **Theta-gamma ATM identity**: when the delta-carry and discounting
   cancel (ATM condition: r*S*delta = r*C), the BS PDE collapses to
   `theta = -(1/2) * sigma^2 * S^2 * gamma`.
   Proof: linear arithmetic from the PDE constraint.

All definitions reuse the concrete BS definitions already in
`Pythia.Finance.BlackScholesGreeks` and
`Pythia.Finance.BlackScholesPDE`.  No axioms are introduced; every
sorry is absent.

## References

* Black, F. and Scholes, M. "The Pricing of Options and Corporate
  Liabilities." *Journal of Political Economy* 81(3): 637-654 (1973).
* Hull, J. C. *Options, Futures, and Other Derivatives*, 10th ed.
  Pearson (2017), §19.4-19.8 (the Greeks).
-/
import Mathlib
import Pythia.Finance.Options.BlackScholesGreeks
import Pythia.Finance.Options.BlackScholesPDE
import Pythia.Tactic.Pythia

open Real

namespace Pythia.Finance.GreeksBoundReal

-- ---------------------------------------------------------------------------
-- Section 1. Delta bounds
-- ---------------------------------------------------------------------------

/-- **Call delta is in [0, 1].**

Under the abstract-CDF axioms `0 <= Phi x` and `Phi x <= 1`, the
Black-Scholes call delta `Phi(d1)` lies in the unit interval.  The
CDF interpretation: call delta is the risk-neutral probability of
expiring in-the-money. -/
@[stat_lemma]
theorem call_delta_nonneg (Phi : ℝ → ℝ)
    (hPhi_nonneg : ∀ x, 0 ≤ Phi x) (hPhi_le_one : ∀ x, Phi x ≤ 1)
    (S K T r sigma : ℝ) :
    0 ≤ bsDelta Phi S K T r sigma := by
  unfold bsDelta
  exact hPhi_nonneg _

@[stat_lemma]
theorem call_delta_le_one (Phi : ℝ → ℝ)
    (hPhi_nonneg : ∀ x, 0 ≤ Phi x) (hPhi_le_one : ∀ x, Phi x ≤ 1)
    (S K T r sigma : ℝ) :
    bsDelta Phi S K T r sigma ≤ 1 := by
  unfold bsDelta
  exact hPhi_le_one _

/-- **Call delta satisfies |delta_call| <= 1.**

`abs_le` says `|x| <= 1 <-> -1 <= x /\ x <= 1`.
Since `0 <= bsDelta ... <= 1`, we have `-1 <= 0 <= bsDelta` and `bsDelta <= 1`. -/
@[stat_lemma]
theorem call_delta_abs_le_one (Phi : ℝ → ℝ)
    (hPhi_nonneg : ∀ x, 0 ≤ Phi x) (hPhi_le_one : ∀ x, Phi x ≤ 1)
    (S K T r sigma : ℝ) :
    |bsDelta Phi S K T r sigma| ≤ 1 := by
  rw [abs_le]
  have h_nn := call_delta_nonneg Phi hPhi_nonneg hPhi_le_one S K T r sigma
  have h_le := call_delta_le_one  Phi hPhi_nonneg hPhi_le_one S K T r sigma
  exact ⟨by linarith, h_le⟩

/-- **Put delta is in [-1, 0].**

Put-call delta parity: delta_put = delta_call - 1.  Since `0 <= delta_call <= 1`,
we obtain `-1 <= delta_put <= 0`. -/
noncomputable def putDelta (Phi : ℝ → ℝ) (S K T r sigma : ℝ) : ℝ :=
  bsDelta Phi S K T r sigma - 1

-- Helper: state the underlying bounds as local variables so linarith has them.
@[stat_lemma]
theorem put_delta_neg_one_le (Phi : ℝ → ℝ)
    (hPhi_nonneg : ∀ x, 0 ≤ Phi x) (hPhi_le_one : ∀ x, Phi x ≤ 1)
    (S K T r sigma : ℝ) :
    -1 ≤ putDelta Phi S K T r sigma := by
  unfold putDelta
  -- goal: -1 <= bsDelta ... - 1, equiv. 0 <= bsDelta ...
  have h := call_delta_nonneg Phi hPhi_nonneg hPhi_le_one S K T r sigma
  linarith

@[stat_lemma]
theorem put_delta_le_zero (Phi : ℝ → ℝ)
    (hPhi_nonneg : ∀ x, 0 ≤ Phi x) (hPhi_le_one : ∀ x, Phi x ≤ 1)
    (S K T r sigma : ℝ) :
    putDelta Phi S K T r sigma ≤ 0 := by
  unfold putDelta
  -- goal: bsDelta ... - 1 <= 0, equiv. bsDelta ... <= 1
  have h := call_delta_le_one Phi hPhi_nonneg hPhi_le_one S K T r sigma
  linarith

/-- **Put delta satisfies |delta_put| <= 1.**

`abs_le` says `|x| <= 1 <-> -1 <= x /\ x <= 1`.
For x = putDelta in [-1, 0], both hold: -1 <= x (direct) and x <= 0 <= 1. -/
@[stat_lemma]
theorem put_delta_abs_le_one (Phi : ℝ → ℝ)
    (hPhi_nonneg : ∀ x, 0 ≤ Phi x) (hPhi_le_one : ∀ x, Phi x ≤ 1)
    (S K T r sigma : ℝ) :
    |putDelta Phi S K T r sigma| ≤ 1 := by
  rw [abs_le]
  have h_lo := put_delta_neg_one_le Phi hPhi_nonneg hPhi_le_one S K T r sigma
  have h_hi := put_delta_le_zero    Phi hPhi_nonneg hPhi_le_one S K T r sigma
  exact ⟨h_lo, by linarith⟩

-- ---------------------------------------------------------------------------
-- Section 2. Gamma non-negativity
-- ---------------------------------------------------------------------------

/-- **Gamma is non-negative for vanilla options.**

For a European call (or put — they share the same gamma), the
second derivative of price with respect to spot is

    Gamma = phi(d1) / (S * sigma * sqrt(T))

where phi is the standard-normal PDF (non-negative everywhere).
The denominator is strictly positive when S > 0, sigma > 0, T > 0,
so the quotient is non-negative.

The proof uses `div_nonneg` from Mathlib with the denominator
positivity established by `positivity` (which combines `mul_pos`,
`Real.sqrt_pos`, and the strict hypotheses). -/
@[stat_lemma]
theorem gamma_nonneg (phi : ℝ → ℝ)
    (hphi_nonneg : ∀ x, 0 ≤ phi x)
    {S sigma T : ℝ} (hS : 0 < S) (hsigma : 0 < sigma) (hT : 0 < T)
    (K r : ℝ) :
    0 ≤ bsGamma phi S K T r sigma := by
  unfold bsGamma
  apply div_nonneg (hphi_nonneg _)
  have hsqrtT : 0 < Real.sqrt T := Real.sqrt_pos.mpr hT
  positivity

/-- **Gamma is strictly positive when the PDF is everywhere positive.**

If the PDF is strictly positive at d1 (true for the standard normal
on all of R), then gamma > 0: every long vanilla has strict convexity. -/
@[stat_lemma]
theorem gamma_pos (phi : ℝ → ℝ)
    (hphi_pos : ∀ x, 0 < phi x)
    {S sigma T : ℝ} (hS : 0 < S) (hsigma : 0 < sigma) (hT : 0 < T)
    (K r : ℝ) :
    0 < bsGamma phi S K T r sigma := by
  unfold bsGamma
  apply div_pos (hphi_pos _)
  have hsqrtT : 0 < Real.sqrt T := Real.sqrt_pos.mpr hT
  positivity

-- ---------------------------------------------------------------------------
-- Section 3. Theta-gamma ATM relationship
-- ---------------------------------------------------------------------------

/-- **Theta-gamma ATM identity.**

From the Black-Scholes PDE:

    theta + (1/2) * sigma^2 * S^2 * gamma + r*S*delta - r*C = 0

At-the-money with cash-neutral carry (r*S*delta = r*C), the carry and
discounting terms cancel, leaving

    theta = -(1/2) * sigma^2 * S^2 * gamma.

This is the practitioner "theta-gamma trade-off": holding a long-gamma
position always costs time premium at exactly this rate when the
portfolio is delta-neutral and the carry washes. -/
@[stat_lemma]
theorem theta_gamma_atm
    {theta gamma S sigma r C delta : ℝ}
    (h_pde : theta + sigma ^ 2 / 2 * S ^ 2 * gamma + r * S * delta - r * C = 0)
    (h_atm : r * S * delta = r * C) :
    theta = -(sigma ^ 2 / 2 * S ^ 2 * gamma) := by
  linarith

/-- **Theta is non-positive for a long-gamma position at ATM.**

Under the ATM carry condition, theta = -(sigma^2/2)*S^2*gamma.
Since gamma >= 0, S^2 >= 0, sigma^2 >= 0, the RHS is non-positive:
you pay time-value to be long gamma. -/
@[stat_lemma]
theorem theta_nonpos_long_gamma
    {theta gamma S sigma r C delta : ℝ}
    (h_pde : theta + sigma ^ 2 / 2 * S ^ 2 * gamma + r * S * delta - r * C = 0)
    (h_atm : r * S * delta = r * C)
    (h_gamma : 0 ≤ gamma) (h_S : 0 ≤ S) (h_sigma : 0 ≤ sigma) :
    theta ≤ 0 := by
  have h_eq := theta_gamma_atm h_pde h_atm
  have h_gamma_term : 0 ≤ sigma ^ 2 / 2 * S ^ 2 * gamma :=
    mul_nonneg (mul_nonneg (div_nonneg (sq_nonneg sigma) (by norm_num)) (sq_nonneg S)) h_gamma
  linarith

/-- **Theta magnitude equals half variance times gamma (ATM).**

The absolute value of ATM theta equals the instantaneous dollar
variance `(1/2) * sigma^2 * S^2` times gamma.  This is the P&L
attribution identity for a delta-neutral gamma trader: theta loss
per unit time = half the gamma times the squared dollar spot move. -/
@[stat_lemma]
theorem theta_abs_eq_half_gamma_variance
    {theta gamma S sigma r C delta : ℝ}
    (h_pde : theta + sigma ^ 2 / 2 * S ^ 2 * gamma + r * S * delta - r * C = 0)
    (h_atm : r * S * delta = r * C)
    (h_gamma : 0 ≤ gamma) (h_S : 0 ≤ S) (h_sigma : 0 ≤ sigma) :
    |theta| = sigma ^ 2 / 2 * S ^ 2 * gamma := by
  have h_eq := theta_gamma_atm h_pde h_atm
  have h_gamma_term : 0 ≤ sigma ^ 2 / 2 * S ^ 2 * gamma :=
    mul_nonneg (mul_nonneg (div_nonneg (sq_nonneg sigma) (by norm_num)) (sq_nonneg S)) h_gamma
  rw [h_eq, abs_neg, abs_of_nonneg h_gamma_term]

-- ---------------------------------------------------------------------------
-- Section 4. Combined summary
-- ---------------------------------------------------------------------------

/-- **Greeks sanity suite.**

One conjunction packaging the three core sanity checks a risk system
runs on every pricing-engine output:

  (a) call delta in [0, 1],
  (b) gamma non-negative,
  (c) theta non-positive under ATM carry cancellation.

If all three hold, the Greeks are consistent with a convex, time-decaying
vanilla option. -/
@[stat_lemma]
theorem greeks_sanity_suite
    (Phi phi : ℝ → ℝ)
    (hPhi_nonneg  : ∀ x, 0 ≤ Phi x)
    (hPhi_le_one  : ∀ x, Phi x ≤ 1)
    (hphi_nonneg  : ∀ x, 0 ≤ phi x)
    {S K T r sigma : ℝ}
    (hS : 0 < S) (hsigma : 0 < sigma) (hT : 0 < T)
    {theta C : ℝ}
    (h_pde : theta + sigma ^ 2 / 2 * S ^ 2 * bsGamma phi S K T r sigma
               + r * S * bsDelta Phi S K T r sigma
               - r * C = 0)
    (h_atm : r * S * bsDelta Phi S K T r sigma = r * C) :
    (0 ≤ bsDelta Phi S K T r sigma ∧ bsDelta Phi S K T r sigma ≤ 1)
    ∧ (0 ≤ bsGamma phi S K T r sigma)
    ∧ (theta ≤ 0) := by
  have h_delta_nn := call_delta_nonneg Phi hPhi_nonneg hPhi_le_one S K T r sigma
  have h_delta_le := call_delta_le_one  Phi hPhi_nonneg hPhi_le_one S K T r sigma
  have h_gamma    := gamma_nonneg phi hphi_nonneg hS hsigma hT K r
  have h_gamma_term : 0 ≤ sigma ^ 2 / 2 * S ^ 2 * bsGamma phi S K T r sigma :=
    mul_nonneg (mul_nonneg (div_nonneg (sq_nonneg sigma) (by norm_num)) (sq_nonneg S)) h_gamma
  refine ⟨⟨h_delta_nn, h_delta_le⟩, h_gamma, ?_⟩
  linarith

end Pythia.Finance.GreeksBoundReal
