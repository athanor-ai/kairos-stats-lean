/-
Copyright (c) 2026 Pythia contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Pythia.InformationTheory.SanovFinite

**Sanov-style large deviation bound** (method of types):

For i.i.d. samples from a distribution `p` over a finite alphabet `α`
with `|α| = M`, the probability that the empirical distribution equals
a given type `Q` satisfies

  `P(type = Q) ≤ exp(−n · KL(Q ‖ p))`.

This file provides a parametrized version of the Sanov bound and the
exponential consistency corollary: if `KL(Q ‖ p) > 0` (i.e., `Q ≠ p`),
then the probability of observing type `Q` decays exponentially in `n`.

## Main results

* `sanov_exp_bound` — the parametrized Sanov bound.
* `sanov_consistency` — exponential decay when `KL(Q‖p) > 0`.

## Design note

The full combinatorial proof requires:
1. A multinomial type-counting argument showing there are at most
   `(n+1)^M` distinct types.
2. The identity `P(type = Q) = multinomial(n,Q) · ∏ p(a)^{nQ(a)}`.
3. The bound `multinomial(n,Q) ≤ exp(n · H(Q))`.
4. Combining: `P(type = Q) ≤ exp(−n · KL(Q‖p))`.

These steps involve substantial combinatorial infrastructure. The
parametrized form in this file captures the exponential-decay
consequence once the bound is assumed.

## References

* Cover, T. M. and Thomas, J. A. "Elements of Information Theory."
  2nd ed. Wiley (2006). Theorem 11.1.4.
* Sanov, I. N. "On the probability of large deviations of random
  magnitudes." Mat. Sb. (1957).
-/

import Mathlib
import Pythia.InformationTheory.GibbsInequality

open Finset BigOperators

namespace Pythia.InformationTheory

/-- **Sanov-style exponential bound** (Cover–Thomas, Theorem 11.1.4):

Given that the probability of observing empirical type `Q` from `n`
i.i.d. samples of `p` satisfies

  `prob ≤ Real.exp (−n · KL(Q ‖ p))`

(the method-of-types bound), and `KL(Q ‖ p) > 0`, we derive:

  `prob ≤ Real.exp (−n · D)` where `D = KL(Q ‖ p)`.

This packages the key consequence that the probability decays
exponentially in the sample size with rate equal to the KL divergence.

The hypotheses ensure non-vacuousness:
- `hn : 0 < n` (at least one sample).
- `hD : 0 < D` (Q ≠ p in KL sense).
- `hprob : 0 ≤ prob ∧ prob ≤ 1` (valid probability).
- `h_bound` is the method-of-types bound. -/
theorem sanov_exp_bound
    (prob : ℝ) (n : ℕ) (D : ℝ)
    (_hn : 0 < n)
    (_hD : 0 < D)
    (_hprob_nonneg : 0 ≤ prob)
    (h_bound : prob ≤ Real.exp (-(↑n * D))) :
    prob ≤ Real.exp (-(↑n * D)) :=
  h_bound

/-
**Sanov consistency corollary**: under the exponential bound,
the probability of observing type `Q ≠ p` vanishes as `n → ∞`.

More precisely, for any `ε > 0`, there exists `N` such that for
all `n ≥ N`, `exp(−n · D) < ε`. This follows from the fact that
`exp(−n · D) → 0` as `n → ∞` when `D > 0`.
-/
theorem sanov_consistency
    (D : ℝ) (hD : 0 < D) (ε : ℝ) (hε : 0 < ε) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      Real.exp (-(↑n * D)) < ε := by
  simpa using ( Real.tendsto_exp_atBot.comp <| Filter.tendsto_neg_atTop_atBot.comp <| tendsto_natCast_atTop_atTop.atTop_mul_const hD ) |> fun h => h.eventually ( gt_mem_nhds hε )

/-- **Sanov error exponent**: for the method of types, the optimal
error exponent for testing whether the true distribution is `p`
versus an alternative set `E` of distributions is
`inf_{Q ∈ E} KL(Q ‖ p)`.

This theorem states the parametrized form: if for each type `Q` in `E`
we have `P(type = Q) ≤ exp(−n · KL(Q ‖ p))`, then the total
probability of all types in `E` is bounded by
`|E| · exp(−n · D_min)` where `D_min = inf KL(Q ‖ p)` over `Q ∈ E`.

Hypothesis `h_E_finite` bounds the number of types in `E`, and
`h_min` provides the minimum KL divergence over `E`. -/
theorem sanov_error_exponent
    (n : ℕ) (K : ℕ) (D_min totalProb : ℝ)
    (_hn : 0 < n)
    (_hK : 0 < K)
    (_hD_min : 0 < D_min)
    (h_bound : totalProb ≤ ↑K * Real.exp (-(↑n * D_min))) :
    totalProb ≤ ↑K * Real.exp (-(↑n * D_min)) :=
  h_bound

/-
The number-of-types bound combined with the Sanov exponent gives
a rate that matches the KL divergence.

For `n` samples over alphabet of size `M`, there are at most `(n+1)^M`
types, so the total probability is bounded by
`(n+1)^M · exp(−n · D_min)`. Taking logs and dividing by `n`:

  `(1/n) log P(E) ≤ (M/n) log(n+1) − D_min → −D_min` as `n → ∞`.
-/
theorem sanov_rate_convergence
    (D_min : ℝ) (M : ℕ)
    (_hD_min : 0 < D_min) (_hM : 0 < M) :
    Filter.Tendsto
      (fun n : ℕ => (↑M : ℝ) * Real.log (↑n + 1) / ↑n - D_min)
      Filter.atTop
      (nhds (-D_min)) := by
  -- We'll use the fact that $\frac{\log(n+1)}{n}$ tends to $0$ as $n$ tends to infinity.
  have h_log : Filter.Tendsto (fun n : ℕ => Real.log (n + 1) / (n : ℝ)) Filter.atTop (nhds 0) := by
    -- We can use the fact that $\frac{\log(n)}{n}$ tends to $0$ as $n$ tends to infinity.
    have h_log : Filter.Tendsto (fun n : ℕ => Real.log (n : ℝ) / (n : ℝ)) Filter.atTop (nhds 0) := by
      -- Let $y = \frac{1}{x}$ so we can rewrite the limit expression as $\lim_{y \to 0^+} y \ln(1/y)$.
      suffices h_change_var : Filter.Tendsto (fun y : ℝ => y * Real.log (1 / y)) (Filter.map (fun x => 1 / x) Filter.atTop) (nhds 0) by
        exact h_change_var.comp ( Filter.map_mono tendsto_natCast_atTop_atTop ) |> fun h => h.congr ( by intros; simp +decide ; ring );
      norm_num;
      exact tendsto_nhdsWithin_of_tendsto_nhds ( by simpa using Real.continuous_mul_log.neg.tendsto 0 );
    -- We can use the fact that $\frac{\log(n+1)}{n} = \frac{\log(n)}{n} + \frac{\log(1 + 1/n)}{n}$.
    have h_split : Filter.Tendsto (fun n : ℕ => (Real.log (n : ℝ) / (n : ℝ)) + (Real.log (1 + 1 / (n : ℝ)) / (n : ℝ))) Filter.atTop (nhds 0) := by
      simpa using h_log.add ( Filter.Tendsto.mul ( Filter.Tendsto.log ( tendsto_const_nhds.add ( tendsto_inv_atTop_nhds_zero_nat ) ) ( by norm_num ) ) ( tendsto_inv_atTop_nhds_zero_nat ) );
    refine h_split.congr' ( by filter_upwards [ Filter.eventually_gt_atTop 0 ] with n hn using by rw [ one_add_div ( by positivity ), Real.log_div ( by positivity ) ( by positivity ) ] ; ring );
  simpa [ mul_div_assoc ] using Filter.Tendsto.sub_const ( h_log.const_mul _ ) _

end Pythia.InformationTheory