/-
Copyright (c) 2026 Pythia contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Pythia.InformationTheory.SourceCoding

Source-coding lower bound: any uniquely-decodable code has expected
length at least the Shannon entropy of the source.

## Main results

* `optimal_code_length_lower_bound` — parametrized form: given a
  Gibbs-style hypothesis that packages the KL / Kraft inequality, the
  expected code length `∑ a, p a * l a` is at least the Shannon
  entropy `∑ a, Real.negMulLog (p a)`.

## Design note

The unconditional form requires two ingredients that are not yet in
the library:
1. A `PrefixFreeCode` / uniquely-decodable code structure and Kraft's
   inequality `∑ a, Real.exp (-l a) ≤ 1`.
2. The extension from Kraft ≤ 1 to the Gibbs hypothesis below (a
   finite-alphabet log-sum inequality).
Both are non-trivial Lean developments; they are deferred and flagged
so the scaffold is clear about what is missing.  The arithmetic
consequence (once the Gibbs bound is in hand) is proved here by
`linarith` after a straightforward sum-rewriting.

## References

* Cover, T. M. and Thomas, J. A. "Elements of Information Theory."
  2nd ed. Wiley (2006). Theorem 5.4.1.
-/

import Mathlib

namespace Pythia.InformationTheory

/-- **Source-coding lower bound (parametrized / Gibbs form).**

For a PMF `p` over a finite alphabet and code lengths `l : α → ℝ`,
if the Gibbs-style non-negativity

  ∑ a, p a * Real.log (p a / Real.exp (-l a)) ≥ 0

holds (this packages the Kraft ≤ 1 step and the log-sum inequality),
then the expected code length is at least the Shannon entropy.

**Proof sketch.**
  `p a * Real.log (p a / exp(-l a))`
  = `p a * (log(p a) - log(exp(-l a)))`    -- Real.log_div (when p a > 0)
  = `p a * (log(p a) + l a)`               -- Real.log_exp, neg cancel
  = `p a * log(p a) + p a * l a`           -- distributivity

Summing over `a`, the hypothesis gives
  `0 ≤ ∑ a, p a * log(p a) + ∑ a, p a * l a`
  `= -(∑ a, negMulLog (p a)) + ∑ a, p a * l a`

so `∑ a, negMulLog (p a) ≤ ∑ a, p a * l a`.

Citation: Cover-Thomas §5.4.1. -/
theorem optimal_code_length_lower_bound
    {α : Type*} [Fintype α]
    (p : α → ℝ) (l : α → ℝ)
    (hp_nonneg : ∀ a, 0 ≤ p a) (hp_sum : ∑ a, p a = 1)
    (h_gibbs : 0 ≤ ∑ a : α, p a * Real.log (p a / Real.exp (-l a))) :
    ∑ a, Real.negMulLog (p a) ≤ ∑ a, p a * l a := by
  -- Rewrite negMulLog as -p * log p.
  simp_rw [Real.negMulLog_def]
  -- The goal is: ∑ a, -(p a) * log(p a) ≤ ∑ a, p a * l a.
  -- Equivalently: 0 ≤ ∑ a, p a * log(p a) + ∑ a, p a * l a.
  -- We derive this from h_gibbs by showing h_gibbs equals exactly this sum.
  have key : ∑ a : α, p a * Real.log (p a / Real.exp (-l a)) =
             ∑ a : α, p a * Real.log (p a) + ∑ a : α, p a * l a := by
    rw [← Finset.sum_add_distrib]
    congr 1
    ext a
    by_cases hpa : p a = 0
    · simp [hpa]
    · have hpa_pos : 0 < p a := lt_of_le_of_ne (hp_nonneg a) (Ne.symm hpa)
      rw [Real.log_div (ne_of_gt hpa_pos) (Real.exp_pos _).ne',
          Real.log_exp]
      ring
  -- From key + h_gibbs: 0 ≤ ∑ a, p a * log(p a) + ∑ a, p a * l a
  have hineq : 0 ≤ ∑ a : α, p a * Real.log (p a) + ∑ a : α, p a * l a := by
    rw [← key]; exact h_gibbs
  -- ∑ a, -(p a) * log(p a) = -(∑ a, p a * log(p a))
  have hneg : ∑ a : α, -(p a) * Real.log (p a) = -(∑ a : α, p a * Real.log (p a)) := by
    simp [Finset.sum_neg_distrib, neg_mul]
  linarith

end Pythia.InformationTheory
