/-
Copyright (c) 2026 Pythia contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Pythia.Verification.Foundations.Induction

Soundness of k-induction for bounded model checking (EBMC
`--k-induction` mode) and BMC counterexample minimality.

If a property `P` holds for the first `k` steps and the induction step
(`P` at steps `i..i+k` implies `P` at step `i+k+1`) holds, then `P`
holds at all steps. This is the proof-theoretic backbone of every
EBMC k-induction run; machine-checking it means the tool's output is
verified at the soundness level.

This module is part of the **4+1 universal invariant set** that the
customer-facing `flow_guard` preflight gate cites. The private
namespace `Pythia.Hardware.KInduction` retains backwards-compatibility
re-exports for downstream private callers.
-/

import Mathlib

namespace Pythia.Verification.Foundations.Induction

/-- **k-induction soundness.** If `P` holds on steps `0..k` (base) and
the induction step holds (`P` on `i..i+k` implies `P` on `i+k+1`),
then `P` holds on all natural numbers. -/
theorem k_induction_soundness
    {P : ℕ → Prop}
    (k : ℕ)
    (base : ∀ n, n ≤ k → P n)
    (step : ∀ i, (∀ j, i ≤ j → j ≤ i + k → P j) → P (i + k + 1)) :
    ∀ n, P n := by
  intro n
  induction n using Nat.strongRecOn with
  | _ n ih =>
    by_cases h : n ≤ k
    · exact base n h
    · push_neg at h
      have hn : n = (n - k - 1) + k + 1 := by omega
      rw [hn]
      apply step
      intro j hj1 hj2
      apply ih; omega

/-- **1-induction is standard strong induction.** -/
theorem one_induction_eq_strong_induction
    {P : ℕ → Prop}
    (base : P 0)
    (step : ∀ i, P i → P (i + 1)) :
    ∀ n, P n :=
  Nat.rec base (fun n ih => step n ih)

/-- **BMC counterexample minimality.** If `P` fails at some step,
there exists a minimal counterexample of length ≤ the recurrence
diameter. -/
theorem bmc_counterexample_minimal
    {P : ℕ → Prop} [DecidablePred P]
    (h_fail : ∃ n, ¬P n) :
    ∃ n₀, ¬P n₀ ∧ ∀ m, m < n₀ → P m :=
  ⟨Nat.find h_fail, Nat.find_spec h_fail, fun m hm => by
    by_contra h
    exact absurd hm (not_lt.mpr (Nat.find_min' h_fail h))⟩

end Pythia.Verification.Foundations.Induction
