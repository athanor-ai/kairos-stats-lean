/-
Copyright (c) 2026 Pythia contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Erlang B blocking-probability formula

The **Erlang B formula** gives the blocking probability for an M/M/n/n
(Erlang loss) queue with `n` servers and offered load `ρ = λ / μ`:

$$
  B(n,\rho) \;=\;
  \frac{\rho^n / n!}{\sum_{k=0}^{n} \rho^k / k!}
$$

## Main definitions

* `ErlangB.unnormProb ρ k` — the unnormalized steady-state weight `ρ^k / k!`.
* `ErlangB.partitionFn ρ n` — the partition function `∑_{k=0}^{n} ρ^k / k!`.
* `ErlangB.blockingProb ρ n` — the blocking probability `B(n, ρ)`.

## Main results

* `ErlangB.blockingProb_zero` — `B(0, ρ) = 1`.
* `ErlangB.partitionFn_pos` — the partition function is positive for `ρ ≥ 0`.
* `ErlangB.blockingProb_nonneg` — `B(n, ρ) ≥ 0` for `ρ ≥ 0`.
* `ErlangB.blockingProb_le_one` — `B(n, ρ) ≤ 1` for `ρ ≥ 0`.
* `ErlangB.steadyState_sum_one` — steady-state probabilities sum to 1.
* `ErlangB.blockingProb_recursion` — the classic Erlang B recursion:
    `B(n+1, ρ) = (ρ · B(n, ρ)) / ((n+1) + ρ · B(n, ρ))`.

## References

* Erlang, A.K. (1917). Solution of some problems in the theory of
  probabilities of significance in automatic telephone exchanges.
* Cooper, R.B. *Introduction to Queueing Theory*, ch. 5.
-/

import Mathlib

open Finset

namespace ErlangB

/-! ### Unnormalized weights and partition function -/

/-- Unnormalized steady-state weight for state `k`: `ρ^k / k!`. -/
noncomputable def unnormProb (ρ : ℝ) (k : ℕ) : ℝ :=
  ρ ^ k / (k.factorial : ℝ)

/-- Partition function (normalization constant): `∑_{k=0}^{n} ρ^k / k!`. -/
noncomputable def partitionFn (ρ : ℝ) (n : ℕ) : ℝ :=
  ∑ k ∈ range (n + 1), unnormProb ρ k

/-- Erlang B blocking probability: `B(n, ρ) = (ρ^n / n!) / (∑_{k=0}^{n} ρ^k / k!)`. -/
noncomputable def blockingProb (ρ : ℝ) (n : ℕ) : ℝ :=
  unnormProb ρ n / partitionFn ρ n

/-- Steady-state probability of being in state `k` (0 if `k > n`). -/
noncomputable def steadyStateProb (ρ : ℝ) (n : ℕ) (k : ℕ) : ℝ :=
  if k ≤ n then unnormProb ρ k / partitionFn ρ n else 0

/-! ### Basic lemmas about unnormalized weights -/

theorem unnormProb_zero (ρ : ℝ) : unnormProb ρ 0 = 1 := by
  simp [unnormProb]

theorem unnormProb_nonneg {ρ : ℝ} (hρ : 0 ≤ ρ) (k : ℕ) : 0 ≤ unnormProb ρ k := by
  exact div_nonneg ( pow_nonneg hρ _ ) ( Nat.cast_nonneg _ )

theorem unnormProb_pos {ρ : ℝ} (hρ : 0 < ρ) (k : ℕ) : 0 < unnormProb ρ k := by
  exact div_pos ( pow_pos hρ _ ) ( Nat.cast_pos.mpr ( Nat.factorial_pos _ ) )

theorem unnormProb_succ (ρ : ℝ) (k : ℕ) :
    unnormProb ρ (k + 1) = ρ / (k + 1 : ℝ) * unnormProb ρ k := by
  unfold unnormProb; push_cast [ pow_succ, Nat.factorial_succ ] ; rw [ div_mul_div_comm ] ; ring;

/-! ### Partition function properties -/

theorem partitionFn_zero (ρ : ℝ) : partitionFn ρ 0 = 1 := by
  simp [partitionFn, unnormProb]

theorem partitionFn_succ (ρ : ℝ) (n : ℕ) :
    partitionFn ρ (n + 1) = partitionFn ρ n + unnormProb ρ (n + 1) := by
  exact Finset.sum_range_succ _ _

theorem partitionFn_pos {ρ : ℝ} (hρ : 0 ≤ ρ) (n : ℕ) : 0 < partitionFn ρ n := by
  exact lt_of_lt_of_le ( by positivity ) ( Finset.single_le_sum ( fun x _ => div_nonneg ( pow_nonneg hρ x ) ( Nat.cast_nonneg _ ) ) ( Finset.mem_range.mpr ( Nat.succ_pos _ ) ) )

/-! ### Blocking probability properties -/

/-- With zero servers, everything is blocked: `B(0, ρ) = 1`. -/
theorem blockingProb_zero (ρ : ℝ) : blockingProb ρ 0 = 1 := by
  simp [blockingProb, partitionFn_zero, unnormProb_zero]

/-
Blocking probability is non-negative for non-negative load.
-/
theorem blockingProb_nonneg {ρ : ℝ} (hρ : 0 ≤ ρ) (n : ℕ) :
    0 ≤ blockingProb ρ n := by
  exact div_nonneg ( div_nonneg ( pow_nonneg hρ _ ) ( Nat.cast_nonneg _ ) ) ( Finset.sum_nonneg fun _ _ => div_nonneg ( pow_nonneg hρ _ ) ( Nat.cast_nonneg _ ) )

/-
Blocking probability is at most 1 for non-negative load.
-/
theorem blockingProb_le_one {ρ : ℝ} (hρ : 0 ≤ ρ) (n : ℕ) :
    blockingProb ρ n ≤ 1 := by
  exact div_le_one_of_le₀ ( Finset.single_le_sum ( fun a _ => unnormProb_nonneg hρ a ) ( Finset.mem_range.mpr ( Nat.lt_succ_self _ ) ) ) ( by exact Finset.sum_nonneg fun a _ => unnormProb_nonneg hρ a )

/-! ### Steady-state probabilities sum to 1 -/

/-
The steady-state probabilities over {0, …, n} sum to 1.
-/
theorem steadyState_sum_one {ρ : ℝ} (hρ : 0 ≤ ρ) (n : ℕ) :
    ∑ k ∈ range (n + 1), steadyStateProb ρ n k = 1 := by
  unfold steadyStateProb;
  rw [ Finset.sum_congr rfl fun x hx => if_pos <| Finset.mem_range_succ_iff.mp hx, ← Finset.sum_div _ _ _, div_eq_iff ] <;> norm_num [ partitionFn ];
  exact ne_of_gt <| lt_of_lt_of_le ( by positivity ) <| Finset.single_le_sum ( fun x _ => div_nonneg ( pow_nonneg hρ _ ) <| Nat.cast_nonneg _ ) <| Finset.mem_range.2 <| Nat.succ_pos _

/-! ### Erlang B recursion -/

/-
The classic Erlang B recursion:
`B(n+1, ρ) = (ρ · B(n, ρ)) / ((n+1) + ρ · B(n, ρ))`,
valid when `ρ > 0`.
-/
theorem blockingProb_recursion {ρ : ℝ} (hρ : 0 < ρ) (n : ℕ) :
    blockingProb ρ (n + 1) =
      ρ * blockingProb ρ n / ((n + 1 : ℝ) + ρ * blockingProb ρ n) := by
  unfold blockingProb;
  rw [ unnormProb_succ, partitionFn_succ ];
  rw [ unnormProb_succ ];
  field_simp;
  rw [ mul_add, mul_div_cancel₀ _ ( ne_of_gt ( partitionFn_pos hρ.le n ) ) ] ; ring

end ErlangB