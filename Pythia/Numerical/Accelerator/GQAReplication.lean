/-
Copyright (c) 2026 Pythia contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# GQA Key Replication = Independent Heads

Grouped Query Attention (GQA, Ainslie et al. 2023) uses fewer
key-value heads than query heads. Each KV head is shared across
a group of query heads. The key correctness property: replicating
KV heads to match query head count produces identical attention
output to computing each query head independently against its
assigned KV head.

## Main results

* `gqa_replication_eq_independent` — replicated attention = grouped
* `gqa_same_group_same_kv` — queries in same group share KV
-/
import Mathlib

namespace Pythia.Numerical.GQA

open Finset BigOperators

noncomputable section

variable {d : ℕ}

def groupSize (num_q num_kv : ℕ) : ℕ := num_q / num_kv

def groupAssignment (num_q num_kv : ℕ)
    (hkv : 0 < num_kv) (hdvd : num_kv ∣ num_q)
    (q_head : Fin num_q) : Fin num_kv :=
  ⟨q_head.val / groupSize num_q num_kv, by
    unfold groupSize
    apply Nat.div_lt_of_lt_mul
    rw [Nat.div_mul_cancel hdvd]
    exact q_head.isLt⟩

def attentionHead (query key value : Fin d → ℝ) : Fin d → ℝ :=
  fun i => (∑ j : Fin d, query j * key j) * value i

theorem gqa_replication_eq_independent
    (num_q num_kv : ℕ) (hkv : 0 < num_kv) (hdvd : num_kv ∣ num_q)
    (queries : Fin num_q → Fin d → ℝ)
    (keys_replicated : Fin num_q → Fin d → ℝ)
    (values_replicated : Fin num_q → Fin d → ℝ)
    (keys_grouped : Fin num_kv → Fin d → ℝ)
    (values_grouped : Fin num_kv → Fin d → ℝ)
    (h_keys : ∀ q : Fin num_q,
      keys_replicated q = keys_grouped (groupAssignment num_q num_kv hkv hdvd q))
    (h_values : ∀ q : Fin num_q,
      values_replicated q = values_grouped (groupAssignment num_q num_kv hkv hdvd q))
    (q : Fin num_q) :
    attentionHead (queries q) (keys_replicated q) (values_replicated q) =
    attentionHead (queries q) (keys_grouped (groupAssignment num_q num_kv hkv hdvd q))
      (values_grouped (groupAssignment num_q num_kv hkv hdvd q)) := by
  rw [h_keys, h_values]

theorem gqa_same_group_same_kv (num_q num_kv : ℕ)
    (hkv : 0 < num_kv) (hdvd : num_kv ∣ num_q)
    (q1 q2 : Fin num_q)
    (h : groupAssignment num_q num_kv hkv hdvd q1 =
         groupAssignment num_q num_kv hkv hdvd q2)
    (keys : Fin num_kv → Fin d → ℝ) :
    keys (groupAssignment num_q num_kv hkv hdvd q1) =
    keys (groupAssignment num_q num_kv hkv hdvd q2) := by
  rw [h]

theorem gqa_group_assignment_range (num_q num_kv : ℕ)
    (hkv : 0 < num_kv) (hdvd : num_kv ∣ num_q) (q : Fin num_q) :
    (groupAssignment num_q num_kv hkv hdvd q).val < num_kv :=
  (groupAssignment num_q num_kv hkv hdvd q).isLt

end

end Pythia.Numerical.GQA
