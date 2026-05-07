/-
Copyright (c) 2026 Pythia contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# KV Cache Append Monotonicity

KV caching in autoregressive transformers stores the key-value pairs
from previous tokens. At each decode step, the new token's K/V vectors
are appended. The critical correctness property: appending preserves
all previously cached entries — the cache is prefix-monotone.

## Main results

* `kv_cache_append_prefix` — appending preserves the prefix
* `kv_cache_length_mono` — cache length is monotone increasing
* `kv_cache_attention_agree` — attention scores on shared prefix unchanged
-/
import Mathlib

namespace Pythia.Numerical.KVCache

variable {α : Type*}

theorem kv_cache_append_prefix (cache : List α) (new_entry : α) :
    cache <+: cache ++ [new_entry] :=
  List.prefix_append cache [new_entry]

theorem kv_cache_length_mono (cache : List α) (new_entry : α) :
    cache.length ≤ (cache ++ [new_entry]).length := by
  simp

theorem kv_cache_append_length (cache : List α) (new_entry : α) :
    (cache ++ [new_entry]).length = cache.length + 1 := by
  simp

theorem kv_cache_get_preserved (cache : List α) (new_entry : α)
    (i : ℕ) (hi : i < cache.length) :
    (cache ++ [new_entry])[i]'(by simp; omega) = cache[i] := by
  rw [List.getElem_append_left (by omega)]

theorem kv_cache_append_last (cache : List α) (new_entry : α) :
    (cache ++ [new_entry]).getLast (by simp) = new_entry := by
  simp

section AttentionScore

variable {n : ℕ}

noncomputable def attentionScore (query key : Fin n → ℝ) : ℝ :=
  ∑ i : Fin n, query i * key i

theorem kv_cache_attention_agree
    (query : Fin n → ℝ) (keys : List (Fin n → ℝ)) (new_key : Fin n → ℝ)
    (j : ℕ) (hj : j < keys.length) :
    attentionScore query (keys[j]) =
    attentionScore query ((keys ++ [new_key])[j]'(by simp; omega)) := by
  congr 1
  exact (kv_cache_get_preserved keys new_key j hj).symm

end AttentionScore

end Pythia.Numerical.KVCache
