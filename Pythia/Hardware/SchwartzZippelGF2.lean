/-
Pythia.Hardware.SchwartzZippelGF2 — Schwartz-Zippel over GF(2) for XOR circuit
equivalence checking.

XOR circuit outputs are multilinear polynomials of total degree ≤ 1 over GF(2).
Random simulation with k independent uniform inputs detects inequivalent circuits
with probability ≥ 1 − 2^(−k).  At k = 10 000 the false-positive probability is
< 2^(−10000), which is negligible for any engineering purpose.

The combinatorial form of Schwartz-Zippel is used throughout (counting "bad" points
rather than working with a probability monad).
-/

import Mathlib

namespace Pythia.Hardware.SchwartzZippelGF2

open MvPolynomial Finset Fintype

/-! ## GF(2) basics -/

/-- GF(2) has exactly 2 elements. -/
lemma card_gf2 : Fintype.card (ZMod 2) = 2 := ZMod.card 2

/-- The universe of GF(2) as a Finset has cardinality 2. -/
lemma card_univ_gf2 : #(Finset.univ : Finset (ZMod 2)) = 2 := by
  rw [Finset.card_univ, card_gf2]

/-! ## Schwartz-Zippel over GF(2) -/

/-- **Schwartz-Zippel over GF(2).**
For a nonzero n-variable polynomial `p` over `ZMod 2`, the fraction of
evaluation points in `(ZMod 2)^n` on which `p` vanishes is at most
`p.totalDegree / 2` (as a non-negative rational).

This is a direct specialisation of `MvPolynomial.schwartz_zippel_totalDegree`
to the set `S = Finset.univ` over `ZMod 2`. -/
theorem schwartz_zippel_gf2 {n : ℕ} (p : MvPolynomial (Fin n) (ZMod 2)) (hp : p ≠ 0) :
    (#({f ∈ Fintype.piFinset (fun _ : Fin n => (Finset.univ : Finset (ZMod 2))) |
        eval f p = 0} : Finset _) : ℚ≥0) / (2 ^ n : ℚ≥0) ≤ p.totalDegree / 2 := by
  have key := MvPolynomial.schwartz_zippel_totalDegree (R := ZMod 2) hp
                (Finset.univ : Finset (ZMod 2))
  simp only [card_univ_gf2] at key
  exact key

/-! ## XOR circuits: degree-1 specialisation -/

/-- **False-positive probability per evaluation for XOR circuits.**
For two distinct n-variable polynomials `p`, `q` over `ZMod 2` with
`(p − q).totalDegree ≤ 1` (the case for all XOR-circuit output bits), the
fraction of evaluation points on which they agree (i.e., `p − q` vanishes) is
at most `1 / 2`.

Equivalently: at most half of the 2^n evaluation points are "bad". -/
theorem xor_equiv_prob_bound {n : ℕ}
    (p q : MvPolynomial (Fin n) (ZMod 2))
    (hpq : p ≠ q)
    (hdeg : (p - q).totalDegree ≤ 1) :
    (#({f ∈ Fintype.piFinset (fun _ : Fin n => (Finset.univ : Finset (ZMod 2))) |
        eval f p = eval f q} : Finset _) : ℚ≥0) / (2 ^ n : ℚ≥0) ≤ 1 / 2 := by
  have hne : p - q ≠ 0 := sub_ne_zero.mpr hpq
  -- Rewrite the agreement condition as a vanishing condition on p − q.
  have heq : {f ∈ Fintype.piFinset (fun _ : Fin n => (Finset.univ : Finset (ZMod 2))) |
      eval f p = eval f q} =
    {f ∈ Fintype.piFinset (fun _ : Fin n => (Finset.univ : Finset (ZMod 2))) |
      eval f (p - q) = 0} := by
    ext f; simp [map_sub, sub_eq_zero]
  rw [heq]
  -- Apply the GF(2) Schwartz-Zippel bound, then use degree ≤ 1.
  have hbound := schwartz_zippel_gf2 (p - q) hne
  calc (#({f ∈ Fintype.piFinset (fun _ : Fin n => (Finset.univ : Finset (ZMod 2))) |
              eval f (p - q) = 0} : Finset _) : ℚ≥0) / (2 ^ n : ℚ≥0)
      ≤ (p - q).totalDegree / 2 := hbound
    _ ≤ 1 / 2 := by
        apply div_le_div_of_nonneg_right _ (by norm_num)
        exact_mod_cast hdeg

/-! ## k independent evaluations -/

/-- **k-evaluation false-positive bound.**
For k independent uniform random evaluations of two distinct degree-1 polynomials
`p`, `q` over GF(2), the fraction of "all-agree" joint evaluation points in
`(ZMod 2)^(n × k)` (out of `2^(n*k)` total) is at most `(1/2)^k`.

The domain is `Fin k → (Fin n → ZMod 2)` (k rows of n-bit inputs), the bad
event is that every row evaluates to the same value on both p and q. -/
theorem k_eval_false_positive {n k : ℕ}
    (p q : MvPolynomial (Fin n) (ZMod 2))
    (hpq : p ≠ q)
    (hdeg : (p - q).totalDegree ≤ 1) :
    (#({evals ∈ Fintype.piFinset (fun _ : Fin k =>
            Fintype.piFinset (fun _ : Fin n => (Finset.univ : Finset (ZMod 2)))) |
          ∀ i : Fin k, eval (evals i) p = eval (evals i) q} : Finset _) : ℚ≥0) /
      (2 ^ (n * k) : ℚ≥0) ≤ (1 / 2) ^ k := by
  set S  := Fintype.piFinset (fun _ : Fin n => (Finset.univ : Finset (ZMod 2)))
  set Sk := Fintype.piFinset (fun _ : Fin k => S)
  -- The per-point bound: fraction of bad inputs ≤ 1/2.
  have hper : (#({f ∈ S | eval f p = eval f q} : Finset _) : ℚ≥0) / 2 ^ n ≤ 1 / 2 :=
    xor_equiv_prob_bound p q hpq hdeg
  -- Cardinality of S.
  have hScard : #S = 2 ^ n := by simp [S]
  -- Cardinality of Sk.
  have hSkcard : #Sk = 2 ^ (n * k) := by simp [Sk, S, pow_mul]
  -- Bad subset: all rows are "bad".
  set badS := {f ∈ S | eval f p = eval f q}
  set bad  := {evals ∈ Sk | ∀ i : Fin k, eval (evals i) p = eval (evals i) q}
  -- The bad joint set is contained in piFinset (fun _ => badS).
  have hbad_sub : bad ⊆ Fintype.piFinset (fun _ : Fin k => badS) := by
    intro evals h
    simp only [Finset.mem_filter, Fintype.mem_piFinset, bad, Sk] at h
    simp only [Fintype.mem_piFinset, badS]
    intro i
    exact Finset.mem_filter.mpr ⟨h.1 i, h.2 i⟩
  -- So |bad| ≤ |badS|^k.
  have hbad_le : (#bad : ℚ≥0) ≤ (#badS : ℚ≥0) ^ k := by
    have hle : #bad ≤ #(Fintype.piFinset (fun _ : Fin k => badS)) :=
      Finset.card_le_card hbad_sub
    have heq : #(Fintype.piFinset (fun _ : Fin k => badS)) = #badS ^ k := by
      simp [Fintype.card_piFinset, Fintype.card_fin]
    calc (#bad : ℚ≥0) ≤ #(Fintype.piFinset (fun _ : Fin k => badS)) := by exact_mod_cast hle
      _ = (#badS : ℚ≥0) ^ k := by exact_mod_cast heq
  -- The main bound: #bad / 2^(n*k) ≤ (#badS/2^n)^k ≤ (1/2)^k.
  calc (#bad : ℚ≥0) / (2 : ℚ≥0) ^ (n * k)
      ≤ (#badS : ℚ≥0) ^ k / (2 : ℚ≥0) ^ (n * k) :=
          div_le_div_of_nonneg_right hbad_le (by positivity)
    _ = ((#badS : ℚ≥0) / (2 : ℚ≥0) ^ n) ^ k := by
          rw [div_pow, ← pow_mul]
    _ ≤ (1 / 2) ^ k :=
          pow_le_pow_left₀ (by positivity) hper k

/-! ## Concrete 10 000-evaluation bound -/

/-- **Simulation-based equivalence checking: 10 000 evaluations.**
For two distinct XOR-circuit outputs modelled as degree-1 polynomials over
GF(2) in n variables, 10 000 independent uniform random evaluations give a
false-positive probability (circuits differ but all evaluations agree) at most
`(1/2)^10000 < 2^(−10000)`.

This is the combinatorial statement: the number of "all-agree" joint points
in `(ZMod 2)^(n × 10000)` divided by `2^(10000*n)` is ≤ `(1/2)^10000`. -/
theorem simulation_10k_bound {n : ℕ}
    (p q : MvPolynomial (Fin n) (ZMod 2))
    (hpq : p ≠ q)
    (hdeg : (p - q).totalDegree ≤ 1) :
    (#({evals ∈ Fintype.piFinset (fun _ : Fin 10000 =>
              Fintype.piFinset (fun _ : Fin n => (Finset.univ : Finset (ZMod 2)))) |
            ∀ i : Fin 10000, eval (evals i) p = eval (evals i) q} : Finset _) : ℚ≥0) /
      (2 ^ (n * 10000) : ℚ≥0) ≤ (1 / 2) ^ 10000 :=
  k_eval_false_positive p q hpq hdeg

end Pythia.Hardware.SchwartzZippelGF2
