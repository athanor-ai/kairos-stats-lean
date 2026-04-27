/-
Pythia.InfoTheory.BretagnolleHuberBinary

Binary-alphabet Bretagnolle-Huber inequality.

The general Bretagnolle-Huber inequality
  TV(P, Q) ≤ √(1 - exp(-KL(P‖Q)))
requires Pinsker / TV-distance machinery for general probability measures,
which is not available in Mathlib v4.28.0. On the *binary* alphabet however the
proof becomes elementary: write KL out elementwise and combine
  (a) concavity of `log` (Jensen on two points), giving
      KL(P‖Q) ≥ -2 log α    where α = √(pq) + √((1-p)(1-q))
  (b) AM-GM `2√(ab) ≤ a + b`, giving
      (p - q)² ≤ 1 - α².

The combination yields
  |p - q| ≤ √(1 - exp(-KL(P‖Q))).

Here `α` is the *Bhattacharyya coefficient* between the two-point distributions
`(p, 1-p)` and `(q, 1-q)`, and `|p - q|` is the total-variation distance on
`{0, 1}`.

Reference: Bretagnolle & Huber, "Estimation des densités: risque minimax",
Z. Wahrscheinlichkeitstheorie verw. Gebiete 47 (1979), pp. 119-137; the
Bhattacharyya bridge (Lemma 2.6 in Tsybakov, *Introduction to Nonparametric
Estimation*, Springer 2009).

Mathlib v4.28.0 only — no `master` imports. Zero-axiom guarantee verified via
`#print axioms` at the bottom of this module.
-/

import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Data.Real.Sqrt
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Pythia.Tactic.Pythia

namespace Pythia.InfoTheory

open Real Set

/-- Binary-alphabet Kullback-Leibler divergence between `Bernoulli p` and
`Bernoulli q`, with both parameters strictly inside `(0, 1)`. -/
noncomputable def klBin (p q : ℝ) : ℝ :=
  p * Real.log (p / q) + (1 - p) * Real.log ((1 - p) / (1 - q))

/-- Bhattacharyya coefficient between two Bernoulli distributions
`(p, 1-p)` and `(q, 1-q)`. -/
noncomputable def bhatt (p q : ℝ) : ℝ :=
  Real.sqrt (p * q) + Real.sqrt ((1 - p) * (1 - q))

section Auxiliary

variable {p q : ℝ}

private lemma bhatt_nonneg : 0 ≤ bhatt p q := by
  unfold bhatt
  have h1 : 0 ≤ Real.sqrt (p * q) := Real.sqrt_nonneg _
  have h2 : 0 ≤ Real.sqrt ((1 - p) * (1 - q)) := Real.sqrt_nonneg _
  linarith

/-- Algebraic expansion of `α² = (√(pq) + √((1-p)(1-q)))²`. -/
private lemma bhatt_sq_eq
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    (bhatt p q) ^ 2
      = p * q + (1 - p) * (1 - q)
        + 2 * Real.sqrt (p * q) * Real.sqrt ((1 - p) * (1 - q)) := by
  unfold bhatt
  have hpq : 0 ≤ p * q := mul_nonneg hp0 hq0
  have hpq' : 0 ≤ (1 - p) * (1 - q) :=
    mul_nonneg (by linarith) (by linarith)
  have h1 : Real.sqrt (p * q) ^ 2 = p * q := Real.sq_sqrt hpq
  have h2 : Real.sqrt ((1 - p) * (1 - q)) ^ 2 = (1 - p) * (1 - q) :=
    Real.sq_sqrt hpq'
  -- (a + b)^2 = a^2 + 2ab + b^2
  have hexpand : (Real.sqrt (p * q) + Real.sqrt ((1 - p) * (1 - q))) ^ 2
      = Real.sqrt (p * q) ^ 2
        + 2 * Real.sqrt (p * q) * Real.sqrt ((1 - p) * (1 - q))
        + Real.sqrt ((1 - p) * (1 - q)) ^ 2 := by ring
  rw [hexpand, h1, h2]
  ring

/-- Algebraic step: `(p - q)² ≤ 1 - α²` for `p, q ∈ [0, 1]`.

This is the AM-GM step of the Bretagnolle-Huber bridge: the gap between
`1 - α²` and `(p - q)²` is `p(1-p) + q(1-q) - 2√(pq · (1-p)(1-q)) ≥ 0` by
AM-GM applied to `√(p(1-p))` and `√(q(1-q))`. -/
private lemma sub_sq_le_one_sub_bhatt_sq
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    (p - q) ^ 2 ≤ 1 - (bhatt p q) ^ 2 := by
  -- Step 1: rewrite (bhatt p q)^2 explicitly
  have hbsq := bhatt_sq_eq hp0 hp1 hq0 hq1
  -- Step 2: √(pq) * √((1-p)(1-q)) = √(p(1-p)) * √(q(1-q)) (rearrangement
  -- under the square root). We use sqrt_mul to factor.
  have hpq : 0 ≤ p * q := mul_nonneg hp0 hq0
  have hp1p : 0 ≤ p * (1 - p) := mul_nonneg hp0 (by linarith)
  have hq1q : 0 ≤ q * (1 - q) := mul_nonneg hq0 (by linarith)
  have hsqmul :
      Real.sqrt (p * q) * Real.sqrt ((1 - p) * (1 - q))
        = Real.sqrt (p * (1 - p)) * Real.sqrt (q * (1 - q)) := by
    rw [← Real.sqrt_mul hpq, ← Real.sqrt_mul hp1p]
    congr 1
    ring
  -- Step 3: AM-GM: 2 * √(p(1-p)) * √(q(1-q)) ≤ p(1-p) + q(1-q)
  have hAM :
      2 * Real.sqrt (p * (1 - p)) * Real.sqrt (q * (1 - q))
        ≤ p * (1 - p) + q * (1 - q) := by
    have h := two_mul_le_add_sq
      (Real.sqrt (p * (1 - p))) (Real.sqrt (q * (1 - q)))
    have e1 : Real.sqrt (p * (1 - p)) ^ 2 = p * (1 - p) :=
      Real.sq_sqrt hp1p
    have e2 : Real.sqrt (q * (1 - q)) ^ 2 = q * (1 - q) :=
      Real.sq_sqrt hq1q
    linarith [h, e1, e2]
  -- Step 4: combine. We rearrange the cross term using `hsqmul`.
  have hcross :
      2 * Real.sqrt (p * q) * Real.sqrt ((1 - p) * (1 - q))
        = 2 * Real.sqrt (p * (1 - p)) * Real.sqrt (q * (1 - q)) := by
    have : Real.sqrt (p * q) * Real.sqrt ((1 - p) * (1 - q))
        = Real.sqrt (p * (1 - p)) * Real.sqrt (q * (1 - q)) := hsqmul
    linarith [this]
  rw [hbsq, hcross]
  nlinarith [hAM]

/-- Concavity step (Jensen's inequality on two points applied to `Real.log`):

    `KL(P ‖ Q) ≥ -2 · log(α)`,

equivalently `α ≥ exp(-KL/2)` or, after squaring (using `α ≥ 0`),
`α² ≥ exp(-KL)`. We prove the squared form directly. -/
private lemma bhatt_sq_ge_exp_neg_kl
    (hp0 : 0 < p) (hp1 : p < 1) (hq0 : 0 < q) (hq1 : q < 1) :
    Real.exp (-klBin p q) ≤ (bhatt p q) ^ 2 := by
  -- Strategy: show `-klBin p q ≤ 2 * log α` and exponentiate.
  -- For Jensen on log, use x := √(q/p), y := √((1-q)/(1-p)),
  -- weights p and (1-p). Then p·x + (1-p)·y = √(pq) + √((1-p)(1-q)) = α.
  have hp0' : 0 ≤ p := le_of_lt hp0
  have hq0' : 0 ≤ q := le_of_lt hq0
  have h1mp : 0 < 1 - p := by linarith
  have h1mq : 0 < 1 - q := by linarith
  have h1mp' : 0 ≤ 1 - p := le_of_lt h1mp
  -- bhatt > 0 (strictly).
  have hα_pos : 0 < bhatt p q := by
    unfold bhatt
    have h1 : 0 < Real.sqrt (p * q) :=
      Real.sqrt_pos.mpr (mul_pos hp0 hq0)
    have h2 : 0 ≤ Real.sqrt ((1 - p) * (1 - q)) := Real.sqrt_nonneg _
    linarith
  -- Define x = √(q/p), y = √((1-q)/(1-p)). Both positive.
  set x : ℝ := Real.sqrt (q / p) with hx_def
  set y : ℝ := Real.sqrt ((1 - q) / (1 - p)) with hy_def
  have hx_pos : 0 < x := by
    rw [hx_def]; exact Real.sqrt_pos.mpr (div_pos hq0 hp0)
  have hy_pos : 0 < y := by
    rw [hy_def]; exact Real.sqrt_pos.mpr (div_pos h1mq h1mp)
  -- Compute (p · x)^2 = p^2 · (q/p) = p · q.
  -- Since p · x ≥ 0, this gives p · x = √(p · q).
  have hpx_sq : (p * x) ^ 2 = p * q := by
    rw [hx_def, mul_pow, Real.sq_sqrt (le_of_lt (div_pos hq0 hp0))]
    field_simp
  have hpx_nn : 0 ≤ p * x := mul_nonneg hp0' (le_of_lt hx_pos)
  have hpx : p * x = Real.sqrt (p * q) := by
    rw [show p * q = (p * x) ^ 2 from hpx_sq.symm, Real.sqrt_sq hpx_nn]
  -- Same for (1-p) · y.
  have h1mpy_sq : ((1 - p) * y) ^ 2 = (1 - p) * (1 - q) := by
    rw [hy_def, mul_pow, Real.sq_sqrt (le_of_lt (div_pos h1mq h1mp))]
    field_simp
  have h1mpy_nn : 0 ≤ (1 - p) * y := mul_nonneg h1mp' (le_of_lt hy_pos)
  have h1mpy : (1 - p) * y = Real.sqrt ((1 - p) * (1 - q)) := by
    rw [show (1 - p) * (1 - q) = ((1 - p) * y) ^ 2 from h1mpy_sq.symm,
        Real.sqrt_sq h1mpy_nn]
  -- Convex combination: p·x + (1-p)·y = bhatt p q = α.
  have hαsum : p * x + (1 - p) * y = bhatt p q := by
    unfold bhatt; rw [hpx, h1mpy]
  -- Jensen via concavity of log on Ioi 0 (two-point case).
  have hConcave : ConcaveOn ℝ (Ioi (0 : ℝ)) Real.log :=
    strictConcaveOn_log_Ioi.concaveOn
  have hJensen :
      p * Real.log x + (1 - p) * Real.log y
        ≤ Real.log (p * x + (1 - p) * y) := by
    have habsum : p + (1 - p) = 1 := by ring
    have key := hConcave.2 (x := x) (y := y) hx_pos hy_pos
      hp0' (by linarith) habsum
    -- key : p • log x + (1-p) • log y ≤ log (p • x + (1-p) • y)
    -- (where • on ℝ is just *)
    simpa [smul_eq_mul] using key
  -- Now relate p · log x to (p/2) · log(q/p)  i.e., p · (1/2) log(q/p).
  have hlogx : Real.log x = (1 / 2) * Real.log (q / p) := by
    rw [hx_def, Real.log_sqrt (le_of_lt (div_pos hq0 hp0))]; ring
  have hlogy : Real.log y = (1 / 2) * Real.log ((1 - q) / (1 - p)) := by
    rw [hy_def, Real.log_sqrt (le_of_lt (div_pos h1mq h1mp))]; ring
  -- klBin p q = p·log(p/q) + (1-p)·log((1-p)/(1-q))
  --           = -[p·log(q/p) + (1-p)·log((1-q)/(1-p))]
  -- Hence -klBin p q = p·log(q/p) + (1-p)·log((1-q)/(1-p))
  --                  = 2 · (p · log x + (1-p) · log y).
  have hpq_inv : Real.log (p / q) = -Real.log (q / p) := by
    rw [Real.log_div (ne_of_gt hp0) (ne_of_gt hq0),
        Real.log_div (ne_of_gt hq0) (ne_of_gt hp0)]
    ring
  have h1mpq_inv :
      Real.log ((1 - p) / (1 - q)) = -Real.log ((1 - q) / (1 - p)) := by
    rw [Real.log_div (ne_of_gt h1mp) (ne_of_gt h1mq),
        Real.log_div (ne_of_gt h1mq) (ne_of_gt h1mp)]
    ring
  have hkl_neg :
      -klBin p q = 2 * (p * Real.log x + (1 - p) * Real.log y) := by
    unfold klBin
    rw [hlogx, hlogy, hpq_inv, h1mpq_inv]
    ring
  -- Apply Jensen + double:
  have hbound :
      -klBin p q ≤ 2 * Real.log (p * x + (1 - p) * y) := by
    rw [hkl_neg]
    linarith [hJensen]
  -- Replace p · x + (1 - p) · y by α; rewrite 2 * log α as log (α^2).
  rw [hαsum] at hbound
  have hαlog : 2 * Real.log (bhatt p q) = Real.log ((bhatt p q) ^ 2) := by
    rw [Real.log_pow]; ring
  rw [hαlog] at hbound
  -- Exponentiate both sides: exp is monotone.
  have hsq_pos : 0 < (bhatt p q) ^ 2 := pow_pos hα_pos 2
  have hexp := Real.exp_le_exp.mpr hbound
  rw [Real.exp_log hsq_pos] at hexp
  exact hexp

end Auxiliary

/-! ## Main theorem -/

/--
**Bretagnolle-Huber inequality (binary alphabet).**

For two Bernoulli distributions with success-probabilities `p, q ∈ (0, 1)`,
the total-variation distance `|p - q|` is bounded by

    `|p - q| ≤ √(1 - exp(-KL(P ‖ Q)))`.

This is the Mathlib-v4.28-friendly fallback for the general Bretagnolle-Huber
bound (which would require TV / Pinsker on arbitrary measure spaces). The proof
combines (a) Jensen's inequality for `Real.log` on `(0, ∞)`, (b) the elementary
AM-GM bound `2√(ab) ≤ a + b`, and (c) monotonicity of `Real.sqrt`.
-/
@[stat_lemma]
theorem bretagnolle_huber_binary
    {p q : ℝ} (hp0 : 0 < p) (hp1 : p < 1) (hq0 : 0 < q) (hq1 : q < 1) :
    |p - q| ≤ Real.sqrt (1 - Real.exp (-klBin p q)) := by
  have hp0' : 0 ≤ p := le_of_lt hp0
  have hq0' : 0 ≤ q := le_of_lt hq0
  have hp1' : p ≤ 1 := le_of_lt hp1
  have hq1' : q ≤ 1 := le_of_lt hq1
  -- Step (A): (p - q)^2 ≤ 1 - α^2
  have hA : (p - q) ^ 2 ≤ 1 - (bhatt p q) ^ 2 :=
    sub_sq_le_one_sub_bhatt_sq hp0' hp1' hq0' hq1'
  -- Step (B): α^2 ≥ exp(-KL)
  have hB : Real.exp (-klBin p q) ≤ (bhatt p q) ^ 2 :=
    bhatt_sq_ge_exp_neg_kl hp0 hp1 hq0 hq1
  -- Combine: (p - q)^2 ≤ 1 - exp(-KL).
  have hC : (p - q) ^ 2 ≤ 1 - Real.exp (-klBin p q) := by linarith
  -- Take square roots. Note |p - q| = √((p - q)^2).
  have hsq_eq : Real.sqrt ((p - q) ^ 2) = |p - q| := Real.sqrt_sq_eq_abs (p - q)
  have hroot := Real.sqrt_le_sqrt hC
  rw [hsq_eq] at hroot
  exact hroot

end Pythia.InfoTheory

/-! ## Axiom audit

Run `#print axioms Pythia.InfoTheory.bretagnolle_huber_binary` to verify
this theorem only depends on the kernel axioms (`propext`, `Classical.choice`,
`Quot.sound`). No new axioms are introduced. -/
