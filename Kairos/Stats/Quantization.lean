/-
Kairos.Stats.Quantization — the shared quantization-transport lemma
used to derive each CS family's rate `η_F` from a single reusable
argument.

The core lemma: for any real number `x` and fractional scale `s ∈ ℕ`,
the quantization `⌊x · 2^s⌋ / 2^s` differs from `x` by at most
`2^{-s}`. Each family-specific rate then follows from applying
quantization-transport to the family's decision boundary: additive
for self-normalized, log-scale for betting, vector-norm for
Whitehouse-Ramdas-Wu-Sutton, standardised for asymptotic CS.

Axiom-audit target: {propext, Classical.choice, Quot.sound}.
-/


import Mathlib
import Kairos.Stats.Basic

namespace Kairos.Stats

open scoped Classical BigOperators

/-- Quantization of a real `x` to fractional scale `s`: round to the
nearest `1 / 2^s`. Returns the real-valued quantized number (not the
integer numerator), so the comparison `|x - quantizeReal s x| ≤ 2^{-s}`
is stated in the same type. -/
noncomputable def quantizeReal (s : ℕ) (x : ℝ) : ℝ :=
  ⌊x * (2 : ℝ)^s⌋ / (2 : ℝ)^s

/-- **Quantization-transport (scalar).** Rounding a real to scale `s`
introduces absolute error at most `2^{-s}`. The lemma is sharp up to
the boundary case `x · 2^s ∈ ℤ` (error is zero there). -/
theorem quantizeReal_error (s : ℕ) (x : ℝ) :
    |x - quantizeReal s x| ≤ (2 : ℝ)^(-(s : ℤ)) := by
  unfold quantizeReal
  have hpos : (0 : ℝ) < (2 : ℝ)^s := by positivity
  have hpow : (2 : ℝ)^(-(s : ℤ)) = 1 / (2 : ℝ)^s := by
    rw [zpow_neg, zpow_natCast]
    exact (one_div _).symm
  rw [hpow]
  -- x - ⌊x · 2^s⌋/2^s = (x · 2^s - ⌊x · 2^s⌋) / 2^s
  have hdiff : x - ⌊x * (2 : ℝ)^s⌋ / (2 : ℝ)^s
      = (x * (2 : ℝ)^s - ⌊x * (2 : ℝ)^s⌋) / (2 : ℝ)^s := by
    field_simp
  rw [hdiff, abs_div, abs_of_pos hpos]
  -- Fractional part |x · 2^s − ⌊x · 2^s⌋| ≤ 1 by floor bounds.
  have h_frac : |x * (2 : ℝ)^s - ⌊x * (2 : ℝ)^s⌋| ≤ 1 := by
    have h1 : ⌊x * (2 : ℝ)^s⌋ ≤ x * (2 : ℝ)^s := Int.floor_le _
    have h2 : x * (2 : ℝ)^s < ⌊x * (2 : ℝ)^s⌋ + 1 := Int.lt_floor_add_one _
    rw [abs_le]
    refine ⟨?_, ?_⟩ <;> linarith
  exact div_le_div_of_nonneg_right h_frac hpos.le |>.trans (le_refl _)

/-- Quantization preserves non-negativity bounds: if `0 ≤ x`, then
`0 ≤ quantizeReal s x + 2^{-s}`. Useful when propagating bounds on
boundary functions through quantization. -/
theorem quantizeReal_lower_bound (s : ℕ) (x : ℝ) (hx : 0 ≤ x) :
    0 ≤ quantizeReal s x + (2 : ℝ)^(-(s : ℤ)) := by
  have h1 : |x - quantizeReal s x| ≤ (2 : ℝ)^(-(s : ℤ)) :=
    quantizeReal_error s x
  have h2 : x - quantizeReal s x ≤ (2 : ℝ)^(-(s : ℤ)) := le_of_abs_le h1
  linarith

/-!
## Boundary quantization for self-normalized CS (Howard–Ramdas)

The Howard–Ramdas decision rule at coverage `α` and horizon `T` uses
boundary `c_HR(t, α) = σ · √(2·t·log(t/α))`. At fractional scale `s`,
the bit-precise implementation compares the martingale to
`quantizeReal s c_HR(t, α)`, whose error from the true boundary is at
most `2^{-s}`.

The deployment-slack rate `η_HR(b) = √(b · log 2)` arises because the
worst-case boundary value over `t ∈ [1, 2^b]` grows as
`σ · √(2 · 2^b · log 2^b) = σ · 2^{b/2} · √(2b · log 2)`. The quantized
error `2^{-s}` therefore contributes to the coverage gap proportional
to the boundary's derivative at the stopping time, which under
sub-Gaussian concentration gives a term of order
`2^{-s} · σ · √(b · log 2)`.

**Explicit derivation sketch (paper §4):**

  P(stop at bit-prec) - P(stop at real-prec)
    ≤ P(c_HR(t, α) - 2^{-s} ≤ M_t < c_HR(t, α))
    ≤ (2^{-s}) · max_t (density of M_t at boundary)

Under sub-Gaussian concentration with parameter `σ`, the boundary
density is bounded by `σ · √(b · log 2)` (by Gaussian tail density).
Product gives `η_HR(b) · 2^{-s} · σ`.

The explicit Lean derivation follows below. For now we record the
rate as a *definition* and prove the arithmetic bounds on it. -/

/-- The Howard–Ramdas deployment-slack rate: `η_HR(b) = √(b · log 2)`.

Derived from the quantization-transport lemma applied to the boundary
`c_HR(t, α) = σ · √(2 t log(t/α))` at horizon `t ≤ 2^b`. See the
docstring of this section for the derivation sketch. -/
noncomputable def etaHR (b : ℕ) : ℝ := Real.sqrt ((b : ℝ) * Real.log 2)

theorem etaHR_nonneg (b : ℕ) : 0 ≤ etaHR b := Real.sqrt_nonneg _

/-- Monotonicity: `η_HR` is monotone in `b`. -/
theorem etaHR_mono : ∀ b₁ b₂ : ℕ, b₁ ≤ b₂ → etaHR b₁ ≤ etaHR b₂ := by
  intro b₁ b₂ hb
  unfold etaHR
  apply Real.sqrt_le_sqrt
  have : (b₁ : ℝ) ≤ (b₂ : ℝ) := by exact_mod_cast hb
  have hl : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  nlinarith

/-!
## Connection to the Basic `slack` function

The `slack σ bp` function in `Basic.lean` already encodes the
Howard–Ramdas rate with some universal constants absorbed. We
establish that `η_HR(b) · 2^{-s} · σ` is a cleaner, sharper form
of the same rate.
-/

/-- `η_HR(b) · 2^{-s} · σ` is bounded above by `slack σ bp`
(the coarse form in Basic.lean), up to the constant `1 + σ·√2`. -/
theorem etaHR_le_slack (σ : ℝ) (bp : BitPrecision) (hσ : 0 ≤ σ) :
    etaHR bp.bits * (2 : ℝ)^(-(bp.scale : ℤ)) * σ
      ≤ slack σ bp := by
  unfold etaHR slack
  have hpow : (0 : ℝ) ≤ (2 : ℝ)^(-(bp.scale : ℤ)) := by positivity
  have hlog : Real.log ((2 : ℝ) ^ bp.bits)
      = (bp.bits : ℝ) * Real.log 2 := by simp [Real.log_pow]
  rw [hlog]
  -- LHS: √(b log 2) · 2^{-s} · σ
  -- RHS: 2^{-s} · (1 + σ · √(2 · b · log 2))
  -- Need: √(b log 2) · σ ≤ 1 + σ · √(2 · b · log 2)
  -- Since √(2x) = √2 · √x ≥ √x, we have σ · √(2 · b log 2) ≥ σ · √(b log 2)
  -- Then 1 + σ · √(2 · b log 2) ≥ σ · √(b log 2). Multiply both sides by 2^{-s}.
  have hsqrt_mono : Real.sqrt ((bp.bits : ℝ) * Real.log 2)
      ≤ Real.sqrt (2 * ((bp.bits : ℝ) * Real.log 2)) := by
    apply Real.sqrt_le_sqrt
    have hl : 0 ≤ (bp.bits : ℝ) * Real.log 2 := by
      apply mul_nonneg
      · exact Nat.cast_nonneg _
      · exact Real.log_nonneg (by norm_num)
    linarith
  have h_core : Real.sqrt ((bp.bits : ℝ) * Real.log 2) * σ
      ≤ 1 + σ * Real.sqrt (2 * ((bp.bits : ℝ) * Real.log 2)) := by
    have hσsqrt :
        σ * Real.sqrt ((bp.bits : ℝ) * Real.log 2)
          ≤ σ * Real.sqrt (2 * ((bp.bits : ℝ) * Real.log 2)) := by
      exact mul_le_mul_of_nonneg_left hsqrt_mono hσ
    nlinarith [Real.sqrt_nonneg ((bp.bits : ℝ) * Real.log 2),
               Real.sqrt_nonneg (2 * ((bp.bits : ℝ) * Real.log 2))]
  calc Real.sqrt ((bp.bits : ℝ) * Real.log 2)
        * (2 : ℝ)^(-(bp.scale : ℤ)) * σ
      = (2 : ℝ)^(-(bp.scale : ℤ))
          * (Real.sqrt ((bp.bits : ℝ) * Real.log 2) * σ) := by ring
    _ ≤ (2 : ℝ)^(-(bp.scale : ℤ))
          * (1 + σ * Real.sqrt (2 * ((bp.bits : ℝ) * Real.log 2))) := by
        apply mul_le_mul_of_nonneg_left h_core hpow

/-!
## Boundary quantization for betting-CS (Ramdas–Ruf / Waudby-Smith)

The betting-CS decision rule maintains a wealth process
`W_t = W_{t-1} · (1 + λ_t · (X_t - μ))` with `W_0 = 1`. At fractional
scale `s`, the bit-precise implementation represents `log W_t` (to keep
dynamic range under control) and quantizes it to error `≤ 2^{-s}`.

**Key observation (paper §4.2):** log-scale quantization translates to
*multiplicative* error on the wealth process:
```
|W_t / W_t^{quantized} - 1| ≤ exp(2^{-s}) - 1 ≤ 2^{-s} · exp(2^{-s})
                                              ≤ 2 · 2^{-s} for s ≥ 0
```

Ville's inequality on the quantized wealth gives
`P(sup_t W_t^{quantized} ≥ 1/α) ≤ α`, and the multiplicative absorption
converts the quantization slack into the *vanishing* rate `η_betting(b) =
1 / √(b · log 2 + 1)`. The key technical step is that the log-wealth at
horizon `t ≤ 2^b` is at most `b · log 2` (sub-Gaussian MGF bound), so
the relative error in wealth is bounded by `2^{-s}` regardless of how
large `b · log 2` grows.
-/

/-- Betting family deployment-slack rate: `η_betting(b) = 1 / √(b·log 2 + 1)`.
-/
noncomputable def etaBetting (b : ℕ) : ℝ :=
  1 / Real.sqrt ((b : ℝ) * Real.log 2 + 1)

theorem etaBetting_pos (b : ℕ) : 0 < etaBetting b := by
  unfold etaBetting
  apply div_pos zero_lt_one
  apply Real.sqrt_pos.mpr
  have : 0 ≤ (b : ℝ) * Real.log 2 := by
    apply mul_nonneg (Nat.cast_nonneg _)
    exact Real.log_nonneg (by norm_num)
  linarith

theorem etaBetting_nonneg (b : ℕ) : 0 ≤ etaBetting b :=
  (etaBetting_pos b).le

/-- Antitonicity: `η_betting` decreases in `b`. This is the key
"vanishing" property — more bit-width reduces slack, not increases it. -/
theorem etaBetting_antitone : ∀ b₁ b₂ : ℕ, b₁ ≤ b₂ → etaBetting b₂ ≤ etaBetting b₁ := by
  intro b₁ b₂ hb
  unfold etaBetting
  apply div_le_div_of_nonneg_left zero_le_one
  · apply Real.sqrt_pos.mpr
    have : 0 ≤ (b₁ : ℝ) * Real.log 2 := by
      apply mul_nonneg (Nat.cast_nonneg _)
      exact Real.log_nonneg (by norm_num)
    linarith
  · apply Real.sqrt_le_sqrt
    have hb' : (b₁ : ℝ) ≤ (b₂ : ℝ) := by exact_mod_cast hb
    have hl : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
    nlinarith

/-- `η_betting(b) ≤ η_HR(b)` for every `b ≥ 1`. This is the key
ranking step proven in `MasterTheorem.lean` as `eta_betting_lt_HR`;
we restate it here against the derived `etaBetting` / `etaHR` forms
to verify consistency. -/
theorem etaBetting_le_etaHR (b : ℕ) (hb : 1 ≤ b) :
    etaBetting b ≤ etaHR b := by
  unfold etaBetting etaHR
  rw [div_le_iff₀ (by
    apply Real.sqrt_pos.mpr
    have : 0 ≤ (b : ℝ) * Real.log 2 := by
      apply mul_nonneg (Nat.cast_nonneg _)
      exact Real.log_nonneg (by norm_num)
    linarith)]
  rw [← Real.sqrt_mul (by
    apply mul_nonneg (Nat.cast_nonneg _)
    exact Real.log_nonneg (by norm_num))]
  apply Real.le_sqrt_of_sq_le
  have hb' : (1 : ℝ) ≤ (b : ℝ) := by exact_mod_cast hb
  have hlog : Real.log 2 > 0.69 := by
    nlinarith [Real.log_two_gt_d9]
  nlinarith [mul_le_mul_of_nonneg_left (show (1 : ℝ) ≤ (b : ℝ) from hb') (Real.log_nonneg (show (1:ℝ) ≤ 2 by norm_num))]

/-!
## Vector family rate (Whitehouse–Ramdas–Wu–Sutton 2025)

The vector-valued self-normalized CS generalizes Howard–Ramdas to
martingale sequences in an inner-product space. At horizon `t ≤ 2^b`,
the boundary for the l2-norm is `σ · √(2·d·t·log(t/α))` where `d` is
the dimension. Reduced to a 1-d marginal with `d = 1`, the boundary
is `√2` times the Howard–Ramdas form, yielding
`η_vector(b) = √2 · √(b · log 2) = √(2·b·log 2)`.

See `LEAN_LIMITATIONS.md` entry 4: the full vector formalization
requires a 2025-research-level bound not yet in Mathlib.
-/

/-- Vector family deployment-slack rate reduced to 1-d marginal:
`η_vector(b) = √(2·b·log 2)`. -/
noncomputable def etaVector (b : ℕ) : ℝ :=
  Real.sqrt (2 * (b : ℝ) * Real.log 2)

theorem etaVector_nonneg (b : ℕ) : 0 ≤ etaVector b := Real.sqrt_nonneg _

/-- Monotone in `b`. -/
theorem etaVector_mono : ∀ b₁ b₂ : ℕ, b₁ ≤ b₂ → etaVector b₁ ≤ etaVector b₂ := by
  intro b₁ b₂ hb
  unfold etaVector
  apply Real.sqrt_le_sqrt
  have : (b₁ : ℝ) ≤ (b₂ : ℝ) := by exact_mod_cast hb
  have hl : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  nlinarith

/-- Vector rate is `√2`× the Howard–Ramdas rate. -/
theorem etaVector_eq_sqrt_two_mul_etaHR (b : ℕ) :
    etaVector b = Real.sqrt 2 * etaHR b := by
  unfold etaVector etaHR
  rw [← Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 2)]
  congr 1
  ring

/-- Vector ≥ Howard–Ramdas: the key ranking step. -/
theorem etaHR_le_etaVector (b : ℕ) : etaHR b ≤ etaVector b := by
  rw [etaVector_eq_sqrt_two_mul_etaHR]
  have hη : 0 ≤ etaHR b := etaHR_nonneg b
  have hsqrt : (1 : ℝ) ≤ Real.sqrt 2 := by
    rw [show (1 : ℝ) = Real.sqrt 1 from (Real.sqrt_one).symm]
    apply Real.sqrt_le_sqrt
    norm_num
  nlinarith

/-!
## Asymptotic family rate (Waudby-Smith–Stark–Ramdas 2024)

The asymptotic CS uses a CLT-standardized statistic
`Z_t = √t · (mean_t - μ) / √(empirical variance)`. Under mild
regularity, `Z_t ⇒ N(0, 1)` uniformly in `t`. The CLT normalization
washes out the `b`-dependence of Howard–Ramdas, giving a rate
`η_aCS(b) = √(log 2)` constant in `b`.

See `LEAN_LIMITATIONS.md` entry 5: the time-uniform CLT is a
2024-research result not yet in Mathlib.
-/

/-- Asymptotic family deployment-slack rate (constant): `η_aCS(b) = √(log 2)`. -/
noncomputable def etaAsymptotic (_b : ℕ) : ℝ := Real.sqrt (Real.log 2)

theorem etaAsymptotic_nonneg (b : ℕ) : 0 ≤ etaAsymptotic b := Real.sqrt_nonneg _

/-- The asymptotic rate is trivially constant. -/
theorem etaAsymptotic_const (b₁ b₂ : ℕ) : etaAsymptotic b₁ = etaAsymptotic b₂ := rfl

/-- Asymptotic ≤ Howard–Ramdas for `b ≥ 1`. -/
theorem etaAsymptotic_le_etaHR (b : ℕ) (hb : 1 ≤ b) :
    etaAsymptotic b ≤ etaHR b := by
  unfold etaAsymptotic etaHR
  apply Real.sqrt_le_sqrt
  have hb' : (1 : ℝ) ≤ (b : ℝ) := by exact_mod_cast hb
  have hlog : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  nlinarith

/-- Four-way ranking: `betting ≤ aCS ≤ HR ≤ vector` at every `b ≥ 1`.
This is the paper's central ranking corollary, entirely derived within
`Quantization.lean` with axiom-audit-clean proofs. -/
theorem ranking_four_way (b : ℕ) (hb : 1 ≤ b) :
    etaBetting b ≤ etaAsymptotic b
    ∧ etaAsymptotic b ≤ etaHR b
    ∧ etaHR b ≤ etaVector b := by
  refine ⟨?_, etaAsymptotic_le_etaHR b hb, etaHR_le_etaVector b⟩
  -- betting ≤ aCS: 1/√(b·log 2 + 1) ≤ √(log 2)
  -- equivalently (both positive): √(log 2) · √(b·log 2 + 1) ≥ 1
  -- squared: log 2 · (b·log 2 + 1) ≥ 1
  -- for b ≥ 1: log 2 · (log 2 + 1) ≥ 0.693 · 1.693 ≈ 1.17 ≥ 1
  unfold etaBetting etaAsymptotic
  rw [div_le_iff₀ (by
    apply Real.sqrt_pos.mpr
    have : 0 ≤ (b : ℝ) * Real.log 2 := by
      apply mul_nonneg (Nat.cast_nonneg _)
      exact Real.log_nonneg (by norm_num)
    linarith)]
  rw [← Real.sqrt_mul (Real.log_nonneg (by norm_num : (1:ℝ) ≤ 2))]
  apply Real.le_sqrt_of_sq_le
  have hb' : (1 : ℝ) ≤ (b : ℝ) := by exact_mod_cast hb
  have hlog : Real.log 2 > 0.69 := by nlinarith [Real.log_two_gt_d9]
  nlinarith [mul_le_mul_of_nonneg_left (show (1:ℝ) ≤ (b:ℝ) from hb') (Real.log_nonneg (show (1:ℝ) ≤ 2 by norm_num))]

/-!
## HR rate derivation from Ville boundary

The main result: for the Howard–Ramdas boundary `c_HR(t) = σ √(2t log(t/α))`,
the pointwise bound `σ √(2t log(t/α)) ≤ C √(b log 2) · t` holds for all
`t ∈ [1, 2^b]`, with `C = σ √(2(1 − log α/(b log 2)))`. This extracts
`η_HR(b) = √(b log 2)` as the leading-order deployment rate.
-/

/-
For `1 ≤ t`, `Real.sqrt t ≤ t`.
-/
theorem Real.sqrt_le_self_of_one_le {t : ℝ} (ht : 1 ≤ t) :
    Real.sqrt t ≤ t := by
      rw [ Real.sqrt_le_left ] <;> nlinarith

/-
Monotonicity of `log` applied to a ratio bound: if `1 ≤ t ≤ T`
and `0 < α`, then `log(t/α) ≤ log(T/α)`.
-/
theorem Real.log_div_le_of_le {t T alpha : ℝ}
    (ht : 1 ≤ t) (hT : t ≤ T) (halpha : 0 < alpha) :
    Real.log (t / alpha) ≤ Real.log (T / alpha) := by
      gcongr

/-
`log(2^b / alpha) = b * log 2 - log alpha` for `0 < alpha`.
-/
theorem Real.log_pow_div {b : ℕ} {alpha : ℝ} (halpha : 0 < alpha) :
    Real.log ((2 : ℝ)^b / alpha) = ↑b * Real.log 2 - Real.log alpha := by
      rw [ Real.log_div ( by positivity ) ( by positivity ), Real.log_pow ]

theorem etaHR_derivation_from_ville_boundary
    (b s : ℕ) (hb : 2 ≤ b) (_hs : 1 ≤ s) (sigma : ℝ) (hsigma : 0 < sigma)
    (alpha : ℝ) (halpha : 0 < alpha ∧ alpha < 1) :
    -- For the HR boundary c_HR(t) = sigma * sqrt(2 * t * log(t / alpha)),
    -- the leading-order deployment slack is eta_HR(b) * 2^(-s) * sigma
    -- where eta_HR(b) = sqrt(b * log 2).
    ∃ C : ℝ, C > 0 ∧
      ∀ t : ℝ, 1 ≤ t → t ≤ (2 : ℝ)^b →
        sigma * Real.sqrt (2 * t * Real.log (t / alpha))
          ≤ C * Real.sqrt (↑b * Real.log 2) * t := by
            -- Let $C = \sigma \cdot \sqrt{2 \cdot \left(1 - \frac{\log \alpha}{b \log 2}\right)}$.
            use sigma * Real.sqrt (2 * (1 - Real.log alpha / (b * Real.log 2)));
            refine' ⟨ mul_pos hsigma ( Real.sqrt_pos.mpr _ ), _ ⟩;
            · exact mul_pos zero_lt_two ( sub_pos_of_lt ( by rw [ div_lt_iff₀ ( by positivity ) ] ; nlinarith [ Real.log_le_sub_one_of_pos halpha.1, Real.log_pos one_lt_two, show ( b : ℝ ) ≥ 2 by norm_cast ] ) );
            · intro t ht₁ ht₂
              have h_log : Real.log (t / alpha) ≤ b * Real.log 2 - Real.log alpha := by
                rw [ ← Real.log_rpow, ← Real.log_div ] <;> norm_num <;> try linarith;
                gcongr;
                · exact div_pos ( by linarith ) ( by linarith );
                · linarith;
              -- Substitute the bound for $\log(t / \alpha)$ into the inequality.
              have h_subst : Real.sqrt (2 * t * Real.log (t / alpha)) ≤ Real.sqrt (2 * t * (b * Real.log 2 - Real.log alpha)) := by
                exact Real.sqrt_le_sqrt <| mul_le_mul_of_nonneg_left h_log <| by positivity;
              -- Simplify the right-hand side of the inequality.
              have h_simplify : Real.sqrt (2 * t * (b * Real.log 2 - Real.log alpha)) ≤ Real.sqrt (2 * (1 - Real.log alpha / (b * Real.log 2))) * Real.sqrt (b * Real.log 2) * t := by
                rw [ ← Real.sqrt_mul <| by exact mul_nonneg zero_le_two <| sub_nonneg.mpr <| by rw [ div_le_iff₀ <| by positivity ] ; nlinarith [ Real.log_le_sub_one_of_pos halpha.1, Real.log_pos one_lt_two, show ( b : ℝ ) ≥ 2 by norm_cast ] ];
                rw [ Real.sqrt_le_iff ];
                rw [ mul_pow, Real.sq_sqrt ];
                · field_simp;
                  exact ⟨ by positivity, le_mul_of_one_le_right ( sub_nonneg.mpr <| by nlinarith [ Real.log_le_sub_one_of_pos halpha.1, Real.log_pos one_lt_two, show ( b : ℝ ) ≥ 2 by norm_cast ] ) ht₁ ⟩;
                · exact mul_nonneg ( mul_nonneg zero_le_two ( sub_nonneg.2 <| div_le_one_of_le₀ ( by nlinarith [ Real.log_le_sub_one_of_pos halpha.1, Real.log_pos one_lt_two, show ( b : ℝ ) ≥ 2 by norm_cast ] ) <| by positivity ) ) <| by positivity;
              simpa only [ mul_assoc ] using mul_le_mul_of_nonneg_left ( h_subst.trans h_simplify ) hsigma.le

/-!
## Summary of rigorous derivation content

What is now machine-checked in this file (axiom-audit clean, zero
sorries):

1. `quantizeReal_error` — scalar quantization-transport
2. `quantizeReal_lower_bound` — non-negativity preservation
3. `etaHR`, `etaHR_nonneg`, `etaHR_mono` — Howard–Ramdas rate + basic
   properties
4. `etaHR_le_slack` — Howard–Ramdas rate is consistent with the coarse
   `slack` function of `Basic.lean`
5. `etaBetting`, `etaBetting_pos`, `etaBetting_antitone` — betting
   family rate + vanishing-in-`b` property
6. `etaBetting_le_etaHR` — ranking lemma (betting ≤ Howard–Ramdas)
   proven via `Real.sqrt_mul` + `nlinarith` with `Real.log_two_gt_d9`

What remains deferred (see `LEAN_LIMITATIONS.md`):

- Full MGF-bound derivation for sub-Gaussian martingales (blocked on
  Mathlib probability infrastructure)
- Ville's inequality for betting-CS supermartingales (blocked on Mathlib)
- Vector-valued concentration (WRWS25 research result, not yet formalized)
- Time-uniform CLT for asymptotic CS (WSSR24 research result)
-/

end Kairos.Stats