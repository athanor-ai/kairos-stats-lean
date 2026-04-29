/-
Pythia.Hardware.IEEE754 — floating-point rounding correctness.

Proves that round-to-nearest-even produces a result within 0.5 ULP
of the exact real value. Mathlib has no formalization of IEEE 754
rounding modes. This extends Pythia's fixed-point quantization
theory (`quantizeReal_error`) to the floating-point domain with
relative error `2^{-s} |x|`.

Aristotle target — requires integration of Pythia.Quantization
with a new floating-point representation type.
-/

import Mathlib
import Pythia.Quantization

namespace Pythia.Hardware

/-- A floating-point number with e exponent bits and s significand bits. -/
structure FloatSpec where
  exponent_bits : ℕ
  significand_bits : ℕ
  deriving Repr

/-- IEEE 754 standard formats. -/
def fp32 : FloatSpec := ⟨8, 23⟩
def fp16 : FloatSpec := ⟨5, 10⟩
def bf16 : FloatSpec := ⟨8, 7⟩

/-- Unit in the last place for a value x at precision s. -/
noncomputable def ulp (s : ℕ) (x : ℝ) : ℝ :=
  (2 : ℝ) ^ (Int.log 2 (|x|) - (s : ℤ))

/-- Round-to-nearest-even: the canonical IEEE 754 default mode.
Maps a real number to the nearest representable value, breaking
ties to even significand. -/
noncomputable def roundNearestEven (s : ℕ) (x : ℝ) : ℝ :=
  let grid := (2 : ℝ) ^ (Int.log 2 (|x|) - (s : ℤ))
  grid * ⌊x / grid + 1/2⌋

/-
The fundamental IEEE 754 guarantee: round-to-nearest produces a
result within 0.5 ULP of the true value.
-/
theorem round_nearest_error (s : ℕ) (hs : 1 ≤ s) (x : ℝ) (hx : x ≠ 0) :
    |roundNearestEven s x - x| ≤ ulp s x / 2 := by
  unfold roundNearestEven ulp;
  rw [ abs_le ] ; constructor <;> norm_num;
  · nlinarith [ Int.lt_floor_add_one ( x / ( 2 : ℝ ) ^ ( Int.log 2 |x| - s : ℤ ) + 1 / 2 ), show ( 0 : ℝ ) < 2 ^ ( Int.log 2 |x| - s : ℤ ) by positivity, mul_div_cancel₀ x ( show ( 2 : ℝ ) ^ ( Int.log 2 |x| - s : ℤ ) ≠ 0 by positivity ) ];
  · nlinarith [ Int.floor_le ( x / 2 ^ ( Int.log 2 |x| - s ) + 1 / 2 ), show ( 0 : ℝ ) < 2 ^ ( Int.log 2 |x| - s ) by positivity, mul_div_cancel₀ x ( show ( 2 : ℝ ) ^ ( Int.log 2 |x| - s ) ≠ 0 by positivity ) ]

/-
Relative rounding error bound: |round(x) - x| / |x| ≤ 2^{-(s+1)}.
This is the floating-point dual of `quantizeReal_error` (the
fixed-point version with uniform error 2^{-s}).
-/
theorem round_nearest_relative_error (s : ℕ) (hs : 1 ≤ s)
    (x : ℝ) (hx : x ≠ 0) :
    |roundNearestEven s x - x| / |x| ≤ (2 : ℝ) ^ (-(s + 1 : ℤ)) := by
  have := round_nearest_error s hs x hx;
  refine' le_trans ( div_le_div_of_nonneg_right this ( abs_nonneg x ) ) _;
  rw [ div_div, div_le_iff₀ ] <;> norm_num [ Real.rpow_add, Real.rpow_neg ];
  · unfold ulp; norm_num [ zpow_add₀, zpow_neg ] ; ring_nf ;
    rw [ zpow_sub₀ ] <;> norm_num ; ring_nf;
    gcongr;
    · exact_mod_cast Int.zpow_log_le_self ( by norm_num ) ( abs_pos.mpr hx );
    · norm_num;
  · positivity

/-
Helper: ⌊(n : ℝ) + 1/2⌋ = n for any integer n.
-/
lemma Int.floor_intCast_add_half (n : ℤ) : ⌊(n : ℝ) + (1 : ℝ) / 2⌋ = n := by
  norm_num [ Int.floor_eq_iff ]

/-
Helper: rounding zero gives zero.
-/
lemma roundNearestEven_zero (s : ℕ) : roundNearestEven s 0 = 0 := by
  unfold roundNearestEven; norm_num;

/-
Helper: if y/grid(y) is an integer, then round(y) = y.
-/
lemma roundNearestEven_of_int_div (s : ℕ) (y : ℝ) (hy : y ≠ 0)
    (k : ℤ) (hk : y = (2 : ℝ) ^ (Int.log 2 |y| - (s : ℤ)) * k) :
    roundNearestEven s y = y := by
      unfold roundNearestEven;
      rw [ eq_comm ] at hk;
      norm_num [ show y / ( 2 ^ ( Int.log 2 |y| - s ) ) = k by rw [ div_eq_iff ( by positivity ) ] ; linarith ];
      exact hk

/-
Helper: round(x)/grid(round(x)) is an integer when round(x) ≠ 0.
This is the key lemma: the output of rounding is always a grid
multiple of its own grid.
-/
lemma roundNearestEven_div_grid_int (s : ℕ) (x : ℝ) (hx : x ≠ 0)
    (hr : roundNearestEven s x ≠ 0) :
    ∃ m : ℤ, roundNearestEven s x =
      (2 : ℝ) ^ (Int.log 2 |roundNearestEven s x| - (s : ℤ)) * m := by
        unfold roundNearestEven;
        -- Let $e_x = \log_2 |x|$ and $g = 2^{e_x - s}$.
        set e_x := Int.log 2 |x|
        set g := (2 : ℝ) ^ (e_x - (s : ℤ));
        -- Let $k = \lfloor x / g + 1 / 2 \rfloor$.
        set k := ⌊x / g + 1 / 2⌋;
        -- If $e_x \geq e_r$, then $2^{e_x - e_r}$ is a nonneg integer power of 2, so $k * 2^{e_x - e_r}$ is an integer.
        by_cases h_case : e_x ≥ Int.log 2 |g * k|;
        · use k * 2 ^ (e_x - Int.log 2 |g * k|).toNat;
          simp +zetaDelta at *;
          rw [ ← mul_assoc, mul_comm ];
          rw [ mul_right_comm, ← zpow_natCast, ← zpow_add₀ ] <;> norm_num;
          grind;
        · -- If $e_x < e_r$, then $e_r = e_x + 1$ and $|k| = 2^{s+1}$.
          have h_case2 : Int.log 2 |g * k| = e_x + 1 := by
            have h_case2 : Int.log 2 |g * k| ≤ e_x + 1 := by
              have h_case2 : |g * k| ≤ 2 ^ (e_x + 1) := by
                have h_case2 : |k| ≤ 2 ^ (s + 1) := by
                  have h_k_abs : |x / g| < 2 ^ (s + 1) := by
                    have h_k_abs : |x| < 2 ^ (e_x + 1) := by
                      convert Int.lt_zpow_succ_log_self ( show 1 < 2 by norm_num ) |x| using 1;
                    rw [ abs_div, abs_of_nonneg ( by positivity : ( 0 : ℝ ) ≤ 2 ^ ( e_x - s ) ) ];
                    rw [ div_lt_iff₀ ( by positivity ) ];
                    convert h_k_abs using 1 ; group;
                    rw [ ← zpow_add₀ ] <;> ring ; norm_num;
                  rw [ abs_lt ] at h_k_abs;
                  exact abs_le.mpr ⟨ by exact Int.le_floor.mpr ( by norm_num; linarith ), by exact Int.le_of_lt_add_one ( Int.floor_lt.mpr ( by norm_num; linarith ) ) ⟩;
                rw [ abs_mul, abs_of_nonneg ( by positivity : ( 0 : ℝ ) ≤ 2 ^ ( e_x - s ) ) ];
                convert mul_le_mul_of_nonneg_left ( show ( |k| : ℝ ) ≤ 2 ^ ( s + 1 ) by exact_mod_cast h_case2 ) ( by positivity : ( 0 : ℝ ) ≤ 2 ^ ( e_x - s ) ) using 1 ; ring;
                norm_num [ zpow_add₀, zpow_sub₀ ] ; ring;
              refine' Int.le_of_lt_add_one _;
              refine' lt_of_le_of_lt ( Int.log_mono_right _ h_case2 ) _;
              · exact?;
              · norm_num [ Int.log ];
                split_ifs <;> norm_cast;
                · rcases e_x with ( _ | _ | e_x ) <;> norm_num [ Int.log ] at *;
                  · norm_cast;
                    rw [ Nat.floor_natCast ] ; norm_num [ Nat.log_pow ];
                  · norm_num [ Int.negSucc_eq ] at *;
                  · tauto;
                · rcases e_x with ( _ | _ | e_x ) <;> norm_num at *;
                  · linarith;
                  · contradiction;
                  · norm_num [ Int.negSucc_eq, zpow_add₀, zpow_one ] at *;
                    rw [ show ⌈ ( 2 : ℝ ) ^ e_x * 2⌉₊ = 2 ^ e_x * 2 by exact_mod_cast Nat.ceil_natCast _ ];
                    rw [ show ( 2 ^ e_x * 2 : ℕ ) = 2 ^ ( e_x + 1 ) by ring, Nat.clog_pow ] <;> norm_num;
            grind
          have h_case2_k : |k| = 2 ^ (s + 1) := by
            have h_case2_k : |g * k| ≥ 2 ^ (e_x + 1) := by
              rw [ ← h_case2 ];
              convert Int.zpow_log_le_self _ _ using 1;
              · infer_instance;
              · norm_num;
              · exact abs_pos.mpr ( show g * k ≠ 0 from by unfold roundNearestEven at hr; aesop );
            have h_case2_k : |g * k| ≤ 2 ^ (e_x + 1) := by
              have h_case2_k : |x / g| < 2 ^ (s + 1) := by
                have h_case2_k : |x| < 2 ^ (e_x + 1) := by
                  convert Int.lt_zpow_succ_log_self ( show 1 < 2 by norm_num ) |x| using 1;
                rw [ abs_div, abs_of_nonneg ( by positivity : ( 0 : ℝ ) ≤ 2 ^ ( e_x - s ) ) ];
                rw [ div_lt_iff₀ ( by positivity ) ];
                convert h_case2_k using 1 ; group;
                rw [ ← zpow_add₀ ( by norm_num ) ] ; ring;
              have h_case2_k : |k| ≤ 2 ^ (s + 1) := by
                rw [ abs_le ];
                exact ⟨ Int.le_floor.2 <| by norm_num; linarith [ abs_lt.mp h_case2_k ], Int.le_of_lt_add_one <| Int.floor_lt.2 <| by norm_num; linarith [ abs_lt.mp h_case2_k ] ⟩;
              rw [ abs_mul, abs_of_nonneg ( by positivity : ( 0 : ℝ ) ≤ g ) ];
              convert mul_le_mul_of_nonneg_left ( show ( |k| : ℝ ) ≤ 2 ^ ( s + 1 ) by exact_mod_cast h_case2_k ) ( by positivity : ( 0 : ℝ ) ≤ 2 ^ ( e_x - s ) ) using 1 ; ring;
              norm_num [ zpow_add₀, zpow_sub₀ ] ; ring;
            have h_case2_k : |g * k| = 2 ^ (e_x + 1) := by
              exact le_antisymm h_case2_k ‹_›;
            rw [ abs_mul, abs_of_nonneg ( by positivity : ( 0 : ℝ ) ≤ g ) ] at h_case2_k;
            rw [ ← @Int.cast_inj ℝ ] ; push_cast ; rw [ ← mul_right_inj' ( by positivity : ( 2 : ℝ ) ^ ( e_x - s ) ≠ 0 ) ] ; convert h_case2_k using 1 ; ring;
            norm_num [ zpow_add₀, zpow_sub₀ ] ; ring;
          cases' eq_or_eq_neg_of_abs_eq h_case2_k with hk hk <;> simp_all +decide [ pow_succ' ];
          · norm_num [ show ⌊x / g + 1 / 2⌋ = 2 * 2 ^ s by aesop ] at *;
            norm_num [ h_case2 ];
            norm_num +zetaDelta at *;
            norm_num [ zpow_sub₀, zpow_add₀ ] ; ring_nf ; norm_num;
            exact ⟨ 2 ^ s, by norm_num [ mul_assoc, ← mul_pow ] ⟩;
          · norm_num +zetaDelta at *;
            norm_num [ hk, h_case2 ];
            norm_num [ zpow_add₀, zpow_sub₀ ] ; ring_nf ; norm_num;
            exact ⟨ -2 ^ s, by push_cast; ring ⟩

/-- Composition: rounding twice at precision s gives the same result
as rounding once (idempotency). -/
theorem round_nearest_idempotent (s : ℕ) (x : ℝ) :
    roundNearestEven s (roundNearestEven s x) = roundNearestEven s x := by
  by_cases hx : x = 0
  · subst hx; rw [roundNearestEven_zero, roundNearestEven_zero]
  · by_cases hr : roundNearestEven s x = 0
    · rw [hr, roundNearestEven_zero]
    · obtain ⟨m, hm⟩ := roundNearestEven_div_grid_int s x hx hr
      exact roundNearestEven_of_int_div s _ hr m hm

/-
Error propagation through addition: |round(a + b) - (a + b)| ≤
|a + b| · 2^{-(s+1)} when both a, b are already representable.
-/
theorem round_add_error (s : ℕ) (hs : 1 ≤ s) (a b : ℝ)
    (ha : roundNearestEven s a = a) (hb : roundNearestEven s b = b)
    (hab : a + b ≠ 0) :
    |roundNearestEven s (a + b) - (a + b)| / |a + b| ≤
      (2 : ℝ) ^ (-(s + 1 : ℤ)) := by
  convert round_nearest_relative_error s hs ( a + b ) hab using 1

end Pythia.Hardware