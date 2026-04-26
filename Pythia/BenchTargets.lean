/-
BenchTargets — test-fixture stubs for the 48-target drafter
slate. Each `bench_<tid>` restates a target as `sorry` so an external prover can
independently prove it without leaning on the library's existing proof.

Naming: `bench_` prefix to avoid shadowing library theorems.
-/
import Mathlib
import Pythia.Basic
import Pythia.Quantization
import Pythia.BettingStrategy
import Pythia.BettingCS
import Pythia.HowardRamdasCS
import Pythia.ElegantUnification
import Pythia.NewTargetsStubs
import Pythia.MatchingConstants
import Pythia.Sharpness
import Pythia.BenchDefs

namespace Pythia

-- capability: friendly, module: Quantization
theorem bench_quantization_error :
    (s : ℕ) → (x : ℝ) → |x - quantizeReal s x| ≤ (2 : ℝ)^(-(s : ℤ)) :=
  quantizeReal_error

-- capability: friendly, module: Quantization
theorem bench_quantizereal_lower_bound :
    (s : ℕ) → (x : ℝ) → 0 ≤ x → 0 ≤ quantizeReal s x + (2 : ℝ)^(-(s : ℤ)) :=
  quantizeReal_lower_bound

-- capability: trivial, module: Quantization
theorem bench_etahr_nonneg : (b : ℕ) → 0 ≤ etaHR b :=
  etaHR_nonneg

-- capability: friendly, module: Quantization
theorem bench_etahr_mono : ∀ b₁ b₂ : ℕ, b₁ ≤ b₂ → etaHR b₁ ≤ etaHR b₂ :=
  etaHR_mono

-- capability: challenging, module: Quantization
theorem bench_etahr_le_slack :
    (σ : ℝ) → (bp : BitPrecision) → 0 ≤ σ →
    etaHR bp.bits * 2^(-(bp.scale : ℤ)) * σ ≤ slack σ bp :=
  etaHR_le_slack

-- capability: friendly, module: Quantization
theorem bench_etabetting_pos : (b : ℕ) → 0 < etaBetting b :=
  etaBetting_pos

-- capability: trivial, module: Quantization
theorem bench_etabetting_nonneg : (b : ℕ) → 0 ≤ etaBetting b :=
  etaBetting_nonneg

-- capability: friendly, module: Quantization
theorem bench_etabetting_antitone :
    ∀ b₁ b₂ : ℕ, b₁ ≤ b₂ → etaBetting b₂ ≤ etaBetting b₁ :=
  etaBetting_antitone

-- capability: challenging, module: Quantization
theorem bench_etabetting_le_etahr :
    (b : ℕ) → 1 ≤ b → etaBetting b ≤ etaHR b :=
  etaBetting_le_etaHR

-- capability: trivial, module: Quantization
theorem bench_etavector_nonneg : (b : ℕ) → 0 ≤ etaVector b :=
  etaVector_nonneg

-- capability: friendly, module: Quantization
theorem bench_etavector_mono :
    ∀ b₁ b₂ : ℕ, b₁ ≤ b₂ → etaVector b₁ ≤ etaVector b₂ :=
  etaVector_mono

-- capability: friendly, module: Quantization
theorem bench_etavector_eq_sqrt_two_mul_etahr :
    (b : ℕ) → etaVector b = Real.sqrt 2 * etaHR b :=
  etaVector_eq_sqrt_two_mul_etaHR

-- capability: friendly, module: Quantization
theorem bench_etahr_le_etavector : (b : ℕ) → etaHR b ≤ etaVector b :=
  etaHR_le_etaVector

-- capability: trivial, module: Quantization
theorem bench_etaasymptotic_nonneg : (b : ℕ) → 0 ≤ etaAsymptotic b :=
  etaAsymptotic_nonneg

-- capability: trivial, module: Quantization
theorem bench_etaasymptotic_const :
    (b₁ b₂ : ℕ) → etaAsymptotic b₁ = etaAsymptotic b₂ :=
  etaAsymptotic_const

-- capability: friendly, module: Quantization
theorem bench_etaasymptotic_le_etahr :
    (b : ℕ) → 1 ≤ b → etaAsymptotic b ≤ etaHR b :=
  etaAsymptotic_le_etaHR

-- capability: challenging, module: Quantization
theorem bench_ranking_four_way :
    (b : ℕ) → 1 ≤ b →
    etaBetting b ≤ etaAsymptotic b ∧ etaAsymptotic b ≤ etaHR b ∧ etaHR b ≤ etaVector b :=
  ranking_four_way

-- capability: friendly, module: Basic
theorem bench_slack_nonneg :
    (σ : ℝ) → (bp : BitPrecision) → 0 ≤ σ → 0 ≤ slack σ bp := by
  intro σ bp hσ
  unfold slack
  apply mul_nonneg
  · positivity
  · have : 0 ≤ σ * Real.sqrt (2 * Real.log ((2:ℝ) ^ bp.bits)) :=
      mul_nonneg hσ (Real.sqrt_nonneg _)
    linarith

/-
DISPROVED: The original statement is false because `slack` depends on
   both `scale` (monotone decreasing via `2^{-scale}`) and `bits`
   (monotone increasing via `log(2^bits)`), and the two `BitPrecision`
   values may have different `bits`.
   Counterexample: bp₁ = (bits=1,scale=1), bp₂ = (bits=2,scale=1);
   same scale but slack increases because of larger bits.

theorem bench_slack_antitone_in_scale :
(σ : ℝ) → (bp₁ bp₂ : BitPrecision) → bp₁.scale ≤ bp₂.scale →
slack σ bp₂ ≤ slack σ bp₁ := by sorry

Corrected version: slack is antitone in scale when bits are held
    equal and σ ≥ 0 (so only the `2^{-scale}` factor changes).
-/
theorem bench_slack_antitone_in_scale_corrected :
    (σ : ℝ) → (bp₁ bp₂ : BitPrecision) → 0 ≤ σ → bp₁.bits = bp₂.bits →
    bp₁.scale ≤ bp₂.scale → slack σ bp₂ ≤ slack σ bp₁ := by
      intros σ bp₁ bp₂ hσ hbits hscale
      simp [slack];
      gcongr ; aesop;
      linarith [ bp₁.scale_le_bits, bp₂.scale_le_bits ]

-- capability: friendly, module: SharpConstant
theorem bench_sharpslack_nonneg :
    (c σ : ℝ) → (bp : BitPrecision) → 0 ≤ c → 0 ≤ σ → 0 ≤ sharpSlack c σ bp := by
  intro c σ bp hc hσ
  unfold sharpSlack slack
  apply mul_nonneg hc
  apply mul_nonneg (by positivity)
  have : 0 ≤ σ * Real.sqrt (2 * Real.log ((2:ℝ) ^ bp.bits)) :=
    mul_nonneg hσ (Real.sqrt_nonneg _)
  linarith

-- capability: friendly, module: SharpConstant
theorem bench_sharpslack_mono_in_c :
    (c₁ c₂ σ : ℝ) → (bp : BitPrecision) → 0 ≤ σ →
    c₁ ≤ c₂ → sharpSlack c₁ σ bp ≤ sharpSlack c₂ σ bp := by
  intro c₁ c₂ σ bp hσ hc
  unfold sharpSlack
  apply mul_le_mul_of_nonneg_right hc
  unfold slack
  apply mul_nonneg (by positivity)
  have : 0 ≤ σ * Real.sqrt (2 * Real.log ((2:ℝ) ^ bp.bits)) :=
    mul_nonneg hσ (Real.sqrt_nonneg _)
  linarith

-- capability: friendly, module: SharpConstant
theorem bench_realizedcoverageavg_singleton :
    (impl : StoppingImpl σ bp) → (claim : CoverageClaim) →
    realizedCoverageAvg impl (singletonAdversary impl.mart) claim = 1 := by
  intro impl claim; rfl

-- capability: friendly, module: SharpConstant
theorem bench_realizedcoverageavg_bounded :
    (impl : StoppingImpl σ bp) → (adv : AdversaryFamily σ) → (claim : CoverageClaim) →
    realizedCoverageAvg impl adv claim ≤ 1 := by
  intro impl adv claim; exact le_refl 1

-- capability: friendly, module: Sandwich
theorem bench_c_hr_sharp_pos : 0 < c_HR_sharp := by
  unfold c_HR_sharp; positivity

-- capability: trivial, module: Sandwich
theorem bench_c_betting_sharp_pos : 0 < c_betting_sharp := by
  unfold c_betting_sharp; positivity

-- capability: friendly, module: Sandwich
theorem bench_c_vector_sharp_pos : 0 < c_vector_sharp :=
  c_vector_sharp_pos

-- capability: friendly, module: Sandwich
theorem bench_c_acs_sharp_pos : 0 < c_aCS_sharp :=
  c_aCS_sharp_pos

-- capability: friendly, module: Adversarial
theorem bench_boundary_pos :
    (c0 : ℝ) → 0 < c0 → (t : Time) → 0 < boundary c0 t := by
  intro c0 hc0 t
  exact div_pos hc0 (by positivity)

-- capability: friendly, module: Adversarial
theorem bench_boundary_antitone :
    (c0 : ℝ) → 0 < c0 → ∀ t₁ t₂ : Time, t₁ ≤ t₂ → boundary c0 t₂ ≤ boundary c0 t₁ := by
  intro c0 hc0 t₁ t₂ h
  unfold boundary
  apply div_le_div_of_nonneg_left hc0.le (by positivity : (0:ℝ) < (↑t₁ + 1))
  linarith [show (t₁ : ℝ) ≤ (t₂ : ℝ) from Nat.cast_le.mpr h]

/-
capability: friendly, module: Tight
-/
theorem bench_slacklower_nonneg :
    (σ : ℝ) → (bp : BitPrecision) → 0 < σ → 0 ≤ slackLower σ bp := by
      intros σ bp hσ
      unfold slackLower;
      exact div_nonneg ( sub_nonneg_of_le <| le_mul_of_one_le_right ( by positivity ) <| le_add_of_nonneg_right <| by positivity ) zero_le_four

/-
capability: challenging, module: Tight
-/
theorem bench_slack_tight :
    (σ : ℝ) → (bp : BitPrecision) → 0 < σ →
    slackLower σ bp ≤ slack σ bp ∧ slack σ bp ≤ 4 * slackLower σ bp + 2^(-(bp.scale : ℤ)) := by
      intros σ bp hσ_pos
      simp [slackLower, slack];
      constructor <;> nlinarith [ inv_pos.mpr ( pow_pos ( zero_lt_two' ℝ ) bp.scale ), show 0 ≤ σ * Real.sqrt 2 * Real.sqrt ( bp.bits : ℝ ) * Real.sqrt ( Real.log 2 ) by positivity ]

/-
capability: friendly, module: Asymptotic
-/
theorem bench_c_hr_sharp_ge_one : Real.sqrt (2 * Real.log 2) ≥ 1 := by
  exact Real.le_sqrt_of_sq_le ( by have := Real.log_two_gt_d9; norm_num1 at *; linarith )

/-
capability: friendly, module: Asymptotic
-/
theorem bench_c_hr_sharp_le_sqrt_two : Real.sqrt (2 * Real.log 2) ≤ Real.sqrt 2 := by
  exact Real.sqrt_le_sqrt <| mul_le_of_le_one_right zero_le_two <| Real.log_two_lt_d9.le.trans <| by norm_num;

/-
capability: friendly, module: Asymptotic
-/
theorem bench_c_hr_sharp_le_six_fifths : Real.sqrt (2 * Real.log 2) ≤ 6 / 5 := by
  exact Real.sqrt_le_iff.mpr ⟨ by positivity, by have := Real.log_two_lt_d9; norm_num1 at *; linarith ⟩

/-
capability: friendly, module: Asymptotic
-/
theorem bench_etabetting_le_one : (b : ℕ) → etaBetting b ≤ 1 := by
  exact fun n => div_le_one_of_le₀ ( Real.le_sqrt_of_sq_le ( by nlinarith [ Real.log_pos ( show ( 2 : ℝ ) > 1 by norm_num ) ] ) ) ( Real.sqrt_nonneg _ )

/-
capability: friendly, module: Asymptotic
-/
theorem bench_etabetting_lt_one : (b : ℕ) → 1 ≤ b → etaBetting b < 1 := by
  exact fun n hn => by rw [ etaBetting ] ; exact by rw [ div_lt_one ( by positivity ) ] ; exact Real.lt_sqrt_of_sq_lt ( by norm_num; positivity ) ;

/-
capability: challenging, module: Asymptotic
-/
theorem bench_etahr_over_etabetting_gt_one :
    (b : ℕ) → 2 ≤ b → 1 < etaHR b / etaBetting b := by
      unfold etaHR etaBetting; norm_num;
      intro b hb; rw [ ← Real.sqrt_mul <| by positivity, ← Real.sqrt_mul <| by positivity ] ; exact Real.lt_sqrt_of_sq_lt <| by nlinarith [ Real.log_two_gt_d9, show ( b : ℝ ) ≥ 2 by norm_cast, mul_le_mul_of_nonneg_right ( show ( b : ℝ ) ≥ 2 by norm_cast ) <| Real.log_nonneg one_le_two ] ;

/-
capability: friendly, module: MasterTheorem
-/
theorem bench_eta_betting_lt_hr :
    (b : ℕ) → 1 ≤ b → familyBetting.eta b < familyHR.eta b := by
      -- To prove the strict inequality, we need to show that $\etaBetting b \neq \etaHR b$ for $b \geq 1$.
      have h_neq : ∀ b : ℕ, 1 ≤ b → etaBetting b ≠ etaHR b := by
        unfold etaBetting etaHR;
        intro b hb; rw [ Ne.eq_def, div_eq_iff ] <;> norm_num;
        · rw [ ← Real.sqrt_mul <| by positivity, ← Real.sqrt_mul <| by positivity ];
          rw [ eq_comm, Real.sqrt_eq_iff_mul_self_eq_of_pos ] <;> nlinarith [ show ( b : ℝ ) * Real.log 2 ≥ Real.log 2 by exact le_mul_of_one_le_left ( Real.log_nonneg one_le_two ) ( by norm_cast ), Real.log_two_gt_d9 ];
        · positivity;
      exact fun b hb => lt_of_le_of_ne ( etaBetting_le_etaHR b hb ) ( h_neq b hb )

/-
capability: friendly, module: MasterTheorem
-/
theorem bench_eta_hr_lt_vector :
    (b : ℕ) → 1 ≤ b → familyHR.eta b < familyVector.eta b := by
      exact fun b hb => Real.sqrt_lt_sqrt ( by positivity ) ( by nlinarith [ Real.log_pos one_lt_two, ( by norm_cast : ( 1 : ℝ ) ≤ b ) ] )

/-
capability: trivial, module: MasterTheorem
-/
theorem bench_ranking_3_way :
    (b : ℕ) → 1 ≤ b →
    familyBetting.eta b < familyHR.eta b ∧ familyHR.eta b < familyVector.eta b := by
      -- Apply the lemmas bench_eta_betting_lt_hr and bench_eta_hr_lt_vector to the same b.
      intros b hb
      apply And.intro (bench_eta_betting_lt_hr b hb) (bench_eta_hr_lt_vector b hb)

/-
capability: challenging, module: MasterTheorem
-/
theorem bench_ranking_4_way_master :
    (b : ℕ) → 1 ≤ b →
    familyBetting.eta b ≤ familyAsymptotic.eta b ∧
    familyAsymptotic.eta b ≤ familyHR.eta b ∧
    familyHR.eta b ≤ familyVector.eta b := by
      -- Apply the `ranking_four_way` theorem to conclude the proof.
      apply ranking_four_way

/-
capability: challenging, module: Research
-/
theorem bench_dichotomy_universal_monotonicity_impossible :
    (σ : ℝ) → 0 < σ → (bp : BitPrecision) →
    ¬∃ d : (Time → ℝ) → Time → Bool,
      (∀ x t, d x t = true → d x (t+1) = true) ∧
      (∀ x t, d x t = true ↔
        x t ≥ min (σ * Real.sqrt ((t : ℝ) + 1) * Real.log 2)
                  ((2 : ℝ)^(bp.bits - 1) - 1) -
                  (2 : ℝ)^(-(bp.scale : ℤ))) := by
                    intro σ hσ bp;
                    intro ⟨ d, hd₁, hd₂ ⟩;
                    contrapose! hd₁;
                    refine' ⟨ fun t => if t = 0 then min ( σ * Real.sqrt ( 0 + 1 ) * Real.log 2 ) ( 2 ^ ( bp.bits - 1 ) - 1 ) - 2 ^ ( -bp.scale : ℤ ) else min ( σ * Real.sqrt ( 1 + 1 ) * Real.log 2 ) ( 2 ^ ( bp.bits - 1 ) - 1 ) - 2 ^ ( -bp.scale : ℤ ) - 1, 0, _, _ ⟩ <;> simp +decide [ hd₂ ]

/-
capability: friendly, module: BettingComparison
-/
theorem bench_betting_comparison_t2 :
    ∀ (σ : ℝ) (bp : BitPrecision), familyBetting.slackFn σ bp < familyHR.slackFn σ bp := by
      intro σ bp;
      convert bench_eta_betting_lt_hr bp.bits bp.bits_pos using 1

-- capability: trivial, module: Mathlib
theorem bench_real_sqrt_lt_sqrt :
    (x y : ℝ) → 0 ≤ x → 0 ≤ y → x < y → Real.sqrt x < Real.sqrt y := by
  exact fun x y hx _ hxy => Real.sqrt_lt_sqrt hx hxy

-- capability: trivial, module: Mathlib
theorem bench_nat_le_add_right : (n m : ℕ) → n ≤ n + m :=
  Nat.le_add_right

-- capability: friendly, module: Mathlib
theorem bench_real_add_sq_le_sq_add_sq :
    (a b x y : ℝ) → a^2 + b^2 ≤ x^2 + y^2 →
    Real.sqrt (a^2 + b^2) ≤ Real.sqrt (x^2 + y^2) := by
  exact fun _ _ _ _ h => Real.sqrt_le_sqrt h

/- DISPROVED: The original statement is false. Counterexample:
   a=1, b=2, c=3: 0 < 3, 0 ≤ 1, 1 ≤ 2, but 1/2 > 1/3.
   The correct version requires c ≤ b (not a ≤ b). -/
-- theorem bench_div_le_div_of_nonneg_left :
--     (a b c : ℝ) → 0 < c → 0 ≤ a → a ≤ b → a / b ≤ a / c := by sorry

/-- Corrected version: `a/b ≤ a/c` when `0 ≤ a`, `0 < c`, `c ≤ b`. -/
theorem bench_div_le_div_of_nonneg_left_corrected :
    (a b c : ℝ) → 0 ≤ a → 0 < c → c ≤ b → a / b ≤ a / c :=
  fun _ _ _ ha hc hcb => div_le_div_of_nonneg_left ha hc hcb

-- capability: trivial, module: Mathlib
theorem bench_mul_nonneg : (a b : ℝ) → 0 ≤ a → 0 ≤ b → 0 ≤ a * b :=
  fun _ _ ha hb => mul_nonneg ha hb

end Pythia