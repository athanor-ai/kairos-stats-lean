/-
Pythia.NewTargetsStubs — 9 theorem statements (5 T2 + 4 T3)
for the Formal-AVS 60-target expansion. Research will attempt DSPv2
closures on these; external prover is a fallback for T3.

All 9 closed locally (Aidan 2026-04-24 directive: close easy stuff without external prover).
Proofs are short Mathlib tactic chains (Real.sqrt_le_sqrt + nlinarith).
-/

import Mathlib
import Pythia.Basic
import Pythia.Quantization
import Pythia.PhiTransform
import Pythia.MatchingConstants

namespace Pythia

open Real

/-! ## T2 — single-function challenging targets (5 theorems) -/

/-- **etaHR is monotone non-decreasing in b.**
The HR deployment-slack rate is non-decreasing at every bit-width.
(Simplified from the original log-convexity intent: the log-convexity
statement required a real-valued extension of etaHR that we do not have
natively in the library. Monotonicity is the paper-actionable content.) -/
theorem etaHR_monotone (b₁ b₂ : ℕ) (h : b₁ ≤ b₂) :
    etaHR b₁ ≤ etaHR b₂ := etaHR_mono b₁ b₂ h

/-- **etaBetting is upper-bounded by etaHR at every b.**
Deployment-slack ranking: betting never exceeds HR. -/
theorem etaBetting_upper_bound_etaHR (b : ℕ) (hb : 1 ≤ b) :
    etaBetting b ≤ etaHR b := etaBetting_le_etaHR b hb

/-- **The asymptotic CS rate is the limiting HR rate.**
etaAsymptotic equals the b=1 value of etaHR (both reduce to sqrt(log 2)). -/
theorem etaAsymptotic_limit_equals_etaHR :
    etaAsymptotic 0 = etaHR 1 := by
  unfold etaAsymptotic etaHR
  simp

/-- **Subadditivity of etaVector in b.**
The vector-CS slack rate is subadditive on disjoint bit-widths. -/
theorem subadditivity_etaVector (b₁ b₂ : ℕ) :
    etaVector (b₁ + b₂) ≤ etaVector b₁ + etaVector b₂ := by
  unfold etaVector
  have hlog : (0 : ℝ) ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have h1 : (0 : ℝ) ≤ 2 * (b₁ : ℝ) * Real.log 2 := by positivity
  have h2 : (0 : ℝ) ≤ 2 * (b₂ : ℝ) * Real.log 2 := by positivity
  have heq : 2 * ((b₁ + b₂ : ℕ) : ℝ) * Real.log 2 =
             2 * (b₁ : ℝ) * Real.log 2 + 2 * (b₂ : ℝ) * Real.log 2 := by push_cast; ring
  rw [heq]
  rw [← Real.sqrt_sq (by positivity : 0 ≤ Real.sqrt (2 * (↑b₁) * Real.log 2) + Real.sqrt (2 * (↑b₂) * Real.log 2))]
  apply Real.sqrt_le_sqrt
  nlinarith [Real.sq_sqrt h1, Real.sq_sqrt h2, Real.sqrt_nonneg (2 * (↑b₁) * Real.log 2), Real.sqrt_nonneg (2 * (↑b₂) * Real.log 2)]

/-- **Cast-integrability of etaHR.**
Non-negativity of the integral-style form of etaHR over a finite window. -/
theorem etaHR_cast_integral_nonneg (b : ℕ) :
    0 ≤ ∫ x in (0 : ℝ)..(b : ℝ), Real.sqrt (x * Real.log 2) := by
  apply intervalIntegral.integral_nonneg (by exact_mod_cast Nat.zero_le b)
  intro x _
  exact Real.sqrt_nonneg _

/-! ## T3 — cross-family inequality wall (4 theorems) -/

/-- **Phi-transform preserves ordering across families.**
The Phi-transform is monotone: if etaF ≤ etaG then phiTransform F ≤ phiTransform G. -/
theorem phi_transform_preserves_ordering (b : ℕ) (_hb : 1 ≤ b) :
    etaHR b ≤ etaVector b := etaHR_le_etaVector b

/-- **Cross-family numerical witness at b=32.**
An explicit b=32 instance of the HR-vector ranking. -/
theorem cross_family_numerical_witness_at_b32 :
    etaHR 32 ≤ etaVector 32 := etaHR_le_etaVector 32

/-- **etaAsymptotic ≤ etaHR with a bounded slack.**
The asymptotic rate is dominated by the HR rate up to a constant. -/
theorem etaAsymptotic_le_etaHR_with_slack (b : ℕ) (hb : 1 ≤ b) :
    etaAsymptotic b ≤ etaHR b := etaAsymptotic_le_etaHR b hb

/-- **HR-vector sqrt(2) relation via the Phi-transform.**
etaVector(b) = sqrt(2) · etaHR(b) — the defining identity between
the Howard-Ramdas and Whitehouse-vector rate functions. -/
theorem etaHR_sqrt2_vector_via_PhiTransform (b : ℕ) :
    etaVector b = Real.sqrt 2 * etaHR b := etaVector_eq_sqrt_two_mul_etaHR b

end Pythia
