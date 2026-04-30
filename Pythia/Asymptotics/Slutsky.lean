/-
Slutsky's theorem — asymptotic combinations.

If X_n ⇒ X in distribution and Y_n →_p c (constant), then:
  - X_n + Y_n ⇒ X + c
  - X_n · Y_n ⇒ c · X
  - X_n / Y_n ⇒ X / c (provided c ≠ 0)

This is the workhorse for combining asymptotic-normality results
(e.g. delta method composition, plug-in estimators).

DO NOT restructure files or change namespaces. The expected output
is a sorry-free Lean file declaring `Pythia.Asymptotics.Slutsky.slutsky_addition`
and `slutsky_multiplication` in namespace `Pythia.Asymptotics.Slutsky`.
-/
import Mathlib

open MeasureTheory Filter

namespace Pythia.Asymptotics.Slutsky

variable {Ω ι : Type*} {m : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]
  {l : Filter ι} [l.IsCountablyGenerated]

/-- Slutsky's theorem, addition form. If `X_n` converges to `Z` in
distribution and `Y_n` converges to `c` in probability, then
`X_n + Y_n` converges to `Z + c` in distribution. -/
theorem slutsky_addition
    {X Y : ι → Ω → ℝ} {Z : Ω → ℝ} {c : ℝ}
    (hXZ : TendstoInDistribution X l Z μ)
    (hY : TendstoInMeasure μ Y l (fun _ ↦ c))
    (hY_meas : ∀ i, AEMeasurable (Y i) μ) :
    TendstoInDistribution (fun n ↦ X n + Y n) l (fun ω ↦ Z ω + c) μ :=
  hXZ.add_of_tendstoInMeasure_const hY hY_meas

/-- Slutsky's theorem, multiplication form. If `X_n` converges to `Z` in
distribution and `Y_n` converges to `c` in probability, then
`Y_n * X_n` converges to `c * Z` in distribution. -/
theorem slutsky_multiplication
    {X Y : ι → Ω → ℝ} {Z : Ω → ℝ} {c : ℝ}
    (hXZ : TendstoInDistribution X l Z μ)
    (hY : TendstoInMeasure μ Y l (fun _ ↦ c))
    (hY_meas : ∀ i, AEMeasurable (Y i) μ) :
    TendstoInDistribution (fun n ω ↦ Y n ω * X n ω) l (fun ω ↦ c * Z ω) μ :=
  hXZ.continuous_comp_prodMk_of_tendstoInMeasure_const
    (g := fun (p : ℝ × ℝ) ↦ p.2 * p.1) (by fun_prop) hY hY_meas

end Pythia.Asymptotics.Slutsky
