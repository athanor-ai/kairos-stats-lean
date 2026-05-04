/-
Copyright (c) 2026 Pythia contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Pythia.InformationTheory.DPI

Data-processing inequality (DPI): if X → Y → Z forms a Markov chain
then I(X;Z) ≤ I(X;Y).

## Main results

* `klDiv_map_le` — DPI for KL divergence under deterministic maps:
  processing data through any measurable function cannot increase the
  KL divergence between two measures.

* `data_processing_inequality` — DPI for mutual information:
  for a Markov chain X → Y → Z (modelled via input distribution ν
  and Markov kernels κ₁ : α → β, κ₂ : β → γ), the mutual information
  I(X;Z) ≤ I(X;Y).  Proven via the KL-divergence DPI for stochastic
  kernels from `Pythia.InfoTheory.DataProcessing`.

## References

* Cover, T. M. and Thomas, J. A. "Elements of Information Theory."
  2nd ed. Wiley (2006). Theorem 2.8.1.
-/

import Mathlib
import Pythia.InfoTheory.DataProcessing

open MeasureTheory ProbabilityTheory InformationTheory Measure

open scoped ENNReal

namespace Pythia.InformationTheory

variable {α β γ : Type*} [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]

/-! ### KL-divergence DPI for deterministic maps -/

/-
**DPI for KL divergence under a deterministic map.**

For any measurable function `f` and measures `μ, ν` with `ν ≪ μ`,
mapping through `f` cannot increase the KL divergence:
  `klDiv (ν.map f) (μ.map f) ≤ klDiv ν μ`

This is a corollary of the stochastic DPI (`klDiv_bind_le_klDiv`)
specialised to the deterministic kernel `Kernel.deterministic f`.
-/
theorem klDiv_map_le
    [StandardBorelSpace α] [Nonempty α]
    {f : α → β} (hf : Measurable f)
    (μ ν : Measure α) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hνμ : ν ≪ μ) :
    klDiv (ν.map f) (μ.map f) ≤ klDiv ν μ := by
  rw [ ← MeasureTheory.Measure.bind_dirac_eq_map ];
  · rw [ ← MeasureTheory.Measure.bind_dirac_eq_map ];
    · convert Pythia.InfoTheory.klDiv_bind_le_klDiv ( Kernel.deterministic f hf ) μ ν hνμ using 1;
    · exact hf;
  · exact hf

/-! ### Mutual information via KL divergence -/

/-- **Mutual information** of a joint measure `μ` on `α × β`, defined as
the KL divergence from `μ` to the product of its marginals:
  `MI(μ) = D_KL(μ ∥ μ.fst ⊗ μ.snd)`

When `μ` is the joint distribution of `(X, Y)`, this equals the
classical mutual information `I(X;Y)`.

Citation: Cover–Thomas §2.3. -/
noncomputable def mutualInformationMeasure (μ : Measure (α × β)) : ℝ≥0∞ :=
  klDiv μ (μ.fst.prod μ.snd)

/-! ### Auxiliary kernel for the DPI proof -/

/-- Kernel that processes the second component of a pair through `κ₂`
while keeping the first component fixed:
  `processSecond κ₂ (x, y) = δ_x × κ₂(y)`

This models the Markov transition `(X, Y) ↦ (X, Z)` where `Z | Y ~ κ₂`. -/
noncomputable def processSecond (κ₂ : Kernel β γ) : Kernel (α × β) (α × γ) :=
  (Kernel.deterministic (Prod.fst : α × β → α) measurable_fst) ×ₖ (κ₂.prodMkLeft α)

instance processSecond_isMarkovKernel (κ₂ : Kernel β γ) [IsMarkovKernel κ₂] :
    IsMarkovKernel (processSecond κ₂ : Kernel (α × β) (α × γ)) := by
  unfold processSecond; infer_instance

/-! ### Key measure equalities -/

/-
Binding the joint `ν ⊗ₘ κ₁` through `processSecond κ₂` yields
the joint `ν ⊗ₘ (κ₂ ∘ κ₁)` of `(X, Z)`.
-/
theorem bind_processSecond_compProd
    (ν : Measure α) [IsProbabilityMeasure ν]
    (κ₁ : Kernel α β) [IsMarkovKernel κ₁]
    (κ₂ : Kernel β γ) [IsMarkovKernel κ₂] :
    (ν ⊗ₘ κ₁).bind ↑(processSecond κ₂ : Kernel (α × β) (α × γ))
      = ν ⊗ₘ (κ₂.comp κ₁) := by
  ext s hs;
  have h_lhs : ∫⁻ y, (processSecond κ₂ y) s ∂(ν ⊗ₘ κ₁) = ∫⁻ a, ∫⁻ b, (κ₂ b) (Prod.mk a ⁻¹' s) ∂(κ₁ a) ∂ν := by
    unfold processSecond;
    erw [ MeasureTheory.Measure.lintegral_compProd ];
    · congr! 3;
      ext b; simp +decide [ Kernel.prod_apply, Kernel.deterministic_apply, Kernel.prodMkLeft_apply ] ;
      rw [ MeasureTheory.Measure.prod_apply hs ];
      rw [ MeasureTheory.lintegral_dirac' ];
      exact measurable_measure_prodMk_left hs;
    · convert ( Kernel.measurable_coe ( Kernel.deterministic Prod.fst measurable_fst ×ₖ Kernel.prodMkLeft α κ₂ ) hs ) using 1;
  convert h_lhs using 1;
  · apply_rules [ Measure.bind_apply ];
    fun_prop;
  · convert Measure.compProd_apply hs;
    · rw [ Kernel.comp_apply ];
      rw [ Measure.bind_apply ];
      · exact measurable_prodMk_left hs;
      · fun_prop;
    · infer_instance;
    · infer_instance

/-
Binding the product `ν.prod μ` through `processSecond κ₂` yields
`ν.prod (μ.bind κ₂)`.
-/
theorem bind_processSecond_prod
    (ν : Measure α) [IsFiniteMeasure ν]
    (μ : Measure β) [IsFiniteMeasure μ]
    (κ₂ : Kernel β γ) [IsMarkovKernel κ₂] :
    (ν.prod μ).bind ↑(processSecond κ₂ : Kernel (α × β) (α × γ))
      = ν.prod (μ.bind ↑κ₂) := by
  refine' MeasureTheory.Measure.ext fun s hs => _;
  rw [ MeasureTheory.Measure.bind_apply hs, MeasureTheory.Measure.prod_apply ];
  · erw [ MeasureTheory.lintegral_prod ];
    · congr! 2;
      unfold processSecond;
      rw [ MeasureTheory.Measure.bind_apply ];
      · simp +decide [ Kernel.prod_apply, Kernel.deterministic_apply, Kernel.prodMkLeft_apply ];
        congr! 2;
        rw [ MeasureTheory.Measure.prod_apply hs ];
        rw [ MeasureTheory.lintegral_dirac' ];
        exact measurable_measure_prodMk_left hs;
      · exact measurable_prodMk_left hs;
      · exact Kernel.aemeasurable κ₂;
    · exact (Kernel.measurable_coe (processSecond κ₂) hs).aemeasurable;
  · exact hs;
  · exact (processSecond κ₂).aemeasurable

/-
Binding through a composition of kernels equals successive binding.
-/
theorem bind_comp_eq_bind_bind
    (ν : Measure α) [SFinite ν]
    (κ₁ : Kernel α β) [IsSFiniteKernel κ₁]
    (κ₂ : Kernel β γ) [IsSFiniteKernel κ₂] :
    ν.bind ↑(κ₂.comp κ₁) = (ν.bind ↑κ₁).bind ↑κ₂ := by
  grind +suggestions

/-! ### Data Processing Inequality for Mutual Information -/

/-
**Data-processing inequality (DPI) for mutual information.**

For a Markov chain `X → Y → Z`, modeled by an input distribution `ν`
on `α` and Markov kernels `κ₁ : Kernel α β`, `κ₂ : Kernel β γ`:

  `I(X;Z) ≤ I(X;Y)`

i.e., processing `Y` through channel `κ₂` to obtain `Z` can only
reduce the information about `X`.

The hypothesis `h_ac` encodes that the joint `(X,Y)` is absolutely
continuous with respect to the product of its marginals, which holds
whenever `I(X;Y) < ∞`.  Without this assumption `I(X;Y) = ⊤` and the
inequality is trivially true.

Citation: Cover-Thomas §2.8.1.
-/
theorem data_processing_inequality
    [StandardBorelSpace (α × β)] [Nonempty (α × β)]
    (ν : Measure α) [IsProbabilityMeasure ν]
    (κ₁ : Kernel α β) [IsMarkovKernel κ₁]
    (κ₂ : Kernel β γ) [IsMarkovKernel κ₂]
    (h_ac : ν ⊗ₘ κ₁ ≪ ν.prod (ν.bind ↑κ₁)) :
    mutualInformationMeasure (ν ⊗ₘ (κ₂.comp κ₁))
      ≤ mutualInformationMeasure (ν ⊗ₘ κ₁) := by
  unfold mutualInformationMeasure;
  have h_kl_le : klDiv (ν ⊗ₘ (κ₂.comp κ₁)) (ν.prod (ν.bind κ₁ |> Measure.bind <| ↑κ₂)) ≤ klDiv (ν ⊗ₘ κ₁) (ν.prod (ν.bind κ₁)) := by
    convert Pythia.InfoTheory.klDiv_bind_le_klDiv ( processSecond κ₂ ) ( ν.prod ( ν.bind κ₁ ) ) ( ν ⊗ₘ κ₁ ) _ using 1;
    · rw [ ← bind_processSecond_compProd, ← bind_processSecond_prod ];
    · exact h_ac;
  convert h_kl_le using 1;
  · rw [ Measure.fst_compProd, Measure.snd_compProd, bind_comp_eq_bind_bind ];
  · rw [ MeasureTheory.Measure.fst_compProd, MeasureTheory.Measure.snd_compProd ]

end Pythia.InformationTheory