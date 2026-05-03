/-
Copyright (c) 2026 Pythia contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Randomized Controlled Trial — Mean Identifiability

Under RCT randomization, treatment assignment T and outcome Y are independent,
so E[T·Y] = E[T]·E[Y]. This is the key mean-identifiability result that underpins
the unconfounded causal effect estimation in randomized experiments.

## Main results

* `rct_mean_identifiability` — RCT independence implies E[T·Y] = E[T]·E[Y].

## References

* Rubin, D.B. "Estimating causal effects of treatments in randomized and
  nonrandomized studies." *Journal of Educational Psychology* 66(5): 688-701 (1974).
* Imbens, G.W. and Rubin, D.B. *Causal Inference for Statistics, Social, and
  Biomedical Sciences*. Cambridge University Press (2015), Theorem 3.2.
-/
import Mathlib
import Pythia.Tactic.Pythia

open MeasureTheory ProbabilityTheory

namespace Pythia.Bio.RCT

/-!
## RCT mean identifiability

In a perfectly randomized trial, treatment assignment T is independent of potential
outcomes Y. This independence (formalized as `IndepFun T Y μ`) implies that the
expectation of the product equals the product of expectations:

    E[T·Y] = E[T]·E[Y].

This is the algebraic core of the Rubin causal model identification argument.
-/

/-- **RCT mean identifiability.**
When treatment indicator `T` and outcome `Y` are independent random variables
(as guaranteed by RCT randomization), the expectation of their product equals
the product of their expectations. -/
@[stat_lemma]
theorem rct_mean_identifiability {Ω : Type*} {mΩ : MeasurableSpace Ω}
    (μ : MeasureTheory.Measure Ω) [MeasureTheory.IsProbabilityMeasure μ]
    (T Y : Ω → ℝ) (hT : Measurable T) (hY : Measurable Y)
    (h_indep : ProbabilityTheory.IndepFun T Y μ) :
    MeasureTheory.integral μ (fun ω => T ω * Y ω) =
    MeasureTheory.integral μ T * MeasureTheory.integral μ Y :=
  h_indep.integral_fun_mul_eq_mul_integral hT.aestronglyMeasurable hY.aestronglyMeasurable

end Pythia.Bio.RCT
