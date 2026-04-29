import import Mathlib
import import Pythia.Basic
import import Pythia.GaussianSmallBall
import import Pythia.SubGaussianMG
import import Pythia.VectorSharpness
import import Pythia.Frontier.GaussianRandomWalk

open MeasureTheory
open ProbabilityTheory
open Pythia

namespace Pythia.Scratch.SwarmDogfood.GRW

lemma swarm_gaussianWalk_integrable (σ : ℝ) : ∀ t, MeasureTheory.Integrable (Pythia.gaussianWalk t) (Pythia.gaussianProductMeasure σ) := by
  intro t
  induction t with
  | zero =>
    simp [Pythia.gaussianWalk]
    exact MeasureTheory.integrable_zero _ _ _
  | succ t ih =>
    simp [Pythia.gaussianWalk]
    apply MeasureTheory.Integrable.add
    · exact ih
    · apply Pythia.integrable_gaussianIncrement
      simp [Pythia.gaussianProductMeasure]

end Pythia.Scratch.SwarmDogfood.GRW

#print axioms Pythia.Scratch.SwarmDogfood.GRW.swarm_gaussianWalk_integrable
