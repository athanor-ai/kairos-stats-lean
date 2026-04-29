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

lemma swarm_gaussianWalk_adapted : Adapted Pythia.canonicalFiltration Pythia.gaussianWalk := fun n => by
  rw [gaussianWalk]
  refine Finset.measurable_sum _ (fun i hi => ?_)
  exact measurable_from_canonicalFiltration (Finset.mem_range.mp hi)

end Pythia.Scratch.SwarmDogfood.GRW

#print axioms Pythia.Scratch.SwarmDogfood.GRW.swarm_gaussianWalk_adapted
