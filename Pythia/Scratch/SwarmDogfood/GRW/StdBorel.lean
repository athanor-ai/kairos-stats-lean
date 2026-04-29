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

noncomputable instance swarm_stdBorel : @StandardBorelSpace (ℕ → ℝ) Pythia.canonicalMeasurableSpace := by
  exact Pythia.instStandardBorelSpaceNatReal

end Pythia.Scratch.SwarmDogfood.GRW
