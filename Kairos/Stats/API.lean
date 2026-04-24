/-
Kairos.Stats.API — public re-export surface.

Downstream users depending on kairos-stats-lean should `import
Kairos.Stats.API` and pull the headline definitions + theorems without
touching internal modules. This module is semver-stable: names here
will not break within a major version.

A user who does `import Kairos.Stats.API` and `open Kairos.Stats` sees
the full public surface — re-exports here are by transitive import,
so every name introduced in the modules below is in scope without an
explicit `export` list.

## Sections of the public surface

  * **Foundations** — `Basic`, `SubGaussianMG`.
    Foundational types (`BitPrecision`, `Time`, `slack`), the
    `SubGaussianMG` structure with its base martingale property and
    exponential supermartingale, and Ville's inequality for sub-Gaussian
    martingales (`ville_ineq`) plus the underlying non-negative-
    supermartingale form (`ville_supermartingale`).

  * **CS families** — `HowardRamdasCS`, `BettingCS`, `VectorSharpness`.
    The anytime-valid confidence-sequence constructions and their
    admissibility theorems: `hrBoundary` +
    `hrStoppingRule_admissible`, `bettingStoppingRule` +
    `bettingStoppingRule_admissible`, plus the vector-family
    1-d-marginal-reduction theorem
    (`one_d_marginal_reduction_tight`) and Gaussian-boundary-density
    identity.

  * **Sharp constants** — `MatchingConstants`, `BenchDefs`.
    Closed-form matching-lower-bound constants: `c_HR_sharp`,
    `c_betting_sharp`, `c_vector_sharp`, `c_aCS_sharp`, plus ranking
    lemma `c_sharp_ranking` and the identity
    `c_vector_eq_sqrt_two_mul_c_HR`.

  * **Quantization** — `Quantization`. The scalar
    quantization-transport lemma `quantizeReal_error` and per-family
    deployment-slack rates `etaHR`, `etaBetting`, `etaVector`,
    `etaAsymptotic`, plus the four-way ranking
    (`ranking_four_way`) and the HR-rate derivation from the
    Ville boundary.

  * **Equivalence break** — `EquivalenceBreak`. The finite-precision
    equivalence-break theorem
    `equivalence_break_at_finite_precision_generic` showing that
    self-normalized and betting CS produce different stopping
    decisions at finite precision in the generic-shift regime, plus
    the half-line characterization `quantizeReal_ge_iff`.

## Excluded from the public surface (deliberately)

  * `Kairos.Stats.VilleMathlibPR`         — house-style reference draft.
  * `Kairos.Stats.SubGamma`               — has structural sorries; not
                                            yet paper-targeted.
  * `Kairos.Stats.NewTargetsStubs`        — scaffolding.
  * `Kairos.Stats.AristotleT0T1T2Bench`   — scaffolding.

## Resolved name-collision note

`ville_supermartingale` now uniquely refers to the infinite-horizon
non-negative-supermartingale form in
`Kairos.Stats.VilleSupermartingale` (axiom-clean, the marquee theorem).
The finite-horizon form previously named `ville_supermartingale` in
`SubGaussianMG.lean` has been renamed to `ville_supermartingale_finite`
(used internally by `BettingCS`).
-/

-- Foundations
import Kairos.Stats.Basic
import Kairos.Stats.SubGaussianMG
import Kairos.Stats.VilleSupermartingale

-- CS families
import Kairos.Stats.HowardRamdasCS
import Kairos.Stats.BettingCS
import Kairos.Stats.VectorSharpness

-- Sharp constants
import Kairos.Stats.MatchingConstants
import Kairos.Stats.BenchDefs

-- Quantization
import Kairos.Stats.Quantization

-- Equivalence break
import Kairos.Stats.EquivalenceBreak

namespace Kairos.Stats

/-
Re-exports happen automatically via the transitive imports above —
every public declaration in the imported modules is visible to users
who `open Kairos.Stats`. This file's role is to pin the curated set
of modules that constitute the stable API and to document the
sectioning of the public surface.
-/

end Kairos.Stats
