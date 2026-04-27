/-
Pythia.AxiomAudit — machine-checked axiom discipline for the
public API surface.

Every headline theorem in the Pythia library should depend only
on the trusted Lean kernel axioms `{propext, Classical.choice,
Quot.sound}`. This file is a per-commit audit trail: if any new
theorem introduces an out-of-band axiom (e.g. an unresolved
`sorryAx`), CI will fail.

Usage:
    lake env lean Pythia/AxiomAudit.lean

This emits `#print axioms` output for each audited theorem. CI grep
asserts that no line names anything outside the trusted triple
`{propext, Classical.choice, Quot.sound}`.

Note on coverage. The library currently declares two separate
`Pythia.ville_supermartingale` symbols — one in
`SubGaussianMG.lean` (finite-horizon supermartingale form, the active
form used by `BettingCS` etc.) and one in `VilleSupermartingale.lean`
(infinite-horizon corollary). Lean refuses to load both modules into
the same environment because the fully-qualified names collide, so
this audit covers the `SubGaussianMG`-rooted form which is the one
actually invoked downstream. The two corollaries
`ville_supermartingale_unit_initial` and `ville_bound_pos` live in
`VilleSupermartingale.lean` and cannot be co-audited from this file
without resolving the name collision upstream — they are NOT covered
here. Recommend renaming the orphan declarations as a follow-up
chore.
-/
import Pythia.SubGaussianMG
import Pythia.VilleSupermartingale
import Pythia.HowardRamdasCS
import Pythia.BettingCS
import Pythia.VectorSharpness
import Pythia.MatchingConstants
import Pythia.Quantization
import Pythia.EquivalenceBreak
import Pythia.Sharpness
import Pythia.BenchDefs
import Pythia.BDG
import Pythia.Bennett
import Pythia.MeasureTheory.ConditionalJensen
import Pythia.InfoTheory.DataProcessing

namespace Pythia.AxiomAudit

open Pythia

/-! ## Ville's inequality — marquee infinite-horizon + finite-horizon -/

#print axioms ville_supermartingale
#print axioms ville_supermartingale_unit_initial
#print axioms ville_bound_pos
#print axioms ville_supermartingale_finite

/-! ## HowardRamdasCS -/

#print axioms hrStoppingRule_admissible

/-! ## BettingCS -/

#print axioms bettingStoppingRule_admissible

/-! ## VectorSharpness -/

#print axioms one_d_marginal_reduction_tight
#print axioms one_d_marginal_sigma_gap_strict
#print axioms gaussian_boundary_density_vector
#print axioms c_vector_sharp_matches_sqrt_two_c_HR
#print axioms gaussian_boundary_density_vector_pos

/-! ## MatchingConstants -/

#print axioms c_vector_sharp
#print axioms c_aCS_sharp
#print axioms c_vector_sharp_pos
#print axioms c_aCS_sharp_pos
#print axioms c_sharp_ranking
#print axioms c_vector_eq_sqrt_two_mul_c_HR

/-! ## BenchDefs (paper-cited sharp constants) -/

#print axioms c_HR_sharp
#print axioms c_betting_sharp

/-! ## EquivalenceBreak -/

#print axioms equivalence_break_at_finite_precision_generic

/-! ## Quantization (slack-rate / transport) -/

#print axioms etaHR_le_slack
#print axioms etaBetting_le_etaHR
#print axioms etaHR_le_etaVector
#print axioms etaVector_eq_sqrt_two_mul_etaHR
#print axioms etaAsymptotic_le_etaHR
#print axioms ranking_four_way
#print axioms etaHR_derivation_from_ville_boundary

/-! ## Sharpness witnesses -/

#print axioms etaHR_sharpness_witness
#print axioms etaBetting_sharpness_witness


/-! ## Burkholder-Davis-Gundy (Aristotle import 2026-04-26, project ff404663) -/

#print axioms bdg_discrete_l2

/-! ## Bennett (Aristotle import 2026-04-26, project 7e11d4c4) -/

#print axioms bennett_iid
#print axioms bennett_mgf_bound

/-! ## Conditional Jensen (Aristotle import 2026-04-26, project 97f3d814) -/

#print axioms ConditionalJensen.condExp_le_condExp_of_convexOn
#print axioms ConditionalJensen.condExp_affine_minorant_le
#print axioms ConditionalJensen.condExp_ge_const

/-! ## Data Processing inequality (Aristotle import 2026-04-26, project 98f89ac0) -/

#print axioms Pythia.InfoTheory.klDiv_bind_le_klDiv
#print axioms Pythia.InfoTheory.klDiv_snd_le
#print axioms Pythia.InfoTheory.klDiv_fst_le
#print axioms Pythia.InfoTheory.klDiv_compProd_right

end Pythia.AxiomAudit
