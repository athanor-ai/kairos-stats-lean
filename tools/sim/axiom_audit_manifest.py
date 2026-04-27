"""tools/sim/axiom_audit_manifest.py — expected coverage list for the
axiom audit.

This is the contract: every theorem listed in
:data:`EXPECTED_AUDITED_THEOREMS` must appear (as a substring) in
the output of ``lake env lean Pythia/AxiomAudit.lean``. A drop in
coverage breaks CI. The list is hand-maintained: when a new
theorem is added to ``Pythia/AxiomAudit.lean``, append the
declaration name here in the same PR.

The substring check runs against lake's actual emitted output —
not against the Lean source — so silent regressions where the
source still contains a ``#print axioms`` directive but lake fails
to run it (e.g., import broken, unrelated build error) are caught.

Why a Python module instead of JSON: keeps the contract grep-able,
type-checked, and editable in the same review flow as the rest of
the sim infra. No schema-validation indirection needed.
"""
from __future__ import annotations


# Coverage manifest. Each entry is a Lean declaration name as it
# appears in `Pythia/AxiomAudit.lean`'s `#print axioms <name>`
# directive. Order is informational; the CI check compares as a
# set.
#
# When adding a new audited theorem:
#   1. Add a `#print axioms <decl>` line to Pythia/AxiomAudit.lean
#   2. Add `<decl>` to this set
#   3. Bump the count comment below
#
# Removing entries:
#   ONLY when the theorem itself is removed from the library.
#   Never remove an entry to "fix" a coverage failure — that's
#   the regression we're guarding against.
EXPECTED_AUDITED_THEOREMS: frozenset[str] = frozenset({
    # Ville family (paper §3 anytime-valid)
    "ville_supermartingale",
    "ville_supermartingale_unit_initial",
    "ville_bound_pos",
    "ville_supermartingale_finite",
    # Howard-Ramdas + Betting CS admissibility
    "hrStoppingRule_admissible",
    "bettingStoppingRule_admissible",
    # Vector / matching constants
    "one_d_marginal_reduction_tight",
    "one_d_marginal_sigma_gap_strict",
    "gaussian_boundary_density_vector",
    "c_vector_sharp_matches_sqrt_two_c_HR",
    "gaussian_boundary_density_vector_pos",
    "c_vector_sharp",
    "c_aCS_sharp",
    "c_vector_sharp_pos",
    "c_aCS_sharp_pos",
    "c_sharp_ranking",
    "c_vector_eq_sqrt_two_mul_c_HR",
    "c_HR_sharp",
    "c_betting_sharp",
    # Quantization / equivalence-break
    "equivalence_break_at_finite_precision_generic",
    # Eta hierarchy
    "etaHR_le_slack",
    "etaBetting_le_etaHR",
    "etaHR_le_etaVector",
    "etaVector_eq_sqrt_two_mul_etaHR",
    "etaAsymptotic_le_etaHR",
    "ranking_four_way",
    "etaHR_derivation_from_ville_boundary",
    "etaHR_sharpness_witness",
    "etaBetting_sharpness_witness",
    # Concentration
    "bdg_discrete_l2",
    "bennett_iid",
    "bennett_mgf_bound",
    # Conditional Jensen
    "ConditionalJensen.condExp_le_condExp_of_convexOn",
    "ConditionalJensen.condExp_affine_minorant_le",
    "ConditionalJensen.condExp_ge_const",
    # Information theory / data processing
    "Pythia.InfoTheory.klDiv_bind_le_klDiv",
    "Pythia.InfoTheory.klDiv_snd_le",
    "Pythia.InfoTheory.klDiv_fst_le",
    "Pythia.InfoTheory.klDiv_compProd_right",
    # Stochastic approximation
    "Pythia.StochasticApproximation.robbins_siegmund",
    "Pythia.StochasticApproximation.robbins_monro_ae_tendsto",
    "Pythia.StochasticApproximation.Dvoretzky.dvoretzky_ae",
    "Pythia.StochasticApproximation.Dvoretzky.robbins_siegmund_ae",
    "Pythia.StochasticApproximation.Dvoretzky.robbins_monro_convergence",
    "Pythia.StochasticApproximation.Dvoretzky.sgd_convergence",
    # Time series
    "Pythia.TimeSeries.NeweyWest.hac_consistent",
    # Control
    "Pythia.Control.LyapunovODE.V_pos_lower_bound_annulus",
    # Risk / coherent measures
    "Pythia.Risk.CoherentMeasures.adeh_attained",
    "Pythia.Risk.CoherentMeasures.adehSet_nonempty",
    "Pythia.Risk.CoherentMeasures.adeh_representation",
    "Pythia.Risk.CoherentMeasures.isCoherent_sup_expect",
})
# Count at 2026-04-27: 51 audited theorems.
# Bump this comment when EXPECTED_AUDITED_THEOREMS grows.

__all__ = ["EXPECTED_AUDITED_THEOREMS"]
