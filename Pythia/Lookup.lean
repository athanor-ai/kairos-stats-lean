/-
Pythia.Lookup — strategy-layer API for the kairos.prove router.

## Contract

The kairos cross-vertical MCP router (ATH-894) calls into Pythia for
the strategy layer of `kairos.prove(target, property)`. The router
parses the customer-facing goal description, derives a goal-class
key, and queries `Pythia.Lookup.query goalClass` to obtain ranked
candidate theorems with their obligations + applicable hypotheses.

The router then either:
  • applies the top candidate template directly (deterministic path),
  • or fires `pythia!` (hammer ladder: Z3 / CVC5 / Vampire / E +
    LLM-defense layers) and uses the lookup result as the closure
    target,
  • or returns the structured obligations as a `decompose` hint
    when neither closes.

This module is the structured-JSON contract platform's router wires
against. It is intentionally pure data + a single query function;
no tactics, no proof obligations, sorry-free.

## Goal-class taxonomy

Goal classes are dot-separated strings:

  `<domain>.<subdomain>.<flavor>`

Examples:
  • `anytime_valid.cs.howard_ramdas`
  • `anytime_valid.cs.betting`
  • `concentration.bernstein.iid`
  • `actuarial.tail.pareto`
  • `actuarial.mean.weibull`
  • `hardware.refinement.transitive`
  • `hardware.acl2_certificate.compose`
  • `info_theory.divergence.bretagnolle_huber`
  • `info_theory.dpi.kl`
  • `neuroscience.cable_equation.steady_state`
  • `stochastic_approx.robbins_monro.convergence`

The query function does prefix matching, so a router asking for
`anytime_valid.cs` returns every CS-family entry. This is intentional
— the router can refine by parsing the customer's description more
or less aggressively without changing the lookup contract.

## Confidence score

Each entry carries a confidence score in `[0.0, 1.0]`:

  • 1.0  — sorry-free mainline theorem, fully closed proof.
  • 0.7  — sorry-free with mild scaffolding (helper sorries closed).
  • 0.4  — Frontier/scaffold, depends on open sub-goals.
  • 0.0  — not exposed.

We only register entries with confidence ≥ 0.7 here. Frontier
sorries stay in the Frontier umbrella and do NOT pollute the
strategy layer.

## Sorry status

This file declares no theorems. It only references theorem names.
Sorry-free trivially.
-/
import Lean

namespace Pythia.Lookup

/-- A lookup entry: goal-class identifier + Lean-name of the registered
theorem + structured metadata for the router.

The `applicableHypotheses` list is human-readable (consumed by the LLM
side of the router for goal-matching). The `obligationsList` is
machine-readable (consumed by the router as the proof-obligation
graph when decomposing a hard target).
-/
structure TheoremEntry where
  /-- Dot-separated goal-class key, e.g. `"anytime_valid.cs.betting"`. -/
  goalClass : String
  /-- Lean theorem name as a string, e.g. `"Pythia.bettingStoppingRule_admissible"`. -/
  theoremName : String
  /-- One of: `"actuarial"`, `"numerical"`, `"bio"`, `"bayes"`, `"control"`,
  `"stats"`, `"hardware"`, `"info_theory"`, `"neuroscience"`,
  `"stochastic_approx"`, `"asymptotics"`, `"queueing"`, `"risk"`,
  `"time_series"`, `"hypothesis_testing"`, `"language_semantics"`,
  `"networking"`, `"chemistry"`. -/
  domain : String
  /-- Human/LLM-facing description of when this template applies. -/
  applicableHypotheses : List String
  /-- Machine-readable obligation list (sub-goals the customer must
  discharge for the template to close). -/
  obligationsList : List String
  /-- Source Lean module for traceability. -/
  sourceModule : String
  /-- Baseline confidence in `[0.0, 1.0]`. We register ≥ 0.7 only. -/
  confidence : Float
  deriving Inhabited, Repr

/-- The canonical Pythia v1 strategy registry. Curated coverage across
the verticals named in ATH-894 (hardware / Lean / bio / Cedar /
actuarial / clinical / neuroscience).

Adding entries: lemma must be sorry-free on mainline AND its name
must round-trip through `lake env lean` against the import. The
CI-side check (`tools/lookup_validate.py`, planned) walks this list
and confirms every `theoremName` resolves in the elaborated
environment, gating drift the same way `check-stale-imports.sh`
gates Frontier import drift.
-/
def registry : List TheoremEntry := [
  -- Anytime-valid CS family ----------------------------------------
  { goalClass := "anytime_valid.cs.howard_ramdas"
    theoremName := "Pythia.hrStoppingRule_admissible"
    domain := "stats"
    applicableHypotheses := [
      "running mean of a [0,1]-valued process",
      "no a-priori variance bound required",
      "want anytime-valid 1-sided CS at level α"
    ]
    obligationsList := [
      "process bounded in [0,1]",
      "filtration adapted",
      "α ∈ (0,1)"
    ]
    sourceModule := "Pythia.HowardRamdasCS"
    confidence := 1.0 },
  { goalClass := "anytime_valid.cs.betting"
    theoremName := "Pythia.bettingStoppingRule_admissible"
    domain := "stats"
    applicableHypotheses := [
      "want a tighter CS than Howard-Ramdas for sub-Gaussian processes",
      "willing to compute betting strategy online"
    ]
    obligationsList := [
      "sub-Gaussian process with known proxy",
      "betting strategy non-anticipating",
      "α ∈ (0,1)"
    ]
    sourceModule := "Pythia.BettingCS"
    confidence := 1.0 },
  -- Ville-family closers -------------------------------------------
  { goalClass := "anytime_valid.ville.supermartingale_infinite"
    theoremName := "Pythia.ville_supermartingale_infinite"
    domain := "stats"
    applicableHypotheses := [
      "non-negative supermartingale on a probability space",
      "infinite-horizon"
    ]
    obligationsList := [
      "process is a supermartingale",
      "process is non-negative",
      "f 0 has finite expectation"
    ]
    sourceModule := "Pythia.BettingCS"
    confidence := 1.0 },
  { goalClass := "anytime_valid.ville.supermartingale_unit_initial"
    theoremName := "Pythia.ville_supermartingale_unit_initial"
    domain := "stats"
    applicableHypotheses := [
      "non-negative supermartingale with f 0 = 1 a.s.",
      "infinite-horizon"
    ]
    obligationsList := [
      "process is a supermartingale",
      "process is non-negative",
      "f 0 = 1 almost everywhere"
    ]
    sourceModule := "Pythia.VilleSupermartingale"
    confidence := 1.0 },
  { goalClass := "anytime_valid.ville.subgaussian"
    theoremName := "Pythia.ville_ineq"
    domain := "stats"
    applicableHypotheses := [
      "sub-Gaussian martingale",
      "want classical Ville-style boundary crossing bound"
    ]
    obligationsList := [
      "martingale is sub-Gaussian with proxy σ²",
      "boundary > 0"
    ]
    sourceModule := "Pythia.SubGaussianMG"
    confidence := 1.0 },
  -- Actuarial: Pareto ---------------------------------------------
  { goalClass := "actuarial.tail.pareto"
    theoremName := "Pythia.Actuarial.Pareto.tail"
    domain := "actuarial"
    applicableHypotheses := [
      "loss is Pareto-distributed with scale x_m and shape α",
      "want P(X > t) for t > x_m"
    ]
    obligationsList := [
      "x_m > 0",
      "α > 0",
      "t ≥ x_m"
    ]
    sourceModule := "Pythia.Actuarial.Pareto"
    confidence := 1.0 },
  { goalClass := "actuarial.mean.pareto"
    theoremName := "Pythia.Actuarial.Pareto.mean"
    domain := "actuarial"
    applicableHypotheses := [
      "loss is Pareto-distributed with scale x_m and shape α > 1",
      "want E[X]"
    ]
    obligationsList := [
      "x_m > 0",
      "α > 0",
      "α > 1 (mean exists)"
    ]
    sourceModule := "Pythia.Actuarial.Pareto"
    confidence := 1.0 },
  -- Actuarial: Weibull --------------------------------------------
  { goalClass := "actuarial.mean.weibull"
    theoremName := "Pythia.Actuarial.Weibull.mean"
    domain := "actuarial"
    applicableHypotheses := [
      "loss is Weibull with scale λ and shape k",
      "want E[X] in closed form via Γ"
    ]
    obligationsList := [
      "λ > 0",
      "k > 0"
    ]
    sourceModule := "Pythia.Actuarial.Weibull"
    confidence := 1.0 },
  -- Actuarial: LogNormal ------------------------------------------
  { goalClass := "actuarial.tail.lognormal_chebyshev"
    theoremName := "Pythia.Actuarial.LogNormal.tail_chebyshev"
    domain := "actuarial"
    applicableHypotheses := [
      "loss is log-normal with parameters μ, σ",
      "want a Chebyshev tail bound (any t > 0)"
    ]
    obligationsList := [
      "t > 0"
    ]
    sourceModule := "Pythia.Actuarial.LogNormal"
    confidence := 1.0 },
  -- Hardware: refinement composition ------------------------------
  { goalClass := "hardware.refinement.transitive"
    theoremName := "Pythia.Hardware.refines_trans"
    domain := "hardware"
    applicableHypotheses := [
      "two refinement claims A ⊑ B and B ⊑ C",
      "want A ⊑ C from composition"
    ]
    obligationsList := [
      "A refines B (per-input architectural-state equality)",
      "B refines C (per-input architectural-state equality)"
    ]
    sourceModule := "Pythia.Hardware.RefinementComposition"
    confidence := 1.0 },
  { goalClass := "hardware.refinement.three_way"
    theoremName := "Pythia.Hardware.three_way_refinement"
    domain := "hardware"
    applicableHypotheses := [
      "three CPU implementations SI, PIPE, OOO",
      "have SI ⊑ PIPE and PIPE ⊑ OOO certificates",
      "want SI ⊑ OOO via composition"
    ]
    obligationsList := [
      "SI ⊑ PIPE (e.g. EBMC k-induction certificate)",
      "PIPE ⊑ OOO (e.g. ACL2 FM9801-style refinement)"
    ]
    sourceModule := "Pythia.Hardware.RefinementComposition"
    confidence := 1.0 },
  { goalClass := "hardware.acl2_certificate.compose"
    theoremName := "Pythia.Hardware.composeWitnessed"
    domain := "hardware"
    applicableHypotheses := [
      "two WitnessedRefinement certificates from heterogeneous engines",
      "want a single composed certificate covering A ⊑ C"
    ]
    obligationsList := [
      "WitnessedRefinement A B (any engine)",
      "WitnessedRefinement B C (any engine)"
    ]
    sourceModule := "Pythia.Hardware.ACL2Bridge"
    confidence := 1.0 },
  { goalClass := "hardware.invariant.rob_commit"
    theoremName := "Pythia.Hardware.rob_commit_consistency"
    domain := "hardware"
    applicableHypotheses := [
      "OoO CPU with reorder buffer commits",
      "want SI/OOO GPR-state agreement on every committed entry"
    ]
    obligationsList := [
      "ALU agreement on every commit",
      "SI matches commit on every entry"
    ]
    sourceModule := "Pythia.Hardware.InvariantObligation"
    confidence := 1.0 },
  -- Information theory --------------------------------------------
  { goalClass := "info_theory.divergence.bretagnolle_huber_binary"
    theoremName := "Pythia.InfoTheory.bretagnolle_huber_binary"
    domain := "info_theory"
    applicableHypotheses := [
      "two probability measures on a binary outcome",
      "want a TV bound from KL via Bretagnolle-Huber"
    ]
    obligationsList := [
      "both measures probability",
      "binary outcome space"
    ]
    sourceModule := "Pythia.InfoTheory.BretagnolleHuberBinary"
    confidence := 1.0 },
  -- Stochastic approximation --------------------------------------
  { goalClass := "stochastic_approx.robbins_monro.condexp_lyapunov"
    theoremName := "Pythia.StochasticApproximation.condExp_lyapunov_bound"
    domain := "stochastic_approx"
    applicableHypotheses := [
      "Robbins-Monro iterate with bounded noise",
      "want conditional-expectation bound on the Lyapunov potential"
    ]
    obligationsList := [
      "step size > 0",
      "noise is martingale-difference",
      "Lyapunov potential well-defined"
    ]
    sourceModule := "Pythia.StochasticApproximation.RobbinsMonro"
    confidence := 1.0 },
  -- Risk ----------------------------------------------------------
  { goalClass := "risk.coherent.zero"
    theoremName := "Pythia.Risk.CoherentMeasures.coherent_zero"
    domain := "risk"
    applicableHypotheses := [
      "ρ is a coherent risk measure",
      "want ρ(0) = 0 (zero loss = zero risk)"
    ]
    obligationsList := [
      "ρ satisfies coherent-risk axioms"
    ]
    sourceModule := "Pythia.Risk.CoherentMeasures"
    confidence := 1.0 },
  -- Queueing ------------------------------------------------------
  { goalClass := "queueing.erlang_b.unnorm_pos"
    theoremName := "ErlangB.unnormProb_pos"
    domain := "queueing"
    applicableHypotheses := [
      "M/M/c/c with offered load ρ > 0",
      "want strict positivity of unnormalized blocking-state probability"
    ]
    obligationsList := [
      "ρ > 0",
      "k ≥ 0"
    ]
    sourceModule := "Pythia.Queueing.ErlangB"
    confidence := 1.0 },
  { goalClass := "queueing.littles_law"
    theoremName := "littles_law"
    domain := "queueing"
    applicableHypotheses := [
      "stationary queueing system",
      "want L = λW relating average queue length, arrival rate, mean wait"
    ]
    obligationsList := [
      "system stationary",
      "arrival rate finite"
    ]
    sourceModule := "Pythia.Queueing.LittlesLaw"
    confidence := 1.0 },
  -- Control -------------------------------------------------------
  { goalClass := "control.lyapunov.v_antitone"
    theoremName := "Pythia.Control.LyapunovDiscrete.V_antitone_along_orbit"
    domain := "control"
    applicableHypotheses := [
      "discrete-time orbit under f",
      "Lyapunov function V with ΔV ≤ 0",
      "want V monotone-decreasing along the orbit"
    ]
    obligationsList := [
      "V satisfies the Lyapunov decrease condition",
      "orbit stays in V's domain"
    ]
    sourceModule := "Pythia.Control.LyapunovDiscrete"
    confidence := 1.0 },
  -- Bio (ATH-897) -------------------------------------------------
  { goalClass := "bio.kinetics.michaelis_menten_saturation"
    theoremName := "Pythia.Bio.michaelis_menten_saturation"
    domain := "bio"
    applicableHypotheses := [
      "enzyme-substrate kinetics with Vmax, Km, [S]",
      "want saturation behavior of reaction velocity"
    ]
    obligationsList := [
      "Vmax > 0", "Km > 0", "[S] ≥ 0"
    ]
    sourceModule := "Pythia.Bio.MichaelisMentenSaturation"
    confidence := 1.0 },
  { goalClass := "bio.population.hardy_weinberg"
    theoremName := "Pythia.Bio.Population.hardy_weinberg_conservation"
    domain := "bio"
    applicableHypotheses := [
      "diallelic locus with allele frequencies p, q",
      "want generation-to-generation conservation under HW assumptions"
    ]
    obligationsList := [
      "p + q = 1"
    ]
    sourceModule := "Pythia.Bio.Population"
    confidence := 1.0 },
  { goalClass := "bio.population.lotka_volterra_equilibrium"
    theoremName := "Pythia.Bio.Population.lotka_volterra_equilibrium_x_pos"
    domain := "bio"
    applicableHypotheses := [
      "predator-prey Lotka-Volterra system",
      "want strict positivity of the non-trivial equilibrium prey count"
    ]
    obligationsList := [
      "all rate parameters strictly positive"
    ]
    sourceModule := "Pythia.Bio.Population"
    confidence := 1.0 },
  { goalClass := "bio.crn.mass_action_existence"
    theoremName := "Pythia.Bio.MassAction.massAction_existence"
    domain := "bio"
    applicableHypotheses := [
      "chemical reaction network with mass-action kinetics",
      "want existence of a unique solution to the CRN ODE system"
    ]
    obligationsList := [
      "rate constants finite",
      "initial condition nonneg"
    ]
    sourceModule := "Pythia.Bio.MassAction"
    confidence := 1.0 },
  { goalClass := "bio.crn.mass_action_nonnegativity"
    theoremName := "Pythia.Bio.MassAction.massAction_nonnegativity"
    domain := "bio"
    applicableHypotheses := [
      "CRN with mass-action kinetics + nonneg initial condition",
      "want trajectory stays in the nonneg orthant"
    ]
    obligationsList := [
      "rate constants nonneg",
      "x(0) ≥ 0 componentwise"
    ]
    sourceModule := "Pythia.Bio.MassAction"
    confidence := 1.0 },
  { goalClass := "bio.phylogenetics.jukes_cantor_pi_sum"
    theoremName := "Pythia.Bio.Phylogenetics.JukesCantor_pi_sum"
    domain := "bio"
    applicableHypotheses := [
      "Jukes-Cantor 4-state DNA substitution model",
      "want stationary distribution sums to 1"
    ]
    obligationsList := []
    sourceModule := "Pythia.Bio.Phylogenetics"
    confidence := 1.0 },
  -- Chemistry (ATH-897) -------------------------------------------
  { goalClass := "chemistry.kinetics.arrhenius_positivity"
    theoremName := "Pythia.Chemistry.arrhenius_pos"
    domain := "chemistry"
    applicableHypotheses := [
      "Arrhenius rate k = A exp(-Ea / (R T))",
      "want strict positivity of k"
    ]
    obligationsList := [
      "pre-exponential A > 0",
      "T > 0", "R > 0"
    ]
    sourceModule := "Pythia.Chemistry.Arrhenius"
    confidence := 1.0 },
  { goalClass := "chemistry.spectroscopy.beer_lambert_monotone"
    theoremName := "Pythia.Chemistry.beerLambert_monotone_in_concentration"
    domain := "chemistry"
    applicableHypotheses := [
      "Beer-Lambert absorbance A = ε ℓ c",
      "want absorbance monotone-increasing in concentration"
    ]
    obligationsList := [
      "molar absorptivity ε ≥ 0",
      "path-length ℓ ≥ 0",
      "concentration nonneg"
    ]
    sourceModule := "Pythia.Chemistry.BeerLambert"
    confidence := 1.0 },
  { goalClass := "chemistry.acid_base.henderson_hasselbalch_monotone"
    theoremName := "Pythia.Chemistry.hh_monotone_in_ratio"
    domain := "chemistry"
    applicableHypotheses := [
      "Henderson-Hasselbalch pH = pKa + log10([A-]/[HA])",
      "want pH monotone-increasing in conjugate-base / acid ratio"
    ]
    obligationsList := [
      "ratio strictly positive"
    ]
    sourceModule := "Pythia.Chemistry.HendersonHasselbalch"
    confidence := 1.0 },
  { goalClass := "chemistry.stoichiometry.mass_action_conservation"
    theoremName := "Pythia.Chemistry.mass_action_conservation_pair"
    domain := "chemistry"
    applicableHypotheses := [
      "single-step reaction A → B with extent ξ",
      "want pairwise mole-balance conservation"
    ]
    obligationsList := []
    sourceModule := "Pythia.Chemistry.MassActionConservation"
    confidence := 1.0 },
  -- Neuroscience (ATH-897) ----------------------------------------
  { goalClass := "neuroscience.cable_equation.steady_state_at_zero"
    theoremName := "Pythia.Neuroscience.cableSteadyState_at_zero"
    domain := "neuroscience"
    applicableHypotheses := [
      "passive cylindrical dendrite cable equation",
      "want V(0) = V0 boundary value"
    ]
    obligationsList := []
    sourceModule := "Pythia.Neuroscience.CableEquation"
    confidence := 1.0 },
  { goalClass := "neuroscience.cable_equation.monotone_decreasing"
    theoremName := "Pythia.Neuroscience.cableSteadyState_monotone_decreasing"
    domain := "neuroscience"
    applicableHypotheses := [
      "passive cable equation steady state V(x) = V0 exp(-x/λ)",
      "want V monotone-decreasing in x for V0 ≥ 0, λ > 0"
    ]
    obligationsList := [
      "V0 ≥ 0", "λ > 0"
    ]
    sourceModule := "Pythia.Neuroscience.CableEquation"
    confidence := 1.0 },
  { goalClass := "neuroscience.nernst.equilibrium_zero"
    theoremName := "Pythia.Neuroscience.nernstPotential_zero_at_equilibrium"
    domain := "neuroscience"
    applicableHypotheses := [
      "Nernst potential E = (RT/zF) ln([X]_out/[X]_in)",
      "want E = 0 when [X]_out = [X]_in"
    ]
    obligationsList := [
      "concentrations strictly positive and equal"
    ]
    sourceModule := "Pythia.Neuroscience.NernstPotential"
    confidence := 1.0 },
  { goalClass := "neuroscience.lif.firing_rate_refractory"
    theoremName := "Pythia.Neuroscience.firing_rate_bounded_by_refractory"
    domain := "neuroscience"
    applicableHypotheses := [
      "leaky integrate-and-fire neuron with refractory period τ_ref",
      "want firing rate ≤ 1/τ_ref"
    ]
    obligationsList := [
      "τ_ref > 0"
    ]
    sourceModule := "Pythia.Neuroscience.LIF"
    confidence := 1.0 },
  { goalClass := "neuroscience.hh_gate.steady_state_in_unit_interval"
    theoremName := "Pythia.Neuroscience.hhGateSteadyState_le_one"
    domain := "neuroscience"
    applicableHypotheses := [
      "Hodgkin-Huxley gating variable steady-state x_∞(V) = α / (α+β)",
      "want x_∞ ≤ 1"
    ]
    obligationsList := [
      "α ≥ 0", "β ≥ 0", "α + β > 0"
    ]
    sourceModule := "Pythia.Neuroscience.HHGate"
    confidence := 1.0 },
  { goalClass := "neuroscience.shannon_hartley.capacity_monotone"
    theoremName := "Pythia.Neuroscience.shannonHartleyCapacity_monotone_in_snr"
    domain := "neuroscience"
    applicableHypotheses := [
      "Shannon-Hartley capacity C = B log2(1 + S/N)",
      "want C monotone-increasing in SNR"
    ]
    obligationsList := [
      "bandwidth B > 0",
      "SNR > 0"
    ]
    sourceModule := "Pythia.Neuroscience.ShannonHartley"
    confidence := 1.0 },
  -- Networking (ATH-898) ------------------------------------------
  { goalClass := "networking.congestion_control.reno_cwnd_floor"
    theoremName := "CC.Reno.cwnd_floor_cwnd_ge_MSS"
    domain := "networking"
    applicableHypotheses := [
      "Reno congestion-control state machine",
      "want cwnd never drops below MSS (floor invariant)"
    ]
    obligationsList := [
      "initial cwnd ≥ MSS",
      "transitions are Reno-spec compliant"
    ]
    sourceModule := "Pythia.Networking.CC.Reno"
    confidence := 1.0 },
  { goalClass := "networking.congestion_control.cubic_cwnd_floor"
    theoremName := "CC.Cubic.cwnd_floor_cwnd_ge_MSS"
    domain := "networking"
    applicableHypotheses := [
      "CUBIC congestion-control state machine",
      "want cwnd never drops below MSS (floor invariant)"
    ]
    obligationsList := [
      "initial cwnd ≥ MSS",
      "transitions are CUBIC-spec compliant"
    ]
    sourceModule := "Pythia.Networking.CC.Cubic"
    confidence := 1.0 },
  -- Language semantics — Cedar (ATH-898) --------------------------
  { goalClass := "language_semantics.cedar.vars_of_type_sound"
    theoremName := "Pythia.LanguageSemantics.Cedar.varsOfType_sound"
    domain := "language_semantics"
    applicableHypotheses := [
      "Cedar policy expression typing context Γ",
      "want generated variable list is sound w.r.t. typing"
    ]
    obligationsList := [
      "Γ well-formed",
      "type τ inhabited at depth n"
    ]
    sourceModule := "Pythia.LanguageSemantics.Cedar.Soundness"
    confidence := 1.0 },
  { goalClass := "language_semantics.cedar.vars_of_type_complete"
    theoremName := "Pythia.LanguageSemantics.Cedar.varsOfType_complete"
    domain := "language_semantics"
    applicableHypotheses := [
      "Cedar policy expression typing context Γ",
      "want every variable of given type is generated (completeness)"
    ]
    obligationsList := [
      "Γ well-formed",
      "type τ inhabited at depth n"
    ]
    sourceModule := "Pythia.LanguageSemantics.Cedar.Coverage"
    confidence := 1.0 },
  -- Clinical trials (ATH-895) -------------------------------------
  { goalClass := "clinical_trials.multi_arm.bonferroni_union_bound"
    theoremName := "Pythia.ClinicalTrials.bonferroni_union_bound_real"
    domain := "clinical_trials"
    applicableHypotheses := [
      "K-arm clinical trial with per-arm non-coverage events",
      "each arm has μ.real-measure of non-coverage ≤ α/K",
      "want family-wise non-coverage ≤ α (joint anytime-valid CS)"
    ]
    obligationsList := [
      "K ≥ 1",
      "per-arm non-coverage measure ≤ α/K (Bonferroni split)",
      "underlying measure is finite"
    ]
    sourceModule := "Pythia.ClinicalTrials.MultiArmCS"
    confidence := 1.0 },
  { goalClass := "clinical_trials.multi_arm.bonferroni_union_bound_packaged"
    theoremName := "Pythia.ClinicalTrials.bonferroni_union_bound_packaged"
    domain := "clinical_trials"
    applicableHypotheses := [
      "MultiArmCS K α structure",
      "per-arm bound expressed via M.perArmLevel"
    ]
    obligationsList := [
      "MultiArmCS structure constructed (α ∈ (0,1), K ≥ 1)",
      "per-arm bounds at M.perArmLevel"
    ]
    sourceModule := "Pythia.ClinicalTrials.MultiArmCS"
    confidence := 1.0 },
  -- Numerical: ODE existence (PicardLindelof, graduated from Frontier) -
  { goalClass := "numerical.ode.picard_lindelof_global"
    theoremName := "Pythia.Numerical.PicardLindelof.picard_lindelof_global"
    domain := "numerical"
    applicableHypotheses := [
      "f : ℝ → ℝ → ℝ globally K-Lipschitz in y",
      "f continuous in t for each fixed y",
      "want global existence + uniqueness on all of ℝ"
    ]
    obligationsList := [
      "LipschitzWith K (fun y => f t y) for all t",
      "Continuous (fun t => f t y) for all y"
    ]
    sourceModule := "Pythia.Numerical.PicardLindelof"
    confidence := 1.0 },
  { goalClass := "numerical.ode.picard_lindelof_continuous_dependence"
    theoremName := "Pythia.Numerical.PicardLindelof.picard_lindelof_continuous_dependence"
    domain := "numerical"
    applicableHypotheses := [
      "two ODE solutions y, z to the same f with initial values y₀, z₀",
      "want exponential divergence bound via Gronwall"
    ]
    obligationsList := [
      "LipschitzWith K (fun y => f t y) for all t",
      "T ≥ 0"
    ]
    sourceModule := "Pythia.Numerical.PicardLindelof"
    confidence := 1.0 },
  -- Concentration: Cantelli one-sided Chebyshev ---------------------
  { goalClass := "concentration.cantelli"
    theoremName := "Pythia.Concentration.Cantelli.cantelli_real"
    domain := "stats"
    applicableHypotheses := [
      "one-sided tail bound for a random variable with finite mean and variance",
      "want P(X - μ ≥ t) ≤ σ²/(σ² + t²)"
    ]
    obligationsList := [
      "Integrable X μ",
      "Integrable (X ^ 2) μ",
      "t > 0"
    ]
    sourceModule := "Pythia.Concentration.Cantelli"
    confidence := 1.0 },
  -- Asymptotics: Slutsky's theorem ----------------------------------
  { goalClass := "asymptotics.slutsky.addition"
    theoremName := "Pythia.Asymptotics.Slutsky.slutsky_addition"
    domain := "asymptotics"
    applicableHypotheses := [
      "Xₙ converges in distribution to X",
      "Yₙ converges in probability to a constant c",
      "want Xₙ + Yₙ converges in distribution to X + c"
    ]
    obligationsList := [
      "TendstoInDistribution Xₙ X",
      "TendstoInMeasure Yₙ (const c)"
    ]
    sourceModule := "Pythia.Asymptotics.Slutsky"
    confidence := 1.0 },
  { goalClass := "asymptotics.slutsky.multiplication"
    theoremName := "Pythia.Asymptotics.Slutsky.slutsky_multiplication"
    domain := "asymptotics"
    applicableHypotheses := [
      "Xₙ converges in distribution to X",
      "Yₙ converges in probability to a constant c",
      "want Xₙ · Yₙ converges in distribution to c · X"
    ]
    obligationsList := [
      "TendstoInDistribution Xₙ X",
      "TendstoInMeasure Yₙ (const c)"
    ]
    sourceModule := "Pythia.Asymptotics.Slutsky"
    confidence := 1.0 },
  -- Asymptotics: scalar delta method --------------------------------
  { goalClass := "asymptotics.delta_method.scalar"
    theoremName := "Pythia.Asymptotics.DeltaMethodScalar.delta_method_scalar"
    domain := "asymptotics"
    applicableHypotheses := [
      "√n(X̄ₙ - θ) → N(0, σ²) in distribution",
      "g differentiable at θ with g'(θ) ≠ 0",
      "want √n(g(X̄ₙ) - g(θ)) → N(0, (g'θ)²σ²)"
    ]
    obligationsList := [
      "HasDerivAt g (g'θ) θ",
      "CLT-type convergence for X̄ₙ"
    ]
    sourceModule := "Pythia.Asymptotics.DeltaMethodScalar"
    confidence := 1.0 },
  -- SPRT: group-sequential type-I error -----------------------------
  { goalClass := "sprt.gsprt.type_i"
    theoremName := "Pythia.SPRT.GSPRT.gsprt_type_I"
    domain := "hypothesis_testing"
    applicableHypotheses := [
      "group-sequential test with K looks",
      "per-look type-I error bound via Bonferroni",
      "want overall type-I error ≤ α"
    ]
    obligationsList := [
      "per-look α/K spending",
      "K ≥ 1"
    ]
    sourceModule := "Pythia.SPRT.GSPRT"
    confidence := 1.0 },
  -- Clinical trials: Pocock alpha-spending boundary -----------------
  { goalClass := "clinical_trials.pocock.boundary_alpha"
    theoremName := "Pythia.ClinicalTrials.Pocock.boundary_alpha"
    domain := "stats"
    applicableHypotheses := [
      "Pocock equal-alpha-spending boundary with K looks",
      "want overall type-I error ≤ α"
    ]
    obligationsList := [
      "per-look α/K spending",
      "K ≥ 1"
    ]
    sourceModule := "Pythia.ClinicalTrials.Pocock"
    confidence := 1.0 },
  -- Clinical trials: stratified anytime-valid CS --------------------
  { goalClass := "clinical_trials.stratified.admissible"
    theoremName := "Pythia.ClinicalTrials.Stratified.stratified_admissible"
    domain := "stats"
    applicableHypotheses := [
      "S strata each with per-stratum coverage error ≤ α/S",
      "want joint coverage error ≤ α via Bonferroni"
    ]
    obligationsList := [
      "per-stratum measure bound ≤ α/S",
      "S ≥ 1"
    ]
    sourceModule := "Pythia.ClinicalTrials.Stratified"
    confidence := 1.0 }
  -- TODO (when headline theorems land):
  --   • time_series.newey_west.consistency (NeweyWest headline)
  --   • nki.kernels.* (Dafny-side, qa lane — registry stub when
  --     Dafny→Lean cert path lands)
]

/-- Prefix-match query. Returns every entry whose `goalClass` starts
with `goalPrefix`. Used by the router as the strategy lookup. -/
def query (goalPrefix : String) : List TheoremEntry :=
  registry.filter (fun e => goalPrefix.isPrefixOf e.goalClass)

/-- Domain-restricted query: only entries in the given `domain`. -/
def queryDomain (domain : String) : List TheoremEntry :=
  registry.filter (fun e => e.domain == domain)

/-- Combined query: prefix-match within a specific domain. -/
def queryDomainPrefix (domain goalPrefix : String) : List TheoremEntry :=
  registry.filter (fun e => e.domain == domain ∧ goalPrefix.isPrefixOf e.goalClass)

/-- Module-keyed query: every entry whose `sourceModule` matches.
Used by `kairos.spec(target.lean)` — customer passes a `.lean` file,
the router extracts the module path, this returns the registered
theorems backed by that module. Complementary to `query` (which is
goal-class-keyed for `kairos.prove`). -/
def queryModule (sourceModule : String) : List TheoremEntry :=
  registry.filter (fun e => e.sourceModule == sourceModule)

/-- Number of registered strategy entries (sanity check / smoke test). -/
def registrySize : Nat := registry.length

/-! ### Introspection commands -/

/-- `#pythia_lookup p` — list every registered entry whose `goalClass`
starts with `p`. -/
elab "#pythia_lookup" pre:str : command => do
  let p := pre.getString
  let results := query p
  if results.isEmpty then
    Lean.logInfo m!"no Pythia.Lookup entries with prefix {repr p}"
  else
    let lines := results.map (fun e =>
      s!"  • {e.goalClass} → {e.theoremName} (domain={e.domain}, conf={e.confidence})")
    Lean.logInfo m!"Pythia.Lookup matches for prefix {repr p}:\n{String.intercalate "\n" lines}"

/-- `#pythia_lookup_size` — print the number of registered entries. -/
elab "#pythia_lookup_size" : command => do
  Lean.logInfo m!"Pythia.Lookup registry size: {registrySize}"

/-- Minimal JSON-string escape: `\\` and `"`. Registry entries are
curated; unicode + control-char escaping isn't needed for v1. -/
private def jsonEscape (s : String) : String :=
  s.replace "\\" "\\\\" |>.replace "\"" "\\\""

private def jsonStringList (xs : List String) : String :=
  let parts := xs.map (fun x => "\"" ++ jsonEscape x ++ "\"")
  "[" ++ String.intercalate ", " parts ++ "]"

private def entryToJson (e : TheoremEntry) : String :=
  let fields := [
    "\"goalClass\": \"" ++ jsonEscape e.goalClass ++ "\"",
    "\"theoremName\": \"" ++ jsonEscape e.theoremName ++ "\"",
    "\"domain\": \"" ++ jsonEscape e.domain ++ "\"",
    "\"applicableHypotheses\": " ++ jsonStringList e.applicableHypotheses,
    "\"obligationsList\": " ++ jsonStringList e.obligationsList,
    "\"sourceModule\": \"" ++ jsonEscape e.sourceModule ++ "\"",
    "\"confidence\": " ++ toString e.confidence
  ]
  "  {" ++ String.intercalate ", " fields ++ "}"

/-- `#pythia_registry_json` — emit the entire registry as a single JSON
array. The MCP router shells out to this once at startup, caches the
parsed result in-process, and queries locally per request — eliminating
per-query shell-outs and the hygienic-binder panic in
`#pythia_validate`. Output is delimited so the router can extract by
splitting on the marker lines.

Named `_registry_json` rather than `_lookup_json` to avoid the
`#pythia_lookup STR` syntax-prefix collision. -/
elab "#pythia_registry_json" : command => do
  let body := String.intercalate ",\n" (registry.map entryToJson)
  Lean.logInfo s!"<<<PYTHIA_LOOKUP_JSON_BEGIN>>>\n[\n{body}\n]\n<<<PYTHIA_LOOKUP_JSON_END>>>"

end Pythia.Lookup
