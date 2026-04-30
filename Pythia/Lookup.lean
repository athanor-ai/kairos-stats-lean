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
    confidence := 1.0 }
  -- TODO (when headline theorems land):
  --   • asymptotics.delta_method.scalar (DeltaMethod headline)
  --   • time_series.newey_west.consistency (NeweyWest headline)
  --   • hypothesis_testing.bonferroni (HypothesisTest headline)
  --   • hardware.float.ieee754_round_trip (IEEE754 headline)
  --   • neuroscience.cable_equation.steady_state (Neuroscience headline)
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

end Pythia.Lookup
