/-
Pythia.Tactic.DomainRegistry — per-domain `@[*_lemma]` attribute family.

Today the `pythia` cascade dispatches to specialized tactics + the
single `@[stat_lemma]` aesop ruleset. As the library grows beyond
statistics into actuarial / numerical / comp-bio / Bayesian / control
domains, we want per-domain tagging so the cascade can route with
locality (`pythia (domain := actuarial)` runs only the actuarial
ruleset before falling through, avoiding aesop blowup from
cross-domain rule explosion).

This module declares the per-domain attributes + their backing aesop
rule sets. `@[stat_lemma]` continues to live in `Pythia.Tactic.Pythia`
for backward compatibility; the new attributes here are the
v0.4+ taxonomy.

## Architecture

For each domain D, we declare:

  • aesop rule set `Pythia.D` (declared via `declare_aesop_rule_sets`)
  • attribute `@[D_lemma]` that forwards to `aesop safe apply (rule_sets := [Pythia.D])`

The `pythia` cascade can then dispatch with optional domain hint:

  ```
  pythia (domain := actuarial)
  ```

falling through to `[Pythia.Actuarial]` rule set first, then the
existing fallback ladder.

## Status

v1 (this file): declare the attributes + rule sets. The cascade
dispatch with domain hint is wired in `Pythia.Tactic.Pythia` at
v0.4 first-customer landing.

## Domains

  • `actuarial`  — survival analysis, mortality models, ruin theory,
    pricing principles, reserving methods.
  • `numerical`  — ODE existence/uniqueness, Lyapunov stability,
    optimization KKT, signal processing, numerical linear algebra.
  • `bio`        — chemical reaction network ODEs, phylogenetic
    likelihood, population genetics, stochastic biology.
  • `bayes`      — posterior consistency, MCMC convergence rates,
    conjugate posteriors, total-variation mixing.
  • `control`    — Lyapunov stability for control systems, transfer
    functions, frequency response.

The full plan is in ATH-718 (Pythia next-phase epic).
-/
import Mathlib
import Aesop

-- Aesop rule sets for each domain. Declared at module load so the
-- attribute bodies below can reference them. Per-domain rule-set
-- isolation prevents one domain's rules from shadowing another's
-- during search.
declare_aesop_rule_sets [Pythia.Actuarial]
declare_aesop_rule_sets [Pythia.Numerical]
declare_aesop_rule_sets [Pythia.Bio]
declare_aesop_rule_sets [Pythia.Bayes]
declare_aesop_rule_sets [Pythia.Control]

namespace Pythia

open Lean

/-! ### `@[actuarial_lemma]` attribute -/

syntax (name := actuarialLemma) "actuarial_lemma" : attr

initialize registerBuiltinAttribute {
  name := `actuarialLemma
  descr := "Register theorem as an `@[aesop safe apply (rule_sets := [Pythia.Actuarial])]` rule for the actuarial domain (survival, mortality, ruin theory, pricing, reserving)."
  add := fun decl _stx kind => do
    let aesopStx ← `(attr| aesop safe apply (rule_sets := [Pythia.Actuarial]))
    Attribute.add decl `aesop aesopStx kind
}

/-! ### `@[numerical_lemma]` attribute -/

syntax (name := numericalLemma) "numerical_lemma" : attr

initialize registerBuiltinAttribute {
  name := `numericalLemma
  descr := "Register theorem as an `@[aesop safe apply (rule_sets := [Pythia.Numerical])]` rule for the numerical-methods domain (ODE existence, Lyapunov stability, KKT, signal processing, numerical LA)."
  add := fun decl _stx kind => do
    let aesopStx ← `(attr| aesop safe apply (rule_sets := [Pythia.Numerical]))
    Attribute.add decl `aesop aesopStx kind
}

/-! ### `@[bio_lemma]` attribute -/

syntax (name := bioLemma) "bio_lemma" : attr

initialize registerBuiltinAttribute {
  name := `bioLemma
  descr := "Register theorem as an `@[aesop safe apply (rule_sets := [Pythia.Bio])]` rule for the computational-biology domain (CRN, phylogenetic likelihood, population genetics, stochastic biology)."
  add := fun decl _stx kind => do
    let aesopStx ← `(attr| aesop safe apply (rule_sets := [Pythia.Bio]))
    Attribute.add decl `aesop aesopStx kind
}

/-! ### `@[bayes_lemma]` attribute -/

syntax (name := bayesLemma) "bayes_lemma" : attr

initialize registerBuiltinAttribute {
  name := `bayesLemma
  descr := "Register theorem as an `@[aesop safe apply (rule_sets := [Pythia.Bayes])]` rule for the Bayesian-inference domain (posterior consistency, MCMC convergence, conjugate posteriors, mixing time)."
  add := fun decl _stx kind => do
    let aesopStx ← `(attr| aesop safe apply (rule_sets := [Pythia.Bayes]))
    Attribute.add decl `aesop aesopStx kind
}

/-! ### `@[control_lemma]` attribute -/

syntax (name := controlLemma) "control_lemma" : attr

initialize registerBuiltinAttribute {
  name := `controlLemma
  descr := "Register theorem as an `@[aesop safe apply (rule_sets := [Pythia.Control])]` rule for the control-theory domain (Lyapunov stability, transfer functions, frequency response)."
  add := fun decl _stx kind => do
    let aesopStx ← `(attr| aesop safe apply (rule_sets := [Pythia.Control]))
    Attribute.add decl `aesop aesopStx kind
}

/-! ### Introspection commands -/

/-- `#pythia_domains` — list every registered domain attribute and the
aesop rule set it backs. -/
elab "#pythia_domains" : command => do
  Lean.logInfo m!"Pythia per-domain attributes:\n  • @[actuarial_lemma] → Pythia.Actuarial\n  • @[numerical_lemma] → Pythia.Numerical\n  • @[bio_lemma]       → Pythia.Bio\n  • @[bayes_lemma]     → Pythia.Bayes\n  • @[control_lemma]   → Pythia.Control\n\nLegacy stats: @[stat_lemma] → Pythia (declared in Pythia.Tactic.Pythia).\n\nTo route the `pythia` cascade through a single domain ruleset, use\n`pythia (domain := actuarial)` etc. (Wired in v0.4; today the cascade\ndispatches through @[stat_lemma] regardless of domain.)"

end Pythia
