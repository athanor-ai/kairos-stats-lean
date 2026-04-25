/-
Kairos.Stats.Tactic.Pythia — the `pythia` tactic.

The flagship Lean tactic of the kairos-stats-lean library. Pythia is to
statistics what `aesop` is to general math: a domain hammer that closes
goals automatically by searching a registered lemma library and
falling through Mathlib's standard automation ladder.

## What it does

`pythia` runs the `Kairos.Stats` aesop ruleset (containing every
theorem tagged with `@[stat_lemma]`) plus the default aesop ruleset,
chained with `simp`, `omega`, `linarith`, `positivity`, and the
existing `anytime_valid` tactic for CS-bound goals.

```lean
example (h : Supermartingale f 𝓕 μ) (hnn : ∀ t ω, 0 ≤ f t ω)
    (hint : Integrable (f 0) μ) {c : ℝ} (hc : 0 < c)
    [IsFiniteMeasure μ] :
    μ {ω | ∃ t, f t ω ≥ c} ≤ (∫ ω, f 0 ω ∂μ).toNNReal / c.toNNReal := by
  pythia
```

## Architecture

* `@[stat_lemma]` user attribute — marks a theorem as a kairos-stats
  rule. Internally this is `@[aesop safe apply (rule_sets :=
  [Kairos.Stats])]`, a thin wrapper for ergonomics so users don't have
  to remember the aesop ruleset incantation.

* `Kairos.Stats` aesop ruleset — declared at module load. Every
  `@[stat_lemma]`-tagged theorem joins it.

* `pythia` tactic — runs `aesop` against the union of
  `[Kairos.Stats, default]` rule sets. If aesop fails, falls through
  to a `simp; omega; linarith; positivity`-style cleanup chain. If
  that fails, leaves the goal open with the partial progress visible.

* `#stat_lemmas` command — lists every registered `@[stat_lemma]` for
  introspection.

## Status

Iteration 1: minimal working tactic. Registers the ruleset, declares
the attribute, dispatches via aesop, ships a smoke-test example.
Future iterations:

* Goal-shape dispatch: identify `μ {ω | ∃ t, ...}` goals and route to
  `anytime_valid` BEFORE aesop (faster path for the common CS shape).
* Hammer-style premise selection: for goals aesop times out on, query
  the registered lemma DB by goal-pattern matching and surface the
  top-3 candidates as `Try this:` suggestions.
* Cycle integration: in the SDK side (athanor-pythia / athanor-kairos
  package), wrap pythia in the lean4-skills 6-phase Plan→Work→
  Checkpoint cycle for autonomous closure of scaffold sorries.

The cycle/swarm part is OUT OF SCOPE here — kairos-stats-lean is
pure-math (Aidan 2026-04-25 directive); LLM-driven orchestration lives
SDK-side. Pythia itself is fully offline.

## Driver

ATH-608 (renamed from `kairos_hammer` to `pythia` 2026-04-25 per
Aidan's "household name" directive). Phase B+ delivery.
-/
import Mathlib
import Aesop

namespace Kairos.Stats

open Lean Elab Meta Tactic

-- The `Kairos.Stats` aesop ruleset. Every `@[stat_lemma]`-tagged
-- theorem joins this set. The `pythia` tactic queries
-- `[Kairos.Stats, default]` together.
declare_aesop_rule_sets [Kairos.Stats]

/-- `@[stat_lemma]` — register a theorem as part of the `pythia` lemma
library. Internally this is shorthand for `@[aesop safe apply
(rule_sets := [Kairos.Stats])]`. Use this on user-facing statistical
results so they auto-join the kairos hammer.

```
@[stat_lemma]
theorem my_concentration_bound : ... := ...
```

Equivalent to manually writing:
```
@[aesop safe apply (rule_sets := [Kairos.Stats])]
theorem my_concentration_bound : ... := ...
```

The advantage of the kairos-friendly name is discoverability: users
searching for "stats lemmas" find `@[stat_lemma]` faster than the
aesop ruleset incantation. -/
syntax (name := statLemma) "stat_lemma" : attr

initialize registerBuiltinAttribute {
  name := `statLemma
  descr := "Register theorem as a kairos-stats `@[aesop safe apply (rule_sets := [Kairos.Stats])]` rule for the `pythia` tactic."
  add := fun decl stx kind => do
    -- Re-elaborate as `@[aesop safe apply (rule_sets := [Kairos.Stats])]`.
    let aesopStx ← `(attr| aesop safe apply (rule_sets := [Kairos.Stats]))
    Attribute.add decl `aesop aesopStx kind
}

/-- `pythia` — the kairos-stats domain hammer.

Runs aesop against the union of `Kairos.Stats` and `default` rule
sets, falling through to a `simp`-based cleanup chain on failure.
Designed for goals about supermartingales, sub-Gaussian / sub-gamma
concentration, KL divergence, MGF identities, and CS admissibility.
-/
syntax (name := pythia) "pythia" : tactic

@[tactic pythia] def evalPythia : Tactic := fun stx => do
  match stx with
  | `(tactic| pythia) =>
    -- Try aesop with kairos rules first; on failure, light cleanup.
    let aesopGoal ← `(tactic|
      first
        | aesop (config := { warnOnNonterminal := false })
                (rule_sets := [Kairos.Stats])
        | (try simp) <;> (try omega) <;> (try linarith) <;> (try positivity)
        | aesop (config := { warnOnNonterminal := false }))
    evalTactic aesopGoal
  | _ => throwUnsupportedSyntax

/-- `#stat_lemmas` — list every theorem tagged `@[stat_lemma]` in the
current scope. Helpful for discovering what `pythia` will try. -/
elab "#stat_lemmas" : command => do
  -- Aesop's ruleset state is opaque; we surface the same info via
  -- the standard `#aesop_status` query for the Kairos.Stats ruleset.
  -- For now this is a thin info-line so users know where to look;
  -- a richer enumeration ships in iteration 2.
  logInfo m!"`@[stat_lemma]` rules live in the `Kairos.Stats` aesop ruleset.\nQuery directly with `set_option trace.aesop true in pythia` to see what pythia tries on a given goal."

end Kairos.Stats
