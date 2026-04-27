# Demo: pythia in 5 minutes

A guided walkthrough that takes a fresh Lean 4 user from "I just heard
of pythia" to "I closed a confidence-sequence admissibility goal in
one tactic call."

## Prerequisites

* Lean 4 toolchain installed (elan + lake; `curl
  https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh
  -sSf | sh`).
* About ~5 GB free disk for Mathlib oleans.

## 1. New project

```bash
mkdir mypaper && cd mypaper
lake init mypaper
```

Add to your `lakefile.lean`:

<!-- doctest: lakefile -->
```lean
require pythia from git
  "https://github.com/athanor-ai/pythia.git" @ "main"
```

```bash
lake exe cache get      # pull Mathlib oleans (one-time, ~5 min)
lake build              # warm full build (~3 min)
```

## 2. The Hello-Pythia program

`Mypaper.lean`:

```lean
import Pythia.Tactic.Pythia

open Pythia

@[stat_lemma]
theorem nonneg_sum_of_nonneg_real (a b : ℝ)
    (ha : 0 ≤ a) (hb : 0 ≤ b) : 0 ≤ a + b := by linarith

example (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) : 0 ≤ a + b := by pythia
```

```bash
lake build              # should print "Build completed successfully"
```

That's it: you've registered a custom statistical lemma and closed a
goal with the `pythia` hammer.

## 3. The anytime-valid bound

This is what the library actually exists for. Open
`Mypaper.lean` again and replace the example with:

```lean
import Pythia.Tactic.AnytimeValid

open Pythia MeasureTheory

example
    {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω}
    [IsFiniteMeasure μ] {f : ℕ → Ω → ℝ} {𝓕 : Filtration ℕ m0}
    (hsup : Supermartingale f 𝓕 μ) (hnn : ∀ t ω, 0 ≤ f t ω)
    (hint : Integrable (f 0) μ) {c : ℝ} (hc : 0 < c) :
    μ {ω : Ω | ∃ t : ℕ, f t ω ≥ c}
      ≤ (∫ ω, f 0 ω ∂μ).toNNReal / c.toNNReal := by
  anytime_valid
```

`lake build`: proof closed in one tactic call.

This is Ville's inequality on a non-negative supermartingale. With
`pythia` and `anytime_valid`, every confidence-sequence
admissibility theorem in this library closes in under 5 lines for
users who don't want to learn the Mathlib martingale API.

## 4. Mix with the standard Lean toolkit

`pythia` is not a black box: it composes naturally with `aesop`,
`linarith`, `simp`, and the rest of the standard Lean tactic set.
The worked examples below all live in `demo/aesop_integration.lean`
and build clean via `lake env lean demo/aesop_integration.lean`.

### 4a. pythia falling through to aesop

When no `@[stat_lemma]` rule covers the goal, `pythia` falls through
to the `default` aesop ruleset and Mathlib's automation:

```lean
import Pythia

-- List identity: no stat rule applies; aesop closes it.
example (l : List ℕ) : l ++ [] = l := by pythia

-- Propositional conjunction: again, aesop's default set closes it.
example (p q : Prop) (hp : p) (hq : q) : p ∧ q := by pythia
```

### 4b. pythia composed with linarith in a tactic block

Use `pythia` to normalise or discharge a subgoal, then hand the
residual to `linarith`:

<!-- doctest: skip-reason: continuation of prior block -->
```lean
example (a b : ℝ) (ha : 0 < a) (hb : 0 < b) (h : a + b ≤ 3) : a < 3 := by
  have hpos : 0 < a + b := by pythia   -- pythia closes positivity subgoal
  linarith                             -- linarith closes the chain
```

This pattern is useful when `pythia` can handle the domain-specific
part (nonnegativity, registered lemma) and a linear arithmetic step
closes out the conclusion.

### 4c. Direct aesop ruleset usage

`@[stat_lemma]` is shorthand for
`@[aesop safe apply (rule_sets := [Pythia])]`.
If you need aesop's full configuration surface, call the ruleset directly:

<!-- doctest: skip-reason: continuation of prior block -->
```lean
@[stat_lemma]
theorem sub_self_zero (x : ℝ) : x - x = 0 := sub_self x

-- Equivalent to `by pythia`, but with direct ruleset access:
example (y : ℝ) : y - y = 0 := by
  aesop (rule_sets := [Pythia])

-- With explicit config (suppress non-terminal warning for composed blocks):
example (z : ℝ) : z - z = 0 := by
  aesop (config := { warnOnNonterminal := false }) (rule_sets := [Pythia])
```

### 4d. simp only pre-processing, then pythia

Normalise the goal with a targeted `simp only` pass first, then hand
the simplified form to `pythia`. This avoids full `simp` blowing up
the goal while still benefiting from pythia's dispatch chain:

<!-- doctest: skip-reason: continuation of prior block -->
```lean
example (x : ℝ) : x * 1 + 0 = x := by
  simp only [mul_one, add_zero]
  pythia

example (n : ℕ) (h : n ≤ 4) : n + 0 ≤ 4 := by
  simp only [add_zero]
  pythia
```

## 5. Under the hood

`pythia` runs a three-step dispatch in order:

1. `aesop (rule_sets := [Pythia])`. Every theorem tagged `@[stat_lemma]`
   lives in this ruleset. If any registered rule closes the goal,
   the tactic succeeds here.

2. `aesop` (default ruleset). If no pythia-specific rule matched,
   the tactic retries with Mathlib's general aesop set. This covers
   List/Option/Nat lemmas, propositional logic, and anything else
   aesop's default configuration handles.

3. `simp` then `omega` / `linarith` / `positivity` fallback chain.
   For goals that aesop cannot close (typically linear arithmetic
   over ℝ or ℕ), the chain fires in order and the first tactic
   that closes the goal wins.

If all three steps fail, `pythia` leaves the goal open with whatever
partial progress is visible, so you can see what remains.

The full implementation is in `Pythia/Tactic/Pythia.lean`. The `Pythia`
aesop ruleset is declared there via `declare_aesop_rule_sets [Pythia]`,
and `@[stat_lemma]` is a thin attribute wrapper around
`@[aesop safe apply (rule_sets := [Pythia])]`.

## Discoverability

<!-- doctest: cmd-only -->
```lean
#cs_families       -- list all @[cs_family]-tagged definitions
#stat_lemmas       -- describe the @[stat_lemma] aesop ruleset
#ville             -- preview the Ville statement
```

Run any of these in your `Mypaper.lean` to introspect what's
available. `pythia` searches across everything `#stat_lemmas` would
list.

## Where to go next

* `examples/`: copy-paste examples for every public tactic.
* `Pythia.API`: the curated public theorem index.
* `docs/lean_lsp_mcp_setup.md`: sub-second proof feedback via the
  lean-lsp-mcp MCP server (recommended for any serious user).

## Honest limitations

* v0.6.0 is shipped: the five tactics (`pythia`, `stats_ineq`,
  `prob_simp`, `anytime_valid`, `z3_check`) are live on main.
* Goal-shape dispatch (route `μ{∃ t, ...}` goals to `anytime_valid`
  before aesop) and hammer-style premise selection are in-flight for
  the next iteration.
* In-flight theorem closures: Bernstein concentration (Tier 1),
  e-detector closures (Tier 2), and the matrix Bernstein dependency
  chain (Tier 7) have scaffolded sorries; full closure is in progress.
