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

## 3. The marquee anytime-valid bound

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

## 4. Discoverability

```lean
#cs_families       -- list all @[cs_family]-tagged definitions
#stat_lemmas       -- describe the @[stat_lemma] aesop ruleset
#ville             -- preview the marquee Ville statement
```

Run any of these in your `Mypaper.lean` to introspect what's
available. `pythia` searches across everything `#stat_lemmas` would
list.

## 5. Where to go next

* `examples/`: copy-paste examples for every public tactic.
* `ROADMAP.md`: the full multi-tier theorem plan (Bernstein, SPRT,
  e-detector, Glivenko-Cantelli, Robbins-Monro, etc.).
* `docs/lean_lsp_mcp_setup.md`: sub-second proof feedback via the
  lean-lsp-mcp MCP server (recommended for any serious user).
* `Pythia.API`: the curated public theorem index.

## Honest limitations

* `pythia` v0.6.0 is iteration 1: aesop ruleset + Mathlib fall-through.
  Goal-shape dispatch (route `μ{∃ t, ...}` goals to `anytime_valid`
  before aesop) and hammer-style premise selection ship in iteration
  2.
* Tier 2 (SPRT + Wald's identity) is scaffolded but the proofs are
  flagged sorries; full closure ships v0.5.x.
* Tier 8 (`pythia` itself) is shipping as part of the v0.6.0 cycle.
