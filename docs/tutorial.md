# Lean for Statisticians — a pythia tutorial

This is the on-ramp for working statisticians who have never used Lean 4
before. Three sections, each one self-contained:

1. *Hello, pythia*: install Lean + Mathlib + pythia, close one Ville
   bound. Five minutes from zero.
2. *The four hammer tactics*: when to use `pythia` vs `anytime_valid`
   vs `stats_ineq` vs `prob_simp`. Lift-by-example.
3. *Adding your own theorem*: tag with `@[stat_lemma]`, prove it,
   verify it joins the cascade.

The bar is a competent statistician with no Lean experience can follow
this in an afternoon and close their first Ville bound. If you get
stuck, open an issue on
[github.com/athanor-ai/pythia](https://github.com/athanor-ai/pythia).

## 1. Hello, pythia

### 1.1 Install Lean + Mathlib + pythia (about 5 minutes)

Pythia targets Lean 4. Install via `elan`, the Lean version manager:

```bash
curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh
```

Restart your shell (or `source ~/.elan/env`). Verify the install:

```bash
elan --version
```

Now clone pythia and let `lake` (the Lean build tool) fetch
Mathlib + dependencies. The first build takes several minutes
because it pulls Mathlib's pre-compiled cache:

```bash
git clone https://github.com/athanor-ai/pythia.git
cd pythia
lake exe cache get
lake build
```

When `lake build` reports success (~8000 jobs at the time of writing),
you are ready to write proofs.

### 1.2 Your first Ville bound

Create a new file `MyFirstProof.lean` in the project root and paste:

```lean
import Mathlib
import Pythia

open MeasureTheory ProbabilityTheory

example
    {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {f : ℕ → Ω → ℝ} {𝓕 : Filtration ℕ mΩ}
    (hsup : Supermartingale f 𝓕 μ)
    (hnn : ∀ t ω, 0 ≤ f t ω)
    (hint : Integrable (f 0) μ)
    {c : ℝ} (hc : 0 < c) :
    μ {ω | ∃ t, f t ω ≥ c} ≤ ENNReal.ofReal ((∫ ω, f 0 ω ∂μ) / c) := by
  anytime_valid
```

Then build it:

```bash
lake env lean MyFirstProof.lean
```

Lean prints nothing on success. That's it: you just proved Ville's
inequality for non-negative supermartingales in one tactic. Next: how
to pick the right tactic.

## 2. The four hammer tactics

Pythia ships ten tactics in total (see `docs/sledgehammer_dispatch.md`
for the full ladder), but four cover the typical statistician's
day-to-day:

### 2.1 `pythia` — the default closer

When you don't know which tactic to reach for, reach for `pythia`. It
runs a cascade through aesop with the `@[stat_lemma]` ruleset, falls
back to `simp + linarith + measurability`, and ends at the SMT oracles
(`z3_check`, `cvc5_check`) for residual arithmetic. If anything closes
the goal, `pythia` reports it.

```lean
example (n : ℕ) (h : 0 < n) : 0 < n + 1 := by pythia
example (a b : ℝ) (h₁ : 0 ≤ a) (h₂ : 0 ≤ b) : 0 ≤ a + b := by pythia
example (X : ℝ → ℝ) (hX_cont : Continuous X) (x : ℝ) :
    Continuous (fun y => X y + x) := by pythia
```

If you want to see *which* rung closed the goal, use `pythia?`:

```lean
example (a : ℝ) (h : 0 ≤ a) : 0 ≤ a + 1 := by pythia?
-- Lean reports: pythia closed via stats_ineq (linarith)
```

### 2.2 `anytime_valid` — Ville bounds, supermartingale tail bounds, e-process tails

When the goal is the probability of a martingale crossing a
threshold, reach for `anytime_valid`:

```lean
example
    {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {Y : ℕ → Ω → ℝ} {𝓕 : Filtration ℕ mΩ}
    (hY : Supermartingale Y 𝓕 μ) (hY_nn : ∀ t ω, 0 ≤ Y t ω)
    (hY_int : Integrable (Y 0) μ) {c : ℝ} (hc : 0 < c) :
    μ {ω | ∃ t, Y t ω ≥ c} ≤ ENNReal.ofReal ((∫ ω, Y 0 ω ∂μ) / c) := by
  anytime_valid
```

Behind the scenes, `anytime_valid` searches the `@[anytime_valid_lemma]`
ruleset (Ville's inequality, sub-gamma Ville, Howard-Ramdas
admissibility, betting-CS admissibility) and tries each.

### 2.3 `stats_ineq` — scalar inequalities

When the goal is a real-valued inequality without an integral or
expectation, `stats_ineq` chains `linarith` + `nlinarith` + `bound` +
`gcongr` + `polyrith` and registered closing-form scalar inequalities:

```lean
example (x : ℝ) (h : 0 ≤ x) : 0 ≤ x + Real.sqrt x := by stats_ineq
example (a b c : ℝ) (h_a : 0 < a) (h_b : 0 < b) :
    a / (a + b + c.exp) ≤ a / (a + b) := by stats_ineq
```

### 2.4 `prob_simp` — probability normalization rewriter

When the goal needs `ProbabilityMeasure` / `pdf` / `cdf` /
`withDensity` rewriting (closer to a `simp_rw` than a hammer):

```lean
example {Ω : Type*} {μ : Measure Ω} [IsProbabilityMeasure μ] :
    μ Set.univ = 1 := by prob_simp
```

The full ladder beyond these four (`z3_check`, `cvc5_check`,
`vampire_check`, `e_check`, `disprove`, `pythia?`) is documented in
`docs/sledgehammer_dispatch.md`.

## 3. Adding your own theorem

The pay-off of a registry library: every theorem you tag with
`@[stat_lemma]` joins the cascade. Future calls to `pythia` will
attempt your theorem alongside Mathlib's. Here is the shape:

### 3.1 Prove the theorem

In your project file, prove your statistical fact as a regular Lean
theorem. Make sure the proof is closing-form, not a long rewrite chain
(aesop-tagged lemmas should match a goal head, then conclude):

```lean
theorem my_concentration_bound
    (X : ℝ) (hX : |X| ≤ 1) :
    Real.exp X ≤ 1 + X + X^2 := by
  -- proof here
  sorry  -- replaced with a real proof in your project
```

### 3.2 Tag it

Add the attribute right before the `theorem` keyword:

```lean
@[stat_lemma]
theorem my_concentration_bound
    (X : ℝ) (hX : |X| ≤ 1) :
    Real.exp X ≤ 1 + X + X^2 := by
  ...
```

Lean compiles it; the `@[stat_lemma]` attribute joins the `Pythia`
aesop ruleset.

### 3.3 Verify it joins the cascade

Use `#stat_lemmas` to list every registered theorem in the Pythia
ruleset:

```lean
#stat_lemmas
-- Lean prints a table of all @[stat_lemma]-tagged theorems,
-- including yours.
```

Now any goal that head-matches your conclusion will pick up your
theorem during `pythia` dispatch:

```lean
example (X : ℝ) (hX : |X| ≤ 1) : Real.exp X ≤ 1 + X + X^2 := by pythia
-- Lean closes via my_concentration_bound from the cascade.
```

### 3.4 Other registry attributes

Pythia supports several attributes for different rungs of the
cascade:

| Attribute | Rung | What kind of theorem |
|---|---|---|
| `@[stat_lemma]` | `pythia` aesop ruleset | Closing-form statistical theorems. |
| `@[anytime_valid_lemma]` | `anytime_valid` ruleset | Ville-style supermartingale tail bounds. |
| `@[stats_ineq]` | `stats_ineq` bound-set | Scalar / vector inequalities. |
| `@[prob_simp]` | `prob_simp` simp-set | Probability-normalization rewrite rules. |
| `@[tail_bound]` | `TightTail.report` | Concentration families with explicit constants. |
| `@[actuarial_lemma]` | `pythia (domain := actuarial)` | Per-domain extension (v0.4+). |

The full attribute reference is in `docs/sledgehammer_dispatch.md`.

## Where to next

- `docs/concentration_cookbook.md` — recipes for sub-Gaussian /
  sub-gamma / Bernstein / Bennett / Freedman bounds.
- `docs/sledgehammer_dispatch.md` — the full ten-tactic cascade.
- `docs/reflective_oracles.md` — how the Z3 / CVC5 / Vampire / E
  oracles reconstruct closures into kernel-checked terms.
- `docs/llm_defense.md` — the Layer 3 LLM-defense guards
  (`#validate_invoked_lemmas`, `#validate_types`, etc.) for catching
  generated-proof hallucinations before lake build.
- `Pythia/Bench/MiniPythia.lean` — the 30-theorem reference
  benchmark, anytime-valid analogue of MiniF2F.

## Reporting issues

If a goal you expected pythia to close does not close, or a tagged
theorem does not get picked up:

- Check your tag matches the rung shape (closing-form vs rewrite).
- Run `pythia?` (verbose) to see which rungs were attempted.
- File an issue at
  [github.com/athanor-ai/pythia/issues](https://github.com/athanor-ai/pythia/issues)
  with the theorem, the tag, and the `pythia?` output. We try to ship
  a fix or a cookbook entry within the week.
