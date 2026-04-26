/-
Pythia.Tactic.ProbSimp — the `pdf_simp` / `prob_simp` tactic and
the `@[prob_simp]` curated simp-set for probability normalization.

A domain `simp`-based normalizer for the pythia library, modeled
on Mathlib's `field_simp` and the `stats_ineq` two-file pattern. Where
`pythia` is the general-purpose hammer and `stats_ineq` handles
inequalities, `prob_simp` (alias `pdf_simp`) specialises to:

  • PDF normalization `∫ x, f x ∂μ = 1` and `∫⁻ x, f x ∂μ = 1`
  • probability-measure axiom `μ Set.univ = 1`
  • `ENNReal → ℝ≥0 → ℝ` coercions in probability contexts
    (`(0:ℝ≥0∞).toReal = 0`, `(1:ℝ≥0∞).toReal = 1`, `toReal_ofReal`, …)
  • outer-measure lifting `μ.toOuterMeasure ↔ μ`
  • `IsProbabilityMeasure μ` axiom unfolding via `measure_univ`

Documented as a need across two independent Lean projects (arxiv
2602.02285 SLT and arxiv 2503.19605 Rademacher) which built custom simp
sets as workaround.

## Architecture

* `@[prob_simp]` user attribute. Two effects:
  1. Re-elaborates as `@[simp]` so Lean's `simp` machinery picks the
     lemma up automatically.
  2. Records the declaration name in `probSimpExt` so users can
     introspect via `#prob_simps`.

* `prob_simp` / `pdf_simp` tactics. Both run:
  1. `simp only` against every `@[prob_simp]`-tagged lemma
  2. ENNReal/NNReal coercion fallback (`push_cast`, `norm_cast`)
  3. `try rfl` to close definitional goals

* `#prob_simps` command — list every registered `@[prob_simp]` lemma.

## Lean-gating

Every `example` in `ProbSimpTest.lean` reduces to a Lean kernel-checked
term against `{propext, Classical.choice, Quot.sound}`. No `sorry`, no
skipped tests. Per Aidan's 2026-04-25 directive.

## Driver

Companion to `pythia` and `stats_ineq`.
-/
import Mathlib

namespace Pythia

open Lean Elab Meta Tactic

/-- Environment extension storing the names of all `@[prob_simp]`-tagged
declarations. Surfaced via `#prob_simps`. -/
initialize probSimpExt :
    SimpleScopedEnvExtension Name (Std.HashSet Name) ←
  registerSimpleScopedEnvExtension {
    addEntry := fun s n => s.insert n
    initial := ∅
  }

/-- `@[prob_simp]` — register a theorem as a pythia probability
normalization rule. The lemma is forwarded to Lean's `@[simp]`
attribute, so the underlying `simp` machinery (and therefore
`prob_simp` / `pdf_simp`) picks it up automatically. The declaration
name is also recorded in `probSimpExt` for `#prob_simps`. -/
initialize registerBuiltinAttribute {
  name := `prob_simp
  descr := "Register theorem as a pythia `@[simp]` rule for the `prob_simp` / `pdf_simp` tactic."
  add := fun decl _stx kind => do
    -- Forward to Lean's `@[simp]`. If the lemma is already in the
    -- simp set (e.g. upstream Mathlib tagging), swallow the
    -- duplicate-registration error: the scoped extension below still
    -- records the name, which is what `#prob_simps` cares about.
    let simpStx ← `(attr| simp)
    try
      Attribute.add decl `simp simpStx kind
    catch _ => pure ()
    probSimpExt.add decl
}

/-- `prob_simp` — pythia probability normalization tactic.

Runs `simp` against every `@[prob_simp]`-tagged lemma (which includes
all upstream Mathlib `@[simp]` lemmas we re-tagged), with an
ENNReal/NNReal coercion fallback (`push_cast`, `norm_cast`). Designed
for normalizing PDF / probability-measure / coercion goals that arise
in concentration-of-measure proofs. -/
syntax (name := probSimpTac) "prob_simp" : tactic

/-- `pdf_simp` — alias for `prob_simp`. Provided because the
PDF-normalization use case (`∫ x, f x ∂μ = 1`) is the most common
trigger for the tactic, and the alias makes call-sites self-documenting. -/
syntax (name := pdfSimpTac) "pdf_simp" : tactic

@[tactic probSimpTac] def evalProbSimp : Tactic := fun stx => do
  match stx with
  | `(tactic| prob_simp) =>
    evalTactic <| ← `(tactic|
      first
        | (simp; done)
        | (simp <;> first | (push_cast; ring_nf; done) | (norm_cast; done) | rfl | trivial)
        | (push_cast; simp; done)
        | (norm_cast; simp; done))
  | _ => throwUnsupportedSyntax

@[tactic pdfSimpTac] def evalPdfSimp : Tactic := fun stx => do
  match stx with
  | `(tactic| pdf_simp) =>
    evalTactic <| ← `(tactic| prob_simp)
  | _ => throwUnsupportedSyntax

/-- `#prob_simps` — list every theorem tagged `@[prob_simp]` in the
current scope. -/
elab "#prob_simps" : command => do
  let env ← getEnv
  let s := probSimpExt.getState env
  if s.isEmpty then
    logInfo "no prob simps registered (use @[prob_simp] to register one)"
  else
    let names := s.toList
    let lines := names.map (fun n => m!"  • {n}")
    logInfo (m!"registered prob simps ({names.length}):" ++ MessageData.joinSep lines "\n")

end Pythia
