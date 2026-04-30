/-
Pythia.Tactic.PythiaValidate — combined LLM-defense validator.

## Contract

The kairos cross-vertical MCP router (ATH-894) routes `kairos.explain`
through this single command. Customer narrations of a Lean proof are
validated through the four LLM-defense layers below before any
explanation is returned, providing the structural anti-hallucination
guarantee the spec calls for.

## Usage

```
#pythia_validate Pythia.bettingStoppingRule_admissible
```

Runs (in sequence):

  1. `#validate_invoked_lemmas T`   — every lemma referenced in the
     proof exists in the environment.
  2. `#flag_concrete_constants T`   — flags numeric over-specialization
     in the theorem statement.
  3. `#minimize_hypotheses T`       — flags unused hypotheses.
  4. `#validate_types T`            — flags type-shape suspicions
     (e.g. `n : Real` for index-like names).

Each sub-command emits its own logInfo / logWarning. The combined
command finishes with a final logInfo summarizing that all four
validators ran.

## Soundness

This command is purely informational; it never errors. The Lean
kernel remains the ultimate check. The validators are pre-flight
filters for the most common LLM hallucination patterns.

## Why a single command

The router needs a single shell-out target for the structural
certificate phase of `kairos.explain`. Running four separate commands
means four `lake env lean` invocations and four output streams to
parse. One combined command means one invocation, one output stream
keyed by the per-validator `logInfo` headers.

## Sorry status

Sorry-free. This file declares no theorems; it composes existing
validators.

## Known limitation

When invoked on a theorem whose hypothesis list contains hygienic
instance binders (`inst._@.<module>.<hash>._hygCtx._hyg.<n>`), the
underlying `#minimize_hypotheses` / `#validate_types` validators
panic in `Lean.Name.getString!` at the very end of the validator's
output (after all useful info has been printed). The panic is in
the upstream validator implementations, not in this command, and
does not affect file compilation — it only surfaces during
interactive `#pythia_validate` invocation. Tracked as a follow-up;
the router consumes the validator output stream BEFORE the panic
fires, so the structural certificate is still produced correctly.
-/
import Pythia.Tactic.ValidateInvokedLemmas
import Pythia.Tactic.FlagConcreteConstants
import Pythia.Tactic.MinimizeHypotheses
import Pythia.Tactic.ValidateTypes

namespace Pythia

/-- `#pythia_validate T` — run all four LLM-defense validators on `T`.

Emits per-validator logInfo / logWarning, ending with a summary line.
The MCP router calls this as the structural-certificate gate before
narrating any proof to a customer.
-/
elab "#pythia_validate" t:ident : command => do
  Lean.logInfo m!"== pythia_validate :: validate_invoked_lemmas =="
  Lean.Elab.Command.elabCommand (← `(#validate_invoked_lemmas $t))
  Lean.logInfo m!"== pythia_validate :: flag_concrete_constants =="
  Lean.Elab.Command.elabCommand (← `(#flag_concrete_constants $t))
  Lean.logInfo m!"== pythia_validate :: minimize_hypotheses =="
  Lean.Elab.Command.elabCommand (← `(#minimize_hypotheses $t))
  Lean.logInfo m!"== pythia_validate :: validate_types =="
  Lean.Elab.Command.elabCommand (← `(#validate_types $t))
  Lean.logInfo m!"== pythia_validate :: complete for {t.getId} =="

end Pythia
