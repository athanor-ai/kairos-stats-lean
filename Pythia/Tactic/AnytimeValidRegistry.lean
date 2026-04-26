/-
Pythia.Tactic.AnytimeValidRegistry — auto-tags the canonical
anytime-valid CS admissibility lemmas with `@[anytime_valid_lemma]`.

This file is split from `AnytimeValid.lean` because Lean does not let a
freshly-`initialize`d builtin attribute be applied in the same module
that declares it. Mirrors the `CSFamilyAttr` ↔ `CSFamilyRegistry` and
`StatsIneq` ↔ `StatsIneqRegistry` splits.

After this file is imported, `#anytime_valid_lemmas` lists every
registered admissibility / Ville-style closer. The `anytime_valid`
tactic dispatches against this list as the first stage of its ladder.

## Registered library

Each lemma below is verified to exist in the pythia library at this
commit. Comments note the source module and theorem flavour.

### Ville-family closers

  • `Pythia.ville_supermartingale` — countable-time Ville on a
    non-negative supermartingale (`VilleSupermartingale.lean`).
  • `Pythia.ville_supermartingale_finite` — finite-horizon
    Ville (`SubGaussianMG.lean`).
  • `Pythia.ville_supermartingale_infinite` — infinite-horizon
    Ville for non-negative supermartingales on probability measures
    (`BettingCS.lean`).
  • `Pythia.ville_supermartingale_unit_initial` — Ville with
    `f 0 = 1` a.s. (`VilleSupermartingale.lean`).
  • `Pythia.ville_ineq` — sub-Gaussian Ville (`SubGaussianMG.lean`).

### CS-family admissibility

  • `Pythia.hrStoppingRule_admissible` — Howard-Ramdas CS
    admissibility (`HowardRamdasCS.lean`).
  • `Pythia.bettingStoppingRule_admissible` — betting CS
    admissibility (`BettingCS.lean`).

## Lemmas requested by that do NOT exist at this commit

  • `Pythia.pacBayesStoppingRule_admissible` — PAC-Bayes CS
    admissibility. `PACBayesCS.lean` is a Phase C scaffold whose
    admissibility statement currently sits behind `sorry`. Will be
    re-tagged once the proof lands.

  • `Pythia.bernsteinStoppingRule_admissible` — Bernstein CS
    admissibility. Same status as PAC-Bayes (Phase C scaffold).

These are tracked but intentionally omitted from the registry until
their proofs are sorry-free.
-/
import Pythia.Tactic.AnytimeValid
import Pythia.HowardRamdasCS
import Pythia.BettingCS

namespace Pythia

attribute [anytime_valid_lemma]
  -- Ville-family closers
  ville_supermartingale
  ville_supermartingale_finite
  ville_supermartingale_infinite
  ville_supermartingale_unit_initial
  ville_ineq
  -- CS-family admissibility theorems
  hrStoppingRule_admissible
  bettingStoppingRule_admissible

end Pythia
