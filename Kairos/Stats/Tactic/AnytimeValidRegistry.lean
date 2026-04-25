/-
Kairos.Stats.Tactic.AnytimeValidRegistry — auto-tags the canonical
anytime-valid CS admissibility lemmas with `@[anytime_valid_lemma]`.

This file is split from `AnytimeValid.lean` because Lean does not let a
freshly-`initialize`d builtin attribute be applied in the same module
that declares it. Mirrors the `CSFamilyAttr` ↔ `CSFamilyRegistry` and
`StatsIneq` ↔ `StatsIneqRegistry` splits.

After this file is imported, `#anytime_valid_lemmas` lists every
registered admissibility / Ville-style closer. The `anytime_valid`
tactic dispatches against this list as the first stage of its ladder.

## Registered library

Each lemma below is verified to exist in the kairos library at this
commit. Comments note the source module and theorem flavour.

### Ville-family closers

  • `Kairos.Stats.ville_supermartingale` — countable-time Ville on a
    non-negative supermartingale (`VilleSupermartingale.lean`).
  • `Kairos.Stats.ville_supermartingale_finite` — finite-horizon
    Ville (`SubGaussianMG.lean`).
  • `Kairos.Stats.ville_supermartingale_infinite` — infinite-horizon
    Ville for non-negative supermartingales on probability measures
    (`BettingCS.lean`).
  • `Kairos.Stats.ville_supermartingale_unit_initial` — Ville with
    `f 0 = 1` a.s. (`VilleSupermartingale.lean`).
  • `Kairos.Stats.ville_ineq` — sub-Gaussian Ville (`SubGaussianMG.lean`).

### CS-family admissibility

  • `Kairos.Stats.hrStoppingRule_admissible` — Howard-Ramdas CS
    admissibility (`HowardRamdasCS.lean`).
  • `Kairos.Stats.bettingStoppingRule_admissible` — betting CS
    admissibility (`BettingCS.lean`).

## Lemmas requested by ATH-594 that do NOT exist at this commit

  • `Kairos.Stats.pacBayesStoppingRule_admissible` — PAC-Bayes CS
    admissibility. `PACBayesCS.lean` is a Phase C scaffold whose
    admissibility statement currently sits behind `sorry`. Will be
    re-tagged once the proof lands.

  • `Kairos.Stats.bernsteinStoppingRule_admissible` — Bernstein CS
    admissibility. Same status as PAC-Bayes (Phase C scaffold).

These are tracked but intentionally omitted from the registry until
their proofs are sorry-free.
-/
import Kairos.Stats.Tactic.AnytimeValid
import Kairos.Stats.HowardRamdasCS
import Kairos.Stats.BettingCS

namespace Kairos.Stats

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

end Kairos.Stats
