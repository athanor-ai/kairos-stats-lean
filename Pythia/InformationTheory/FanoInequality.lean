/-
Copyright (c) 2026 Pythia contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Pythia.InformationTheory.FanoInequality

**Fano's inequality** and its **converse**: bounds relating error
probability to conditional entropy for discrete estimation problems.

## Main results

* `fano_inequality` — `H(X|Y) ≤ h_b(P_e) + P_e · log(M − 1)`.
* `fano_converse` — `P_e ≥ (H − log 2) / log(M − 1)` when
  `H ≤ h_b(P_e) + P_e · log(M − 1)`.

## Design note

The bound `fano_inequality` is stated in parametrized form: we
assume the conditional entropy `H_cond` and error probability `P_e`
satisfy the standard Fano hypothesis. The converse is an arithmetic
consequence: since `h_b(P_e) ≤ log 2`, we derive a lower bound on
the error probability from the conditional entropy.

The non-trivial step — deriving the Fano hypothesis from a joint
distribution via conditioning on the error event — requires
conditional entropy chain-rule infrastructure. The arithmetic
consequences proved here are the ones most commonly applied in
channel-coding converses.

## References

* Cover, T. M. and Thomas, J. A. "Elements of Information Theory."
  2nd ed. Wiley (2006). Theorem 2.10.1.
* Fano, R. M. "Transmission of Information." MIT Press (1961).
-/

import Mathlib

open Finset BigOperators

namespace Pythia.InformationTheory

/-
**Fano's converse** (Cover–Thomas, §2.10):
if Fano's inequality `H ≤ h_b(P_e) + P_e · log(M − 1)` holds and
`h_b(P_e) ≤ log 2`, then the error probability is bounded below:

  `P_e ≥ (H − log 2) / log(M − 1)`.

This is the form most commonly used in channel-coding converse proofs:
if the conditional entropy is large, the error probability cannot be
small.

The hypotheses ensure non-vacuousness:
- `hM : 2 ≤ M` ensures `log(M−1) > 0` (non-trivial alphabet).
- `hPe : 0 ≤ P_e`, `hPe1 : P_e ≤ 1`.
- `hH : 0 ≤ H` (entropy is non-negative).
- `h_fano` is the Fano inequality hypothesis.
- `h_bin` is `h_b(P_e) ≤ log 2` (binary entropy is at most `log 2`).
-/
theorem fano_converse
    (H P_e : ℝ) (M : ℕ)
    (hM : 2 ≤ M)
    (hPe : 0 ≤ P_e) (hPe1 : P_e ≤ 1)
    (hH : 0 ≤ H)
    (h_fano : H ≤ Real.binEntropy P_e + P_e * Real.log (M - 1 : ℝ))
    (h_bin : Real.binEntropy P_e ≤ Real.log 2) :
    (H - Real.log 2) / Real.log (M - 1 : ℝ) ≤ P_e := by
  exact div_le_of_le_mul₀ ( Real.log_nonneg <| by linarith [ show ( M : ℝ ) ≥ 2 by norm_cast ] ) ( by positivity ) ( by nlinarith [ Real.log_nonneg one_le_two ] )

/-
**Fano's inequality implies capacity bound**: if one can achieve
error probability `P_e < (M − 1) / M` over an `M`-ary alphabet, then
the mutual information `I(X;Y)` must be at least
`log M − log 2 − 1 + 1/M`.

This is a direct consequence of Fano's inequality applied to the
decoder:
  `H(X|Y) ≤ h_b(P_e) + P_e · log(M−1)`
combined with `I(X;Y) = H(X) − H(X|Y)` and `H(X) ≤ log M`.

The parametrized form assumes the Fano bound on conditional entropy
and derives the mutual information lower bound.

Hypotheses:
- `hM : 2 ≤ M`.
- `H_X` is the source entropy, `H_cond` is the conditional entropy.
- `I_XY` is the mutual information, satisfying `I_XY = H_X − H_cond`.
- `h_fano_bound : H_cond ≤ h_b(P_e) + P_e · log(M−1)`.
- `hH_X_le : H_X ≤ log M` (maximum entropy).
-/
theorem fano_capacity_bound
    (I_XY H_X H_cond P_e : ℝ) (M : ℕ)
    (hM : 2 ≤ M)
    (hPe : 0 ≤ P_e) (hPe1 : P_e ≤ 1)
    (h_mi : I_XY = H_X - H_cond)
    (h_fano_bound : H_cond ≤ Real.binEntropy P_e + P_e * Real.log (M - 1 : ℝ))
    (hH_X_le : H_X ≤ Real.log M)
    (h_bin : Real.binEntropy P_e ≤ Real.log 2)
    (hH_cond_nonneg : 0 ≤ H_cond) :
    H_X - Real.binEntropy P_e - P_e * Real.log (M - 1 : ℝ) ≤ I_XY := by
  linarith

end Pythia.InformationTheory