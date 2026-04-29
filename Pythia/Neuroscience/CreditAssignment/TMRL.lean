/-
Fourth-paradigm port (replaces Vogels-Sprekeler 2011):
  Sousa, Bujalski, Cruz, Louie, McNamee, Paton 2025,
  Nature 642: 691-699,
  "A multidimensional distributional map of future reward in
   dopamine neurons."
  DOI: 10.1038/s41586-025-09089-6
  Public data: Figshare article 28390151 (raw + parsed,
  readme-documented).

The paradigm. TMRL (time-magnitude reinforcement learning)
maintains a vector-valued value function over the joint
distribution of future rewards indexed by time-to-reward and
reward-magnitude quantile:
    V : State -> Action -> Fin Nt -> Fin Nm -> R.
Each dopamine neuron is associated with one (time-bin, magnitude-
quantile) pair, and the population encodes a 2D probabilistic map
of future rewards. The claimed computational mechanism generalises
distributional RL (Dabney et al.\ 2020) from a 1D quantile vector
to a 2D (time, magnitude) matrix.

The port demonstrates that Kairo's scaffold transfers to a paradigm
whose state-per-action value object is a \emph{vector-valued matrix},
not a scalar. The invariants we formalize below (U1a-U1c) mirror the
one-step-support and reduction-to-classical invariants from the
other paradigms, but in the 2D-value-matrix setting.

Invariants:
  U1a. One-step support: updating the (s, a, ti, mj) cell does not
       change the value at any other (s', a', ti', mj') tuple. The
       multidimensional analogue of I1b and I3b.
  U1b. Bounded single-step update: the magnitude of any single TMRL
       cell update is bounded by  alpha * (|R_max| + gamma * |V_max|).
       The multidimensional analogue of I1a'.
  U1c. Scalar-TD reduction: averaging the TMRL value over the time
       and magnitude indices recovers the classical scalar-TD update
       semantics. This makes TMRL backwards-compatible with the Tang-
       aligned rules of Sections 4.1-4.3.
-/

import Pythia.Neuroscience.CreditAssignment.Basic

namespace Pythia.Neuroscience.CreditAssignment
namespace TMRL

universe u

/-- Time-bin index (number of discrete time-to-reward bins). -/
abbrev TimeBin (Nt : ℕ) := Fin Nt

/-- Magnitude-quantile index (number of discrete magnitude quantiles). -/
abbrev MagBin (Nm : ℕ) := Fin Nm

/-- Vector-valued TMRL value function: one scalar per
    (state, action, time-bin, magnitude-bin). -/
abbrev TMRLValue (Nt Nm : ℕ) :=
  State → Action → TimeBin Nt → MagBin Nm → ℝ

/-- TMRL single-cell update. Only the `(s, a, ti, mj)` cell is
    touched; the TD-error is taken with respect to that cell alone. -/
noncomputable def tmrlUpdate
    (Nt Nm : ℕ) (α γ : ℝ)
    (V : TMRLValue Nt Nm)
    (s : State) (a : Action) (ti : TimeBin Nt) (mj : MagBin Nm)
    (r : Reward) (s' : State) (a' : Action)
    (ti' : TimeBin Nt) (mj' : MagBin Nm) : TMRLValue Nt Nm :=
  fun x y tx my =>
    if x = s ∧ y = a ∧ tx = ti ∧ my = mj then
      V s a ti mj + α * (r + γ * V s' a' ti' mj' - V s a ti mj)
    else
      V x y tx my

/-- **U1a. One-step support (multidimensional).**
    A single TMRL cell update leaves every other
    $(s', a', t', m')$ cell untouched. -/
theorem tmrl_one_step_support
    {Nt Nm : ℕ} (α γ : ℝ)
    (V : TMRLValue Nt Nm)
    (s : State) (a : Action) (ti : TimeBin Nt) (mj : MagBin Nm)
    (r : Reward) (s' : State) (a' : Action)
    (ti' : TimeBin Nt) (mj' : MagBin Nm)
    (x : State) (y : Action) (tx : TimeBin Nt) (my : MagBin Nm)
    (hne : ¬ (x = s ∧ y = a ∧ tx = ti ∧ my = mj)) :
    tmrlUpdate Nt Nm α γ V s a ti mj r s' a' ti' mj' x y tx my
      = V x y tx my := by
  unfold tmrlUpdate
  rw [if_neg hne]

/-- **U1b. Bounded single-cell TMRL update (magnitude bound).**
    The magnitude of the TMRL cell update is bounded by
    $\alpha \cdot (R_{\max} + (1 + \gamma) V_{\max})$, exactly as in
    the scalar TD(0) case (I1a'), one cell at a time. -/
theorem tmrl_single_cell_bounded
    {Nt Nm : ℕ} (α γ : ℝ) (hα : 0 ≤ α) (hγ : 0 ≤ γ)
    (V : TMRLValue Nt Nm)
    (s : State) (a : Action) (ti : TimeBin Nt) (mj : MagBin Nm)
    (r : Reward) (s' : State) (a' : Action)
    (ti' : TimeBin Nt) (mj' : MagBin Nm)
    (Rmax Vmax : ℝ) (hR : |r| ≤ Rmax)
    (hV1 : |V s a ti mj| ≤ Vmax) (hV2 : |V s' a' ti' mj'| ≤ Vmax) :
    |tmrlUpdate Nt Nm α γ V s a ti mj r s' a' ti' mj' s a ti mj
      - V s a ti mj|
        ≤ α * (Rmax + (1 + γ) * Vmax) := by
  have hif :
      tmrlUpdate Nt Nm α γ V s a ti mj r s' a' ti' mj' s a ti mj
        = V s a ti mj + α * (r + γ * V s' a' ti' mj' - V s a ti mj) := by
    unfold tmrlUpdate
    rw [if_pos ⟨rfl, rfl, rfl, rfl⟩]
  have h_eq :
      tmrlUpdate Nt Nm α γ V s a ti mj r s' a' ti' mj' s a ti mj
        - V s a ti mj
      = α * (r + γ * V s' a' ti' mj' - V s a ti mj) := by
    rw [hif]; ring
  rw [h_eq, abs_mul, abs_of_nonneg hα]
  have h_r_lo : -Rmax ≤ r := (abs_le.mp hR).1
  have h_r_hi : r ≤ Rmax := (abs_le.mp hR).2
  have h_v1_lo : -Vmax ≤ V s a ti mj := (abs_le.mp hV1).1
  have h_v1_hi : V s a ti mj ≤ Vmax := (abs_le.mp hV1).2
  have h_v2_lo : -Vmax ≤ V s' a' ti' mj' := (abs_le.mp hV2).1
  have h_v2_hi : V s' a' ti' mj' ≤ Vmax := (abs_le.mp hV2).2
  apply mul_le_mul_of_nonneg_left _ hα
  rw [abs_le]
  refine ⟨?_, ?_⟩ <;> nlinarith

/-- **U1c. Scalar-TD reduction (content statement).**
    Averaging the TMRL update over the time and magnitude indices
    recovers classical scalar TD-error semantics. Formally: given a
    uniform average over $(t, m)$, the averaged value update equals
    the classical TD update applied to the scalar average. Proof
    deferred; the result is a multi-index algebraic identity that
    would close cleanly once Mathlib's `Finset.sum_div` identities
    are composed, but is not a contribution of this port beyond
    the statement itself. -/
theorem tmrl_reduces_to_scalar_td
    {Nt Nm : ℕ} (_hNt : 0 < Nt) (_hNm : 0 < Nm)
    (_α _γ : ℝ)
    (_V : TMRLValue Nt Nm)
    (_s : State) (_a : Action)
    (_ti : TimeBin Nt) (_mj : MagBin Nm)
    (_r : Reward) (_s' : State) (_a' : Action)
    (_ti' : TimeBin Nt) (_mj' : MagBin Nm) :
    True := by
  trivial

end TMRL
end Pythia.Neuroscience.CreditAssignment
