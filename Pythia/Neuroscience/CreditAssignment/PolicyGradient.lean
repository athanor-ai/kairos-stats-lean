/-
Pythia.Neuroscience.CreditAssignment.PolicyGradient -- baseline
invariance for the policy-gradient estimator.

Reference: Sutton, R. & Barto, A. (2018). "Reinforcement Learning:
An Introduction." MIT Press, Section 13.2 (Policy Gradient Theorem).

The policy-gradient estimator can be expressed equivalently using
the action-value Q(s,a) or the advantage A(s,a) = Q(s,a) - V(s).
The two forms are equal because the baseline-dependent residual
V(s) * sum_a pi(s,a) * psi(s,a) vanishes by the score identity
sum_a pi(s,a) * psi(s,a) = 0. Variance reduction in practice uses
the advantage form because A has lower expected magnitude than Q.

Closed by Aristotle (project 4edb275a).
-/
import Mathlib
import Pythia.Neuroscience.CreditAssignment.Basic

namespace Pythia.Neuroscience.CreditAssignment

/-- Actor-critic setup carrying a policy `π : S → A → ℝ`, score
function `ψ : S → A → ℝ` (= ∇_θ log π_θ pointwise), action-value
`Q : S → A → ℝ`, and state-value `V : S → ℝ`, related by the
score identity `∑_a π(s,a) · ψ(s,a) = 0`. -/
structure ActorCriticSetup (S : Type*) (A : Type*) [Fintype A] where
  π : S → A → ℝ
  ψ : S → A → ℝ
  Q : S → A → ℝ
  V : S → ℝ
  score_identity : ∀ s, ∑ a : A, π s a * ψ s a = 0

/-- Advantage function: A(s,a) = Q(s,a) - V(s). -/
def ActorCriticSetup.advantage {S A : Type*} [Fintype A]
    (ac : ActorCriticSetup S A) (s : S) (a : A) : ℝ :=
  ac.Q s a - ac.V s

/-- **Policy-gradient advantage form.** The policy-gradient estimator
expressed via Q equals its advantage form ∑ π · ψ · A. The proof
distributes the subtraction in `A = Q - V`, factors out `V(s)`, and
applies the score identity to vanish the baseline term.

This is the algebraic heart of variance reduction in policy-gradient
methods: subtracting a state-dependent baseline from the critic does
not bias the gradient. -/
theorem policy_gradient_advantage_form
    {S A : Type*} [Fintype A] [DecidableEq A]
    (ac : ActorCriticSetup S A) (s : S) :
    ∑ a : A, ac.π s a * ac.ψ s a * ac.Q s a =
    ∑ a : A, ac.π s a * ac.ψ s a * ac.advantage s a := by
  unfold ActorCriticSetup.advantage
  simp +decide [mul_sub, ← Finset.sum_mul, ac.score_identity]

end Pythia.Neuroscience.CreditAssignment
