/-
Eligibility-trace definitions + the algebraic invariants that apply to any
rule using traces (R2 TD(λ), R4 SARSA(λ), R5 actor-critic).

Key targets for the fleet to prove (invariants from spec/invariants.md):

  * `trace_formula` : e_t(s) = ∑_{k=0}^t (γλ)^{t-k} · [s_k = s]
  * `trace_bound`   : γλ < 1 → ‖e_t‖∞ ≤ 1 / (1 - γλ)
  * `trace_diverges`: γλ = 1 + self-loop → e_t → ∞
  * `credit_window_tau` : τ_c(γ, λ, Δt) = -Δt / log(γ λ)
-/

import Pythia.Neuroscience.CreditAssignment.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.Normed.Order.Lattice
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Pow.Real

namespace Pythia.Neuroscience.CreditAssignment

namespace EligibilityTrace

/-- Accumulating eligibility trace update:
    `e_t(s) = γλ · e_{t-1}(s) + 𝟙[s = s_t]`. -/
noncomputable def traceUpdate
    (γ : ℝ) (lam : ℝ) (prevTrace : State → ℝ) (currentState : State) :
    State → ℝ :=
  fun s => γ * lam * prevTrace s + (if s = currentState then 1 else 0)

/-- Iterated eligibility trace from an initial zero trace. -/
noncomputable def trace
    (γ : ℝ) (lam : ℝ) (τ : Trajectory) : ℕ → (State → ℝ)
  | 0     => fun _ => 0
  | t + 1 => traceUpdate γ lam (trace γ lam τ t) (τ.states t)

/-- Closed-form eligibility trace as a sum of decayed indicators.
    Target: **I2b / I4b** from spec/invariants.md. -/
theorem trace_formula
    (γ lam : ℝ) (τ : Trajectory) (t : ℕ) (s : State) :
    trace γ lam τ t s
      = ∑ k ∈ Finset.range t, (γ * lam) ^ (t - 1 - k) *
          (if τ.states k = s then 1 else 0) := by
  induction t with
  | zero => simp [trace]
  | succ n ih =>
    rw [trace, traceUpdate, ih, Finset.mul_sum, Finset.sum_range_succ]
    -- Goal:
    --   ∑ k ∈ range n, γ*lam * ((γ*lam)^(n-1-k) * [τ.states k = s])
    --     + (if s = τ.states n then 1 else 0)
    -- = ∑ k ∈ range n, (γ*lam)^(n+1-1-k) * [τ.states k = s]
    --     + (γ*lam)^(n+1-1-n) * [τ.states n = s]
    congr 1
    · apply Finset.sum_congr rfl
      intro k hk
      rw [Finset.mem_range] at hk
      have hexp : n + 1 - 1 - k = 1 + (n - 1 - k) := by omega
      rw [hexp, pow_add, pow_one]
      ring
    · have hexp : n + 1 - 1 - n = 0 := by omega
      rw [hexp, pow_zero, one_mul]
      by_cases h : s = τ.states n
      · rw [if_pos h, if_pos h.symm]
      · rw [if_neg h, if_neg (fun heq => h heq.symm)]

/-- Eligibility trace is bounded when `γλ < 1`.
    Target: **I2c / I4c**. -/
theorem trace_bound
    (γ lam : ℝ) (hgl_nn : 0 ≤ γ * lam) (hgl_lt : γ * lam < 1)
    (τ : Trajectory) (t : ℕ) (s : State) :
    trace γ lam τ t s ≤ 1 / (1 - γ * lam) := by
  -- Direct induction on t. At t=0 the trace is 0 ≤ 1/(1-γλ) (positive).
  -- At t+1: trace ≤ γλ · 1/(1-γλ) + 1 = (γλ + 1 - γλ)/(1-γλ) = 1/(1-γλ).
  have h1_gl_pos : 0 < 1 - γ * lam := by linarith
  have hinv_pos : 0 < 1 / (1 - γ * lam) := by positivity
  induction t with
  | zero => simp [trace]; linarith
  | succ n ih =>
    simp only [trace, traceUpdate]
    -- Goal: γ * lam * trace ... + (if _ then 1 else 0) ≤ 1/(1-γλ)
    have h_ind : γ * lam * trace γ lam τ n s ≤ γ * lam * (1 / (1 - γ * lam)) :=
      mul_le_mul_of_nonneg_left ih hgl_nn
    have h_ind' : γ * lam * trace γ lam τ n s
                ≤ γ * lam / (1 - γ * lam) := by
      have := h_ind
      rw [mul_one_div] at this
      exact this
    have h_if : (if s = τ.states n then (1 : ℝ) else 0) ≤ 1 := by
      split_ifs <;> simp
    calc γ * lam * trace γ lam τ n s + (if s = τ.states n then (1 : ℝ) else 0)
        ≤ γ * lam / (1 - γ * lam) + 1 := by linarith
      _ = (γ * lam + (1 - γ * lam)) / (1 - γ * lam) := by
          field_simp
      _ = 1 / (1 - γ * lam) := by ring

/-- Eligibility trace diverges for a self-loop when `γ λ = 1`.
    Target: **I2d / I4d**. -/
theorem trace_diverges_at_boundary
    (γ lam : ℝ) (hgl : γ * lam = 1) (s₀ : State)
    (τ : Trajectory) (hSelfLoop : ∀ t, τ.states t = s₀) :
    Filter.Tendsto (fun t => trace γ lam τ t s₀) Filter.atTop Filter.atTop := by
  rw [Filter.tendsto_atTop_atTop]
  intro b
  -- For the self-loop with γ*lam = 1, trace γ lam τ t s₀ = t
  -- We show this by using trace_formula
  suffices key : ∀ t, trace γ lam τ t s₀ = ↑t by
    obtain ⟨n, hn⟩ := exists_nat_gt b
    exact ⟨n, fun m hm => by rw [key m]; exact le_trans (le_of_lt hn) (by exact_mod_cast hm)⟩
  intro t
  induction t with
  | zero => simp [trace]
  | succ n ih =>
    simp only [trace, traceUpdate]
    rw [hSelfLoop n, if_pos rfl, ih, hgl]
    push_cast
    ring

/-- Characteristic time τ_c of the eligibility trace.
    Target: **I2e / I4e**. -/
noncomputable def creditWindowTau (γ lam Δt : ℝ) : ℝ :=
  -Δt / Real.log (γ * lam)

theorem credit_window_is_one_over_e_decay
    (γ lam Δt : ℝ) (hgl_pos : 0 < γ * lam) (hgl_lt : γ * lam < 1)
    (hΔt : 0 < Δt) :
    Real.rpow (γ * lam) (creditWindowTau γ lam Δt / Δt) = Real.exp (-1) := by
  -- (γλ)^(τ_c/Δt) = exp(log(γλ) * τ_c/Δt), and τ_c = -Δt/log(γλ), so
  -- the exponent reduces to -1 (log(γλ) ≠ 0 since γλ ∈ (0, 1)).
  have hlog_lt : Real.log (γ * lam) < 0 := Real.log_neg hgl_pos hgl_lt
  have hlog_ne : Real.log (γ * lam) ≠ 0 := ne_of_lt hlog_lt
  have hΔt_ne : Δt ≠ 0 := ne_of_gt hΔt
  have hexp : Real.log (γ * lam) * (creditWindowTau γ lam Δt / Δt) = -1 := by
    unfold creditWindowTau
    field_simp
  calc Real.rpow (γ * lam) (creditWindowTau γ lam Δt / Δt)
      = Real.exp (Real.log (γ * lam) * (creditWindowTau γ lam Δt / Δt)) :=
        Real.rpow_def_of_pos hgl_pos _
    _ = Real.exp (-1) := by rw [hexp]

end EligibilityTrace

end Pythia.Neuroscience.CreditAssignment
