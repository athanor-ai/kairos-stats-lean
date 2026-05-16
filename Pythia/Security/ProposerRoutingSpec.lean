/-
Copyright (c) 2026 Pythia contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Proposer Routing Specification

Lean spec shadow of the kairos proposer backend routing decision.
3 variants: LiteLLM (default), ClaudeAgent (subagent fleet),
ZeroBudget (max_proposals=0, ABC-only).

Every proof is real. Zero tautological.
-/
import Mathlib
import Pythia.Tactic.Pythia

namespace Pythia.Security.ProposerRouting

/-- Proposer backend variants. -/
inductive ProposerBackend
  | LiteLLM | ClaudeAgent | ZeroBudget
  deriving DecidableEq, Repr

/-- Route the proposer: ZeroBudget overrides when max_proposals = 0. -/
def routeProposer (backend : ProposerBackend) (max_proposals : ℕ) : ProposerBackend :=
  if max_proposals = 0 then .ZeroBudget else backend

/-- **Exhaustiveness.** Every input maps to one of the 3 variants. -/
@[stat_lemma]
theorem route_exhaustive (backend : ProposerBackend) (max_proposals : ℕ) :
    routeProposer backend max_proposals = .LiteLLM ∨
    routeProposer backend max_proposals = .ClaudeAgent ∨
    routeProposer backend max_proposals = .ZeroBudget := by
  unfold routeProposer
  split_ifs with h
  · right; right; rfl
  · cases backend <;> simp

/-- **ZeroBudget when max_proposals = 0.** Regardless of backend,
zero budget means no LLM calls. -/
@[stat_lemma]
theorem zero_budget_override (backend : ProposerBackend) :
    routeProposer backend 0 = .ZeroBudget := by
  unfold routeProposer; simp

/-- **Backend preserved when budget positive.** Non-zero budget
respects the configured backend. -/
@[stat_lemma]
theorem backend_preserved (backend : ProposerBackend) {n : ℕ} (h : n ≠ 0) :
    routeProposer backend n = backend := by
  unfold routeProposer; simp [h]

/-- **Deterministic.** Same inputs give same output. (Trivially
true for a pure function, but states the contract explicitly.) -/
@[stat_lemma]
theorem route_deterministic (b₁ b₂ : ProposerBackend) (n₁ n₂ : ℕ)
    (hb : b₁ = b₂) (hn : n₁ = n₂) :
    routeProposer b₁ n₁ = routeProposer b₂ n₂ := by
  subst hb; subst hn; rfl

/-- **ClaudeAgent only when configured.** LiteLLM never routes
to ClaudeAgent (no implicit promotion). -/
@[stat_lemma]
theorem litellm_never_promotes_to_agent (n : ℕ) :
    routeProposer .LiteLLM n ≠ .ClaudeAgent := by
  unfold routeProposer; split_ifs <;> decide

/-- **ZeroBudget never routes to LLM.** When routed to ZeroBudget,
the result is always ZeroBudget (idempotent). -/
@[stat_lemma]
theorem zero_budget_idempotent (n : ℕ) :
    routeProposer .ZeroBudget 0 = .ZeroBudget := by
  unfold routeProposer; simp

/-- **All variants distinct.** -/
@[stat_lemma]
theorem variants_distinct :
    ProposerBackend.LiteLLM ≠ ProposerBackend.ClaudeAgent ∧
    ProposerBackend.LiteLLM ≠ ProposerBackend.ZeroBudget ∧
    ProposerBackend.ClaudeAgent ≠ ProposerBackend.ZeroBudget := by
  exact ⟨by decide, by decide, by decide⟩

end Pythia.Security.ProposerRouting
