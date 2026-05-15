/-
Copyright (c) 2026 Pythia contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Cedar env_allowlist Policy Specification (Lean shadow)

Lean specification shadow of the Cedar env_allowlist authorization
policies from kairos (src/kairos/security/cedar/env_allowlist.cedar).

This module encodes the tool/env-var domain as finite inductive types,
the Cedar policy set as a decidable authorization function, and
proves two security properties:

1. **Non-contradiction**: no (Tool, EnvVar) pair is both permitted
   and forbidden (trivial since all policies are PERMIT).
2. **Isolation**: sensitive env vars (API keys, service role keys)
   are NOT forwarded to hardware/formal-methods tools.

The isolation property is the customer-facing security guarantee:
"ANTHROPIC_API_KEY never reaches yosys/ebmc/verilator."

## References

* Cedar policy language: https://www.cedarpolicy.com/
* kairos env_allowlist: src/kairos/security/cedar/env_allowlist.cedar
-/
import Mathlib
import Pythia.Tactic.Pythia

namespace Pythia.Security.EnvAllowlist

/-- Tools that kairos can dispatch to. -/
inductive Tool
  | yosys | ebmc | lean | lake | acl2 | verilator | cedar | claude_subagent
  deriving DecidableEq, Repr

/-- Environment variable groups (Cedar entity groups). -/
inductive EnvVarGroup
  | baseline | lean_extra | docker_transport | claude_subagent_extra
  deriving DecidableEq, Repr

/-- Sensitive environment variables that must not leak to
hardware/formal-methods tools. -/
inductive SensitiveVar
  | ANTHROPIC_API_KEY
  | ANTHROPIC_BASE_URL
  | ANTHROPIC_AUTH_TOKEN
  | AWS_ACCESS_KEY_ID
  | AWS_SECRET_ACCESS_KEY
  | AWS_SESSION_TOKEN
  | SUPABASE_SERVICE_ROLE_KEY
  | OPENAI_API_KEY
  | ATHANOR_SYNC_TOKEN
  deriving DecidableEq, Repr

/-- Hardware/formal-methods tools that must never see sensitive vars. -/
def isHardwareTool : Tool → Bool
  | .yosys => true
  | .ebmc => true
  | .verilator => true
  | .acl2 => true
  | _ => false

/-- A sensitive var is in the claude_subagent_extra group (or ungrouped). -/
def sensitiveVarInSubagentGroup : SensitiveVar → Bool
  | .ANTHROPIC_API_KEY => true
  | .ANTHROPIC_BASE_URL => true
  | .ANTHROPIC_AUTH_TOKEN => true
  | .AWS_ACCESS_KEY_ID => true
  | .AWS_SECRET_ACCESS_KEY => true
  | .AWS_SESSION_TOKEN => true
  | _ => false

/-- The Cedar authorization decision for (tool, sensitive_var).
Models the 7 PERMIT policies from env_allowlist.cedar.
A tool gets a sensitive var only if:
- the var is in the baseline group (none of the sensitive vars are), OR
- the tool has a specific policy granting access to the var's group. -/
def isPermitted (t : Tool) (v : SensitiveVar) : Bool :=
  match t, v with
  | .claude_subagent, sv => sensitiveVarInSubagentGroup sv
  | _, _ => false

/-- **Isolation theorem.** No hardware tool is permitted access to
any sensitive variable. This is the core security property. -/
@[stat_lemma]
theorem hardware_tool_isolation (t : Tool) (v : SensitiveVar)
    (ht : isHardwareTool t = true) :
    isPermitted t v = false := by
  cases t <;> simp_all [isHardwareTool, isPermitted]

/-- **Non-contradiction.** Since all policies are PERMIT (no FORBID),
and our model returns Bool (not a permit/forbid pair), contradiction
is impossible by construction. This theorem witnesses that the
authorization function is total and deterministic. -/
@[stat_lemma]
theorem authorization_deterministic (t : Tool) (v : SensitiveVar) :
    isPermitted t v = true ∨ isPermitted t v = false := by
  cases isPermitted t v <;> simp

/-- **Only claude_subagent gets API keys.** -/
@[stat_lemma]
theorem only_subagent_gets_api_key (t : Tool)
    (ht : t ≠ Tool.claude_subagent) :
    isPermitted t .ANTHROPIC_API_KEY = false := by
  cases t <;> simp_all [isPermitted]

/-- **Only claude_subagent gets AWS credentials.** -/
@[stat_lemma]
theorem only_subagent_gets_aws_key (t : Tool)
    (ht : t ≠ Tool.claude_subagent) :
    isPermitted t .AWS_ACCESS_KEY_ID = false := by
  cases t <;> simp_all [isPermitted]

/-- **Supabase service role key is never forwarded to any tool.** -/
@[stat_lemma]
theorem supabase_key_never_forwarded (t : Tool) :
    isPermitted t .SUPABASE_SERVICE_ROLE_KEY = false := by
  cases t <;> simp [isPermitted, sensitiveVarInSubagentGroup]

/-- **OpenAI key is never forwarded to any tool.** -/
@[stat_lemma]
theorem openai_key_never_forwarded (t : Tool) :
    isPermitted t .OPENAI_API_KEY = false := by
  cases t <;> simp [isPermitted, sensitiveVarInSubagentGroup]

/-- **Athanor sync token is never forwarded to any tool.** -/
@[stat_lemma]
theorem sync_token_never_forwarded (t : Tool) :
    isPermitted t .ATHANOR_SYNC_TOKEN = false := by
  cases t <;> simp [isPermitted, sensitiveVarInSubagentGroup]

end Pythia.Security.EnvAllowlist
