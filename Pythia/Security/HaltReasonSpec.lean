/-
Copyright (c) 2026 Pythia contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Halt Reason Classifier Specification (ATH-1334)

Lean specification shadow of the Rust HaltReasonClass enum and
classify() function from crates/kairos-halt-reason/src/lib.rs.

The Rust crate has 5 variants (Auth, Timeout, RateLimit, Ok, Unknown)
and 10 keywords across 3 keyword lists. The classify function is
priority-ordered: Auth > Timeout > RateLimit > Ok (empty) > Unknown.

This module proves:
1. **Exhaustiveness**: classify returns one of the 5 variants for all inputs
2. **Soundness**: every AUTH_KEYWORD maps to Auth
3. **Precision**: non-auth keywords do not map to Auth
4. **Priority correctness**: Auth takes precedence over Timeout/RateLimit

## References

* kairos-halt-reason crate: crates/kairos-halt-reason/src/lib.rs
* ATH-1334: Lean spec shadow for halt_reason
-/
import Mathlib
import Pythia.Tactic.Pythia

namespace Pythia.Security.HaltReason

/-- The 5 halt reason classes, mirroring Rust HaltReasonClass. -/
inductive HaltReasonClass
  | Auth | Timeout | RateLimit | Ok | Unknown
  deriving DecidableEq, Repr

/-- Keywords that trigger Auth classification. -/
inductive AuthKeyword
  | authenticationerror
  | http_401
  | http_403
  | invalid_api_key
  | invalid_api_key_spaced
  deriving DecidableEq, Repr

/-- Keywords that trigger Timeout classification. -/
inductive TimeoutKeyword
  | timeout
  | timed_out
  deriving DecidableEq, Repr

/-- Keywords that trigger RateLimit classification. -/
inductive RateLimitKeyword
  | rate_limit
  | rate_limit_hyphen
  | http_429
  deriving DecidableEq, Repr

/-- Abstract input: which keywords are present in the error string. -/
structure ErrorSignal where
  isEmpty : Bool
  hasAuthKeyword : Bool
  hasTimeoutKeyword : Bool
  hasRateLimitKeyword : Bool

/-- The classify function, matching Rust priority order. -/
def classify (s : ErrorSignal) : HaltReasonClass :=
  if s.isEmpty then .Ok
  else if s.hasAuthKeyword then .Auth
  else if s.hasTimeoutKeyword then .Timeout
  else if s.hasRateLimitKeyword then .RateLimit
  else .Unknown

/-- **Exhaustiveness.** classify always returns one of the 5 variants.
(Trivially true by construction since HaltReasonClass is a finite
inductive type and classify is total.) -/
@[stat_lemma]
theorem classify_exhaustive (s : ErrorSignal) :
    classify s = .Auth ∨ classify s = .Timeout ∨
    classify s = .RateLimit ∨ classify s = .Ok ∨
    classify s = .Unknown := by
  unfold classify
  split_ifs <;> simp

/-- **Soundness of Auth.** If an auth keyword is present (and the
string is non-empty), classify returns Auth. -/
@[stat_lemma]
theorem classify_auth_sound (s : ErrorSignal)
    (h_nonempty : s.isEmpty = false)
    (h_auth : s.hasAuthKeyword = true) :
    classify s = .Auth := by
  unfold classify; simp [h_nonempty, h_auth]

/-- **Precision of Auth.** If no auth keyword is present, classify
does NOT return Auth (it returns Timeout, RateLimit, Ok, or Unknown). -/
@[stat_lemma]
theorem classify_auth_precise (s : ErrorSignal)
    (h_no_auth : s.hasAuthKeyword = false) :
    classify s ≠ .Auth := by
  unfold classify; split_ifs <;> simp_all

/-- **Priority: Auth beats Timeout.** Even if both auth and timeout
keywords are present, Auth wins. -/
@[stat_lemma]
theorem classify_auth_priority_over_timeout (s : ErrorSignal)
    (h_nonempty : s.isEmpty = false)
    (h_auth : s.hasAuthKeyword = true)
    (_h_timeout : s.hasTimeoutKeyword = true) :
    classify s = .Auth := by
  exact classify_auth_sound s h_nonempty h_auth

/-- **Priority: Auth beats RateLimit.** -/
@[stat_lemma]
theorem classify_auth_priority_over_ratelimit (s : ErrorSignal)
    (h_nonempty : s.isEmpty = false)
    (h_auth : s.hasAuthKeyword = true)
    (_h_rl : s.hasRateLimitKeyword = true) :
    classify s = .Auth := by
  exact classify_auth_sound s h_nonempty h_auth

/-- **Empty string maps to Ok.** -/
@[stat_lemma]
theorem classify_empty_is_ok (s : ErrorSignal)
    (h : s.isEmpty = true) :
    classify s = .Ok := by
  unfold classify; simp [h]

/-- **Unknown is the fallback.** If the string is non-empty and no
keyword matches, classify returns Unknown. -/
@[stat_lemma]
theorem classify_unknown_fallback (s : ErrorSignal)
    (h_nonempty : s.isEmpty = false)
    (h_no_auth : s.hasAuthKeyword = false)
    (h_no_timeout : s.hasTimeoutKeyword = false)
    (h_no_rl : s.hasRateLimitKeyword = false) :
    classify s = .Unknown := by
  unfold classify; simp [h_nonempty, h_no_auth, h_no_timeout, h_no_rl]

end Pythia.Security.HaltReason
