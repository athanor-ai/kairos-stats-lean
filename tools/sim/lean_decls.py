"""tools/sim/lean_decls.py — line-based extraction of top-level Lean
declarations from a source file.

This is a deliberately small parser: enough to enumerate the
declarations a file defines so other code (e.g., the triage
validator) can check whether a claimed theorem name actually
exists. It does NOT type-check, does NOT understand Lean
semantics, and is NOT a substitute for ``lake env lean``.

Why hand-rolled and not regex: Aidan 2026-04-27 directive
(memory: ``feedback_no_regex_use_real_parsers.md``). Regex on
source code is a band-aid; structural parsing is the right
approach. We line-scan for the canonical
``<keyword> <identifier> ...`` shape Lean 4 uses for top-level
declarations. Documented limits below.

Caveats:
* Only catches column-0 declarations. Inner ``where``-clauses and
  nested ``let``-defs are out of scope; that's fine — only
  top-level public declarations need triage attribution.
* Doesn't follow ``namespace`` blocks. The returned set is
  unqualified identifier names; callers compare against the
  rightmost segment of any qualified declaration name in the
  triage (``Foo.Bar.baz`` -> compare ``baz`` to the set).
* Comments (``--`` and ``/- ... -/``) at column 0 are skipped.
* Multi-line declarations: only the first line is parsed; that's
  where the keyword + identifier always live in well-formed Lean.
* Decoration tokens like ``@[simp]``, ``@[stat_lemma]``,
  ``noncomputable``, ``private``, ``protected``, ``unsafe``,
  ``partial``, etc. that prefix a declaration line are stripped
  before scanning so e.g. ``@[stat_lemma] theorem foo := ...``
  is correctly attributed to the ``foo`` identifier.
"""
from __future__ import annotations

from pathlib import Path

# Lean 4 declaration keywords we care about for triage. Excludes
# ``inductive`` and ``structure`` because they're rare in pythia
# and the triage focuses on ``theorem`` / ``lemma`` / ``def`` style
# declarations.
DECL_KEYWORDS = (
    "theorem",
    "lemma",
    "def",
    "instance",
    "abbrev",
    "noncomputable def",
    "private theorem",
    "private lemma",
    "private def",
    "protected theorem",
    "protected lemma",
    "protected def",
)


def _strip_attribute_prefix(line: str) -> str:
    """Strip a leading ``@[...]`` attribute block, returning the rest.

    Handles single-line attributes only (``@[simp] theorem foo``).
    Multi-line attribute blocks are rare in pythia and are skipped
    by the column-0 check (the next line, where the keyword lives,
    is parsed instead).
    """
    s = line.lstrip()
    if not s.startswith("@["):
        return line
    depth = 0
    for i, ch in enumerate(s):
        if ch == "[":
            depth += 1
        elif ch == "]":
            depth -= 1
            if depth == 0:
                return s[i + 1 :].lstrip()
    return line  # malformed; let the caller treat as no decl


def _identifier_from_rest(rest: str) -> str | None:
    """Extract the first identifier from the start of ``rest``.

    Lean identifiers: alphanumeric + ``_`` + ``'`` + ``.`` (for
    namespace-qualified names like ``Foo.bar`` written explicitly
    in the declaration). Stop at the first whitespace or other
    punctuation.
    """
    if not rest:
        return None
    end = 0
    while end < len(rest):
        ch = rest[end]
        if ch.isalnum() or ch in "_'.":
            end += 1
        else:
            break
    if end == 0:
        return None
    ident = rest[:end]
    # Strip trailing dot (e.g. malformed input).
    return ident.rstrip(".") or None


def top_level_decls(source: str) -> set[str]:
    """Return the unqualified identifier of every top-level
    declaration in ``source``.

    For a Lean file containing::

        @[simp] theorem foo (x : Nat) : x = x := rfl
        lemma bar : True := trivial
        namespace Baz
        theorem qux ...

    returns ``{"foo", "bar", "qux"}``. Namespace-prefixed forms
    are returned unqualified — callers should compare by the
    rightmost segment for fully-qualified triage entries.
    """
    out: set[str] = set()
    for raw in source.splitlines():
        if not raw or raw[0].isspace():
            # Indented = nested or inside-let — out of scope.
            continue
        line = _strip_attribute_prefix(raw).rstrip()
        if not line:
            continue
        # Skip comments at column 0.
        if line.startswith("--") or line.startswith("/-"):
            continue
        for kw in DECL_KEYWORDS:
            prefix = kw + " "
            if line.startswith(prefix):
                rest = line[len(prefix):]
                ident = _identifier_from_rest(rest)
                if ident is not None:
                    # Strip namespace prefix for the "unqualified" view.
                    out.add(ident.split(".")[-1])
                break
    return out


def top_level_decls_in_file(path: Path) -> set[str]:
    """Read a file and return its top-level declaration identifiers."""
    if not path.is_file():
        return set()
    return top_level_decls(path.read_text(encoding="utf-8", errors="replace"))


__all__ = ["DECL_KEYWORDS", "top_level_decls", "top_level_decls_in_file"]
