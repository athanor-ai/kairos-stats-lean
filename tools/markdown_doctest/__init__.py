"""Markdown doctest harness for Pythia.

Walks `*.md` files via markdown-it-py's structured AST (no regex on
the markdown source), extracts every fenced code block tagged
``lean`` or ``lean4``, and runs each through ``lake env lean`` to
verify it actually compiles. The harness is the customer-facing
backstop on top of the in-repo `examples/**/*.lean` CI gate (B1):
this one catches drift in README + tutorial + cookbook prose where
broken snippets were silently shipping for weeks before B1 landed.

## Skip markers

A code block is skipped when an HTML comment immediately precedes
the fence with one of these forms:

  <!-- doctest: skip -->
  <!-- doctest: skip-reason: <free-text reason> -->
  <!-- doctest: lakefile -->          (lakefile snippet, not a Lean module)
  <!-- doctest: cmd-only -->          (`#stat_lemmas` etc, needs interactive env)

"Immediately precedes" means: the marker is the last non-blank
non-paragraph element before the code fence. The harness uses the
markdown AST's source-line offsets to determine adjacency, NOT
regex on the raw text.

## Compilation contract

Each non-skipped block is written to a temp file under the project
root and run through ``lake env lean <tempfile>``. Exit 0 with no
``error:`` lines on stderr = pass. Anything else = fail, with the
full lake output surfaced in the pytest failure for actionability.

The block is compiled VERBATIM — no auto-prepended imports. Authors
who want a snippet to compile must either:

  1. Include the imports inside the snippet (recommended for
     standalone reference), or
  2. Mark it skip with a doctest marker (for derivative snippets
     like "and now this part" continuation samples).

This is intentional: hidden-import doctests pass when the project is
configured one way and fail when a customer copy-pastes them into a
fresh project. Explicit imports up front means the snippet is
copy-paste runnable, which is the whole point of having one.
"""
from .extract import CodeBlock, extract_blocks
from .runner import RunResult, run_block

__all__ = ["CodeBlock", "RunResult", "extract_blocks", "run_block"]
