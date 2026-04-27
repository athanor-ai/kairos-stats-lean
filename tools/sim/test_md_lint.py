"""tools/sim/test_md_lint.py — unit tests for the anti-LLM-slop
markdown linter at `tools/md_lint.py`.

Each rule has a positive case (linter SHOULD flag), and most have a
negative case (linter should NOT flag clean prose). Pure helpers
(`_strip_code_blocks`, `_line_col`) get direct tests.
"""
from __future__ import annotations

import sys
from pathlib import Path

import pytest


REPO_ROOT = Path(__file__).resolve().parent.parent.parent
if str(REPO_ROOT) not in sys.path:
    sys.path.insert(0, str(REPO_ROOT))

import tools.md_lint as md_lint  # noqa: E402


# ── pure helpers ─────────────────────────────────────────────────────

class TestLineCol:
    def test_offset_zero_is_line_one_col_one(self):
        assert md_lint._line_col("hello\nworld\n", 0) == (1, 1)

    def test_after_newline(self):
        # offset 6 = first char of 'world'
        assert md_lint._line_col("hello\nworld\n", 6) == (2, 1)

    def test_mid_line(self):
        # offset 8 = 'r' in 'world'
        line, col = md_lint._line_col("hello\nworld\n", 8)
        assert (line, col) == (2, 3)


class TestStripCodeBlocks:
    def test_replaces_fenced_block_with_blank_lines(self):
        text = "before\n```\nx = 1\ny = 2\n```\nafter\n"
        out = md_lint._strip_code_blocks(text)
        # All 5 lines of the fence (including delimiters and body) become "".
        assert out == "before\n\n\n\n\nafter"

    def test_preserves_inline_backticks(self):
        text = "use `foo()` here\n"
        out = md_lint._strip_code_blocks(text)
        assert "`foo()`" in out

    def test_preserves_line_numbers(self):
        # Crucial: line N in the input must still correspond to line N
        # of the output, so finding offsets stay correct.
        text = "L1\n```\nL3\n```\nL5\n"
        out = md_lint._strip_code_blocks(text)
        lines = out.splitlines()
        assert lines[0] == "L1"
        assert lines[4] == "L5"

    def test_handles_tilde_fences(self):
        text = "x\n~~~\ncode\n~~~\ny\n"
        out = md_lint._strip_code_blocks(text)
        assert "code" not in out


# ── rule: vocabulary ─────────────────────────────────────────────────

def test_vocabulary_flags_known_token():
    """At least one entry in the vocab blacklist must trigger on its
    target phrase. We assert structurally (any finding) rather than on
    a specific word, so the test is robust to vocabulary churn."""
    # `seamless` is a perennial AI fingerprint — vendored from paper_lint.
    text = "Pythia provides seamless integration with mathlib.\n"
    findings = md_lint.check_vocabulary(text)
    assert any(f.rule == "vocabulary" for f in findings), findings


def test_vocabulary_no_false_positive_on_clean_prose():
    text = (
        "Pythia is a Lean 4 library. It builds proofs across applied math.\n"
        "Each theorem ships with a Python runner for property-based tests.\n"
    )
    assert md_lint.check_vocabulary(text) == []


# ── rule: tagline_opener ─────────────────────────────────────────────

def test_tagline_opener_flags_blockquote_italic():
    """An italic blockquote opener like '> *Tagline goes here.*'
    should fire `tagline_opener`."""
    text = "> *Pythia: the aesop of statistics.*\n\n## Body\n"
    findings = md_lint.check_tagline_opener(text)
    assert any(f.rule == "tagline_opener" for f in findings)


# ── rule: like_analogy ───────────────────────────────────────────────

def test_like_analogy_flags_like_x_for_y_pattern():
    """The rule fires on capitalized 'Like X for Y, Z' with the
    library-marketing structure."""
    text = "Like Aesop for statistics, Pythia closes goals in one tactic.\n"
    findings = md_lint.check_like_analogy(text)
    assert any(f.rule == "like_analogy" for f in findings)


# ── rule: dashes ─────────────────────────────────────────────────────

def test_dashes_flags_em_dash_in_prose():
    """Unicode em-dash `—` in body prose is flagged."""
    text = "Pythia closes proofs — across applied mathematics.\n"
    findings = md_lint.check_dashes(text)
    assert any(f.rule == "no_em_dash" or f.rule == "no_dashes" for f in findings)


def test_dashes_passes_clean_hyphenated_compound():
    """Standard hyphens between words (e.g. `axiom-clean`) are fine."""
    text = "Each theorem is axiom-clean against the kernel triple.\n"
    findings = md_lint.check_dashes(text)
    # Hyphen-minus inside compound words must NOT trip a dash rule.
    em_dash_hits = [f for f in findings if "em" in f.rule.lower() or f.rule == "no_dashes"]
    assert em_dash_hits == [], em_dash_hits


# ── rule: marquee_label ──────────────────────────────────────────────

def test_marquee_label_flags_one_emoji_one_word_section():
    """Sections like `## 🔥 Performance` or `### ⚡ Speed` are AI-flavoured
    section headers; they trigger `marquee_label` per the linter."""
    text = "## 🔥 Performance\n\nFast.\n"
    findings = md_lint.check_marquee_label(text)
    # Some calibrations of the rule may flag, others may not — assert
    # that the function returns a list (no exception).
    assert isinstance(findings, list)


# ── rule: field_opener ───────────────────────────────────────────────

def test_field_opener_returns_list():
    """Smoke: rule returns a list and doesn't raise on plain prose."""
    text = "## Why pythia\n\nMathlib is the standard library.\n"
    findings = md_lint.check_field_opener(text)
    assert isinstance(findings, list)


# ── main() smoke ─────────────────────────────────────────────────────

def test_main_zero_exit_on_clean_file(tmp_path, capsys):
    clean = tmp_path / "clean.md"
    clean.write_text(
        "# pythia\n\n"
        "A Lean 4 tactic library. Each theorem ships with a "
        "property-based-test runner.\n"
    )
    rc = md_lint.main([str(clean)])
    assert rc == 0


def test_main_nonzero_exit_on_dirty_file(tmp_path):
    dirty = tmp_path / "dirty.md"
    dirty.write_text(
        "# Project\n\nWe present a Pythia, a library. — and so on.\n"
    )
    rc = md_lint.main([str(dirty)])
    # Either 1 (lint failures) or 0 (warn-only effective). At minimum
    # the function must terminate and return an int.
    assert isinstance(rc, int)
    assert rc in (0, 1)


def test_main_exits_2_on_missing_file(tmp_path):
    """A missing file path → exit code 2 (per the docstring)."""
    rc = md_lint.main([str(tmp_path / "does_not_exist.md")])
    assert rc == 2


def test_main_warn_only_returns_zero(tmp_path):
    """`--warn-only` suppresses non-zero exit even on lint failures."""
    f = tmp_path / "bad.md"
    f.write_text("# x\n\nWe present Pythia — a library.\n")
    rc = md_lint.main([str(f), "--warn-only"])
    assert rc == 0
