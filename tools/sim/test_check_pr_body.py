"""tools/sim/test_check_pr_body.py — unit tests for tools/check_pr_body.py.

Covers the parsing helpers (parse_sections, find_section,
section_is_meaningful, count_checked_boxes), the top-level validate()
function in lenient + strict modes, and the body-loaders (file, stdin,
GitHub event JSON). All tests are pure-Python, offline, stdlib-only —
they run on a stock GitHub `ubuntu-latest` runner without `pip install`.
"""
from __future__ import annotations

import io
import json
import re
import sys
import textwrap
from pathlib import Path

import pytest


REPO_ROOT = Path(__file__).resolve().parent.parent.parent
if str(REPO_ROOT) not in sys.path:
    sys.path.insert(0, str(REPO_ROOT))

import tools.check_pr_body as check_pr_body  # noqa: E402


# ── helpers ──────────────────────────────────────────────────────────


def _valid_body() -> str:
    """A PR body that should pass both lenient and strict checks."""
    return textwrap.dedent(
        """\
        ## Summary

        Adds a new theorem `foo_bar_positivity` under `Pythia/Engineering/`
        plus a Python harness with three caught mutations. Closes a small
        manifest gap from the strategic ask review.

        ## New theorem (Track A: cross-domain quick path)

        - [x] `Pythia/Engineering/FooBar.lean` builds clean
        - [x] harness passes
        - [x] All 3 mutations caught
        - [ ] manifest patched

        ## New theorem (Track B: statistics-spine)

        - [ ] Issue opened first
        - [ ] Statement scaffold

        ## General PR (tactic, tool, docs, infra)

        - [ ] `lake build` green
        - [ ] README updated

        ## Linked issues

        Closes #123
        """
    )


def _template_body() -> str:
    """The verbatim repo template — should FAIL lenient (placeholder)."""
    return (REPO_ROOT / ".github" / "pull_request_template.md").read_text(
        encoding="utf-8"
    )


# ── parse_sections ────────────────────────────────────────────────────


class TestParseSections:
    def test_extracts_h2_titles_in_order(self):
        body = _valid_body()
        sections = check_pr_body.parse_sections(body)
        titles = [s.title for s in sections]
        assert titles[0] == "Summary"
        assert titles[1].startswith("New theorem (Track A")
        assert titles[2].startswith("New theorem (Track B")
        assert titles[3].startswith("General PR")
        assert titles[4] == "Linked issues"

    def test_summary_body_isolated_to_summary_block(self):
        body = _valid_body()
        sections = check_pr_body.parse_sections(body)
        summary = sections[0]
        assert "Adds a new theorem" in summary.body
        # Does NOT bleed into the next section.
        assert "## New theorem" not in summary.body
        assert "Track A" not in summary.body

    def test_drops_preamble_before_first_h2(self):
        body = "<!-- preamble -->\n\nrandom text\n\n## Summary\n\nbody."
        sections = check_pr_body.parse_sections(body)
        assert len(sections) == 1
        assert sections[0].title == "Summary"
        assert sections[0].body == "body."

    def test_handles_empty_input(self):
        assert check_pr_body.parse_sections("") == []

    def test_does_not_match_h1_or_h3(self):
        body = "# Heading 1\n\n### Heading 3\n\n## Real H2\n\nfoo."
        sections = check_pr_body.parse_sections(body)
        assert [s.title for s in sections] == ["Real H2"]


# ── section_is_meaningful ─────────────────────────────────────────────


class TestSectionIsMeaningful:
    def test_real_content_passes(self):
        assert check_pr_body.section_is_meaningful(
            "Adds positivity lemma for engineering domain."
        )

    def test_empty_string_fails(self):
        assert not check_pr_body.section_is_meaningful("")

    def test_pure_whitespace_fails(self):
        assert not check_pr_body.section_is_meaningful("   \n\n\t  \n")

    def test_verbatim_placeholder_fails(self):
        assert not check_pr_body.section_is_meaningful(
            check_pr_body.SUMMARY_PLACEHOLDER
        )

    def test_html_comments_dont_count(self):
        # Even with a comment block, no body content -> fail.
        assert not check_pr_body.section_is_meaningful(
            "<!-- this is just an HTML comment that should be stripped -->"
        )

    def test_short_content_below_threshold_fails(self):
        # 9 non-whitespace chars < 10 threshold.
        assert not check_pr_body.section_is_meaningful("abc def gh")

    def test_threshold_inclusive(self):
        # exactly 10 non-whitespace chars passes.
        assert check_pr_body.section_is_meaningful("abcde fghij")


# ── count_checked_boxes ───────────────────────────────────────────────


class TestCountCheckedBoxes:
    def test_counts_lower_x(self):
        body = "- [x] one\n- [x] two\n- [ ] three"
        assert check_pr_body.count_checked_boxes(body) == 2

    def test_counts_upper_X(self):
        body = "- [X] one\n- [x] two"
        assert check_pr_body.count_checked_boxes(body) == 2

    def test_zero_when_all_unchecked(self):
        body = "- [ ] one\n- [ ] two"
        assert check_pr_body.count_checked_boxes(body) == 0

    def test_ignores_non_task_lines(self):
        body = "regular bullet\n- not a checkbox\n- [x] real one"
        assert check_pr_body.count_checked_boxes(body) == 1


# ── validate (lenient) ────────────────────────────────────────────────


class TestValidateLenient:
    def test_valid_body_passes(self):
        assert check_pr_body.validate(_valid_body(), strict=False) == []

    def test_template_body_fails_summary_placeholder(self):
        errors = check_pr_body.validate(_template_body(), strict=False)
        assert len(errors) == 1
        assert "Summary" in errors[0]
        assert "placeholder" in errors[0]

    def test_missing_summary_section_fails(self):
        body = "## General PR\n\n- [x] real\n"
        errors = check_pr_body.validate(body, strict=False)
        assert any("missing required section `## Summary`" in e for e in errors)

    def test_empty_summary_fails(self):
        body = "## Summary\n\n   \n\n## Linked issues\n"
        errors = check_pr_body.validate(body, strict=False)
        assert any("Summary" in e and "empty" in e for e in errors)

    def test_lenient_ignores_unchecked_checkboxes(self):
        # Real summary content, all checkboxes blank -> still passes.
        body = textwrap.dedent(
            """\
            ## Summary

            Real summary content describing the change in detail here.

            ## General PR

            - [ ] not ticked
            """
        )
        assert check_pr_body.validate(body, strict=False) == []

    def test_lenient_does_not_require_linked_issues(self):
        body = textwrap.dedent(
            """\
            ## Summary

            Real summary content describing the change in detail here.
            """
        )
        assert check_pr_body.validate(body, strict=False) == []


# ── validate (strict) ─────────────────────────────────────────────────


class TestValidateStrict:
    def test_valid_body_passes_strict(self):
        # _valid_body has Track A boxes ticked.
        assert check_pr_body.validate(_valid_body(), strict=True) == []

    def test_strict_fails_when_no_box_ticked(self):
        body = textwrap.dedent(
            """\
            ## Summary

            Real summary content describing the change in detail here.

            ## General PR

            - [ ] not ticked
            - [ ] also not ticked
            """
        )
        errors = check_pr_body.validate(body, strict=True)
        assert any("strict mode" in e and "no boxes checked" in e for e in errors)

    def test_strict_passes_with_any_box_ticked(self):
        body = textwrap.dedent(
            """\
            ## Summary

            Real summary content describing the change in detail here.

            ## General PR

            - [x] ticked
            """
        )
        assert check_pr_body.validate(body, strict=True) == []

    def test_strict_fails_when_no_checklist_blocks_present(self):
        body = textwrap.dedent(
            """\
            ## Summary

            Real summary content describing the change in detail here.

            ## Linked issues

            Closes #123
            """
        )
        errors = check_pr_body.validate(body, strict=True)
        assert any(
            "strict mode" in e and "Track A" in e and "Track B" in e for e in errors
        )


# ── load_from_event (GitHub event JSON parsing) ───────────────────────


class TestLoadFromEvent:
    def test_extracts_body_from_event(self, tmp_path: Path):
        event = {
            "action": "opened",
            "pull_request": {
                "number": 42,
                "body": "## Summary\n\nA real PR description.\n",
                "draft": False,
            },
        }
        p = tmp_path / "event.json"
        p.write_text(json.dumps(event), encoding="utf-8")
        body = check_pr_body.load_from_event(str(p))
        assert body.startswith("## Summary")

    def test_returns_empty_when_body_null(self, tmp_path: Path):
        event = {"pull_request": {"number": 7, "body": None}}
        p = tmp_path / "event.json"
        p.write_text(json.dumps(event), encoding="utf-8")
        assert check_pr_body.load_from_event(str(p)) == ""

    def test_returns_empty_when_no_pull_request_key(self, tmp_path: Path):
        p = tmp_path / "event.json"
        p.write_text(json.dumps({"action": "opened"}), encoding="utf-8")
        assert check_pr_body.load_from_event(str(p)) == ""

    def test_invalid_json_raises_system_exit(self, tmp_path: Path):
        p = tmp_path / "bad.json"
        p.write_text("{not json", encoding="utf-8")
        with pytest.raises(SystemExit) as exc:
            check_pr_body.load_from_event(str(p))
        assert "invalid JSON" in str(exc.value)

    def test_missing_event_file_raises(self, tmp_path: Path):
        with pytest.raises(SystemExit) as exc:
            check_pr_body.load_from_event(str(tmp_path / "nope.json"))
        assert "event file not found" in str(exc.value)


# ── load_from_file ────────────────────────────────────────────────────


class TestLoadFromFile:
    def test_reads_file(self, tmp_path: Path):
        p = tmp_path / "body.md"
        p.write_text("## Summary\n\nfoo", encoding="utf-8")
        assert check_pr_body.load_from_file(str(p)) == "## Summary\n\nfoo"

    def test_missing_file_raises(self, tmp_path: Path):
        with pytest.raises(SystemExit) as exc:
            check_pr_body.load_from_file(str(tmp_path / "nope.md"))
        assert "file not found" in str(exc.value)


# ── main() / CLI entrypoint ───────────────────────────────────────────


class TestMain:
    def test_main_passes_on_valid_file(
        self, tmp_path: Path, capsys: pytest.CaptureFixture[str]
    ):
        p = tmp_path / "body.md"
        p.write_text(_valid_body(), encoding="utf-8")
        rc = check_pr_body.main(["--file", str(p)])
        assert rc == 0
        out = capsys.readouterr().out
        assert "PR body check OK" in out
        assert "lenient" in out

    def test_main_fails_on_template_file(
        self, tmp_path: Path, capsys: pytest.CaptureFixture[str]
    ):
        p = tmp_path / "body.md"
        p.write_text(_template_body(), encoding="utf-8")
        rc = check_pr_body.main(["--file", str(p)])
        assert rc == 1
        err = capsys.readouterr().err
        assert "FAILED" in err
        assert "Summary" in err

    def test_main_strict_mode_in_summary(
        self, tmp_path: Path, capsys: pytest.CaptureFixture[str]
    ):
        p = tmp_path / "body.md"
        p.write_text(_valid_body(), encoding="utf-8")
        rc = check_pr_body.main(["--file", str(p), "--strict"])
        assert rc == 0
        out = capsys.readouterr().out
        assert "strict" in out

    def test_main_reads_stdin_when_no_source(
        self, monkeypatch: pytest.MonkeyPatch, capsys: pytest.CaptureFixture[str]
    ):
        monkeypatch.setattr(
            sys,
            "stdin",
            io.StringIO(
                "## Summary\n\nA real description with enough characters.\n"
            ),
        )
        rc = check_pr_body.main([])
        assert rc == 0

    def test_main_consumes_event_file(
        self, tmp_path: Path, capsys: pytest.CaptureFixture[str]
    ):
        event = {
            "pull_request": {
                "body": (
                    "## Summary\n\nA real description with enough chars to "
                    "pass the threshold."
                ),
            }
        }
        p = tmp_path / "event.json"
        p.write_text(json.dumps(event), encoding="utf-8")
        rc = check_pr_body.main(["--from-event", str(p)])
        assert rc == 0
