#!/usr/bin/env python3
"""check_pr_body — validate that a PR description keeps the load-bearing
sections of `.github/pull_request_template.md` non-empty.

The repo's PR template ships several `## H2` sections (Summary, Track A
checklist, Track B checklist, General PR checklist, Linked issues).
Reviewers depend on the Summary always being filled; external
contributors sometimes delete it, leaving a checklist-only body that
is hard to triage.

This script reads a candidate PR body from one of:

    --file PATH          a markdown file on disk
    --from-event PATH    a GitHub `pull_request` event payload JSON
                         (extracts `.pull_request.body`)
    (default)            stdin

and checks:

    1. `## Summary` heading is present
    2. The text under `## Summary` (until the next `## ` heading or
       end of file) contains at least 10 non-whitespace characters
       AND is not the verbatim placeholder from the template
       ("What changed and why, in 2-3 sentences.").

In `--strict` mode, additionally:

    3. At least ONE of the three checkbox blocks
       (`## New theorem (Track A...)`, `## New theorem (Track B...)`,
       `## General PR (...)`) has at least one box checked
       (`- [x]` or `- [X]`).

`## Linked issues` is always optional — many PRs are unrelated to a
specific issue and the placeholder `Closes #...` is the documented
no-op.

Exit code:
    0 — all required sections OK; one-line summary printed
    1 — at least one required section missing or empty
    2 — bad invocation / file not found / bad JSON

Usage:
    # Local check of a draft PR description saved to a file
    python3 tools/check_pr_body.py --file my_pr_body.md

    # Pipe-in form for editor integrations
    cat my_pr_body.md | python3 tools/check_pr_body.py

    # CI form (consumed in `.github/workflows/pr-template-check.yml`)
    python3 tools/check_pr_body.py --from-event "$GITHUB_EVENT_PATH"

Stdlib only — runs on a stock ubuntu-latest GitHub runner without
`pip install`.
"""
from __future__ import annotations

import argparse
import json
import re
import sys
from dataclasses import dataclass
from pathlib import Path


# Verbatim placeholder shipped in `.github/pull_request_template.md`.
# A PR body that still has this exact line under `## Summary` has not
# been filled in; treat it as empty.
SUMMARY_PLACEHOLDER = "What changed and why, in 2-3 sentences."

# Minimum non-whitespace character count beneath `## Summary` to count
# as filled. 10 is intentionally low — we only catch obvious neglect,
# not short-but-valid summaries.
MIN_SUMMARY_CHARS = 10

# Heading regex captures the `## H2` lines that delimit template
# sections. We split by these to extract per-section bodies. Match is
# anchored to start-of-line (multiline mode) and stops at end-of-line.
HEADING_RE = re.compile(r"^##\s+(?P<title>.+?)\s*$", re.MULTILINE)

# Checkbox regex covers `- [ ]`, `- [x]`, `- [X]` (markdown task list).
CHECKBOX_RE = re.compile(r"^\s*-\s*\[(?P<mark>[ xX])\]\s*", re.MULTILINE)

# Required H2 titles we must find. The Track A / Track B / General
# titles in the template carry parenthesised qualifiers; we match a
# stable prefix so the script keeps passing if the qualifier is
# reworded.
SUMMARY_TITLE_RE = re.compile(r"^Summary\b", re.IGNORECASE)
TRACK_A_TITLE_RE = re.compile(r"^New theorem \(Track A", re.IGNORECASE)
TRACK_B_TITLE_RE = re.compile(r"^New theorem \(Track B", re.IGNORECASE)
GENERAL_TITLE_RE = re.compile(r"^General PR\b", re.IGNORECASE)


@dataclass
class Section:
    title: str
    body: str  # text until the next H2 heading (excludes the heading itself)


def parse_sections(body: str) -> list[Section]:
    """Split a markdown body into ordered `## H2` sections.

    Anything before the first `## H2` heading is dropped (it's the
    template's HTML comment preamble). Returns sections in document
    order with body text stripped of leading and trailing blank lines
    but otherwise verbatim.
    """
    sections: list[Section] = []
    matches = list(HEADING_RE.finditer(body))
    for i, m in enumerate(matches):
        title = m.group("title").strip()
        start = m.end()
        end = matches[i + 1].start() if i + 1 < len(matches) else len(body)
        section_body = body[start:end].strip("\n")
        sections.append(Section(title=title, body=section_body))
    return sections


def find_section(sections: list[Section], title_re: re.Pattern[str]) -> Section | None:
    """Return the first section whose title matches the supplied regex."""
    for s in sections:
        if title_re.match(s.title):
            return s
    return None


def section_is_meaningful(body: str) -> bool:
    """True if the supplied section body has real content.

    Strips HTML comments first (template preambles use them to give
    instructions that the contributor is supposed to delete), then
    requires `MIN_SUMMARY_CHARS` non-whitespace characters AND that
    the body is not just the verbatim placeholder.
    """
    # Drop HTML comments, which the template uses to ship instructions.
    no_comments = re.sub(r"<!--.*?-->", "", body, flags=re.DOTALL)
    stripped = no_comments.strip()
    if not stripped:
        return False
    if stripped == SUMMARY_PLACEHOLDER:
        return False
    # Count non-whitespace characters as a proxy for real content.
    non_ws = re.sub(r"\s+", "", stripped)
    return len(non_ws) >= MIN_SUMMARY_CHARS


def count_checked_boxes(body: str) -> int:
    """Number of `- [x]` or `- [X]` task-list items in the body."""
    return sum(1 for m in CHECKBOX_RE.finditer(body) if m.group("mark") in ("x", "X"))


def validate(body: str, strict: bool = False) -> list[str]:
    """Run all checks against `body`. Returns the list of error
    messages; an empty list means valid.
    """
    errors: list[str] = []
    sections = parse_sections(body)

    summary = find_section(sections, SUMMARY_TITLE_RE)
    if summary is None:
        errors.append(
            "missing required section `## Summary` "
            "(must be present and non-empty)"
        )
    elif not section_is_meaningful(summary.body):
        errors.append(
            "`## Summary` section is empty or still contains the "
            f"verbatim placeholder ({SUMMARY_PLACEHOLDER!r}); "
            f"write at least {MIN_SUMMARY_CHARS} characters describing "
            "what changed and why"
        )

    if strict:
        track_a = find_section(sections, TRACK_A_TITLE_RE)
        track_b = find_section(sections, TRACK_B_TITLE_RE)
        general = find_section(sections, GENERAL_TITLE_RE)
        checklist_blocks = [
            s for s in (track_a, track_b, general) if s is not None
        ]
        if not checklist_blocks:
            errors.append(
                "strict mode: none of `## New theorem (Track A...)`, "
                "`## New theorem (Track B...)`, `## General PR (...)` "
                "found; restore the template structure"
            )
        else:
            total_checked = sum(
                count_checked_boxes(s.body) for s in checklist_blocks
            )
            if total_checked == 0:
                errors.append(
                    "strict mode: no boxes checked across the Track A "
                    "/ Track B / General PR checklists; tick at least "
                    "one box in the section that matches your PR"
                )

    return errors


# ───────────────────────────────────────────────────────────────────────
# Body loaders.
# ───────────────────────────────────────────────────────────────────────


def load_from_file(path: str) -> str:
    p = Path(path)
    if not p.exists():
        raise SystemExit(f"check_pr_body: file not found: {path}")
    return p.read_text(encoding="utf-8")


def load_from_event(path: str) -> str:
    """Extract `.pull_request.body` from a GitHub `pull_request` event
    payload JSON (the file at `$GITHUB_EVENT_PATH` in CI).

    Returns an empty string when the body field is null / absent —
    upstream validation will then flag the missing Summary section
    with a clear message.
    """
    p = Path(path)
    if not p.exists():
        raise SystemExit(f"check_pr_body: event file not found: {path}")
    try:
        payload = json.loads(p.read_text(encoding="utf-8"))
    except json.JSONDecodeError as e:
        raise SystemExit(f"check_pr_body: invalid JSON in event file: {e}")
    pr = payload.get("pull_request") or {}
    body = pr.get("body")
    return body if isinstance(body, str) else ""


def load_from_stdin() -> str:
    return sys.stdin.read()


# ───────────────────────────────────────────────────────────────────────
# CLI entrypoint.
# ───────────────────────────────────────────────────────────────────────


def build_parser() -> argparse.ArgumentParser:
    p = argparse.ArgumentParser(
        prog="check_pr_body",
        description=(
            "Validate that a PR description keeps the load-bearing "
            "sections of the repo's PR template non-empty."
        ),
    )
    src = p.add_mutually_exclusive_group()
    src.add_argument(
        "--file",
        metavar="PATH",
        help="read PR body from a markdown file (default: stdin)",
    )
    src.add_argument(
        "--from-event",
        metavar="PATH",
        help=(
            "read PR body from a GitHub event payload JSON; extracts "
            "`.pull_request.body`. Use $GITHUB_EVENT_PATH in CI."
        ),
    )
    p.add_argument(
        "--strict",
        action="store_true",
        help=(
            "additionally enforce that at least one Track A / Track B "
            "/ General PR checkbox is ticked"
        ),
    )
    return p


def main(argv: list[str] | None = None) -> int:
    args = build_parser().parse_args(argv)
    if args.file:
        body = load_from_file(args.file)
    elif args.from_event:
        body = load_from_event(args.from_event)
    else:
        body = load_from_stdin()

    errors = validate(body, strict=args.strict)
    if errors:
        sys.stderr.write("PR body check FAILED:\n")
        for e in errors:
            sys.stderr.write(f"  - {e}\n")
        sys.stderr.write(
            "\nFix: edit the PR description to fill the flagged "
            "sections, then re-run.\n"
        )
        return 1
    mode = "strict" if args.strict else "lenient"
    sys.stdout.write(
        f"PR body check OK ({mode} mode): all required sections present.\n"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
