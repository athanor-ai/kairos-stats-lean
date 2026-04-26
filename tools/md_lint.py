#!/usr/bin/env python3
"""md_lint — anti-LLM-slop linter for single Markdown files (READMEs etc.).

Targets the patterns LLM-generated prose disproportionately produces vs.
human-written technical documentation: high-register filler vocabulary,
italic-blockquote taglines, "wants to be" / "designed to" intent-hedging,
"like X for Y" analogy openings, and field-rhetoric meta openers.

Usage:
    python3 tools/md_lint.py README.md
    python3 tools/md_lint.py README.md --format github      # GH Actions
    python3 tools/md_lint.py README.md --warn-only          # exit 0 even on errors
    python3 tools/md_lint.py README.md --rules vocabulary,tagline_opener

Exit code:
    0 — no error-level findings
    1 — one or more error-level findings
    2 — bad invocation / file not found

Calibrated against the paper_lint vocabulary blacklist used on Athanor's
research papers.
"""
from __future__ import annotations

import argparse
import re
import sys
from dataclasses import dataclass
from pathlib import Path


@dataclass(frozen=True)
class Finding:
    rule: str
    severity: str  # "error" | "warning"
    line: int
    col: int
    text: str
    reason: str
    suggestion: str


# ---------------------------------------------------------------------------
# Vocabulary blacklist (vendored from paper_lint, calibrated against Tang
# 2024, BBRv3 paper, CAV/FMCAD/PLDI reference set — none used these words).
# Each entry: (regex, severity, suggestion).
# ---------------------------------------------------------------------------

_VOCAB: list[tuple[str, str, str]] = [
    # Hype / marketing fillers.
    (r"\bcutting-?edge\b", "error", "drop entirely"),
    (r"\bground-?breaking\b", "error", "drop entirely"),
    (r"\btransformative\b", "error", "drop entirely"),
    (r"\bunparalleled\b", "error", "drop entirely"),
    (r"\bstate[- ]of[- ]the[- ]art\b", "warning", "drop or quantify"),
    (r"\bbest[- ]in[- ]class\b", "error", "drop"),
    (r"\bworld[- ]class\b", "error", "drop"),
    (r"\bgame[- ]chang(ing|er)\b", "error", "drop; quantify the change"),
    (r"\bparadigm shift\b", "error", "drop entirely"),
    (r"\bnext[- ]generation\b", "warning", "drop or specify version"),
    (r"\bindustry[- ]leading\b", "error", "drop"),
    (r"\bpowerful\b", "warning", "drop or quantify capability"),
    (r"\brobust\b", "warning", "drop or specify what's robust to"),
    (r"\bseamless(ly)?\b", "error", "drop entirely"),
    (r"\beffortless(ly)?\b", "error", "drop entirely"),
    (r"\bblazing(ly)?\b", "error", "drop or give the number"),
    (r"\blightning[- ]fast\b", "error", "drop or give the number"),
    (r"\bsupercharge[ds]?\b", "error", "drop"),
    (r"\bturbocharge[ds]?\b", "error", "drop"),
    # Academic-ese filler.
    (r"\belide[ds]?\b|\belided\b|\beliding\b", "error", "drop / leave out"),
    (r"\bdelve[ds]?\b|\bdelving\b", "error", "examine / look at"),
    (r"\bleverage[ds]?\b|\bleveraging\b", "error", "use / uses"),
    (r"\bharness(es|ed|ing)?\b", "error", "use / apply"),
    (r"\bmeticulous(ly)?\b", "error", "drop"),
    (r"\bcomprehensive(ly)?\b", "error", "complete / list what was covered"),
    (r"\bholistic(ally)?\b", "error", "drop; describe what you mean"),
    (r"\bmultifaceted\b", "error", "specific / complex"),
    (r"\bnuanced\b", "error", "specific"),
    (r"\bintricate\b", "error", "specific"),
    (r"\bbespoke\b", "error", "custom / specific"),
    (r"\bplethora\b", "error", "many"),
    (r"\bmyriad\b", "error", "many"),
    (r"\btapestry\b", "error", "drop"),
    (r"\brealm of\b", "error", "in / for"),
    (r"\blandscape of\b", "error", "in / among"),
    (r"\bdynamic (field|landscape|area|domain|environment)\b",
     "error", "drop 'dynamic' or give a specific adjective"),
    (r"\bever-\w+\b", "error", "drop 'ever-' prefix"),
    (r"\bshowcase[ds]?\b|\bshowcasing\b", "error", "show / demonstrate"),
    (r"\bunderscore[ds]?\b|\bunderscoring\b", "error",
     "drop; let the claim stand"),
    (r"\belucidate[ds]?\b|\belucidating\b", "error", "explain / show"),
    (r"\bdemystif(y|ies|ied)\b", "error", "explain / describe"),
    (r"\bnavigat(e|ing|es|ed)\b", "warning", "use a domain-specific verb"),
    (r"\bembark(s|ed|ing)?\b", "error", "start / begin"),
    (r"\bnestled\b", "error", "located / contained"),
    (r"\bvibrant\b", "error", "drop"),
    (r"\bgarner(ed|s|ing)?\b", "error", "received / attracted"),
    (r"\bbolster(s|ed|ing)?\b", "error", "strengthen / support / increase"),
    (r"\bfoster(s|ed|ing)?\b", "error", "enable / allow / support"),
    (r"\bcultivat(e|es|ed|ing)\b", "error", "build / develop / grow"),
    (r"\bempower(s|ed|ing)?\b", "error", "enable / let / allow"),
    (r"\bfacilitate[ds]?\b|\bfacilitating\b", "error", "enable / perform"),
    (r"\bstreamline[ds]?\b|\bstreamlining\b", "error", "simplify / replace"),
    (r"\bunpack(s|ed|ing)?\b", "error", "describe / explain"),
    (r"\bdive deep(er)? into\b", "error", "examine / look at"),
    (r"\bload[- ]bearing\b", "error", "drop; name the specific role"),
    (r"\btestament\b", "error", "drop; state the evidence directly"),
    (r"\bresonate[ds]?\b|\bresonating\b", "error",
     "drop; state the claim directly"),
    (r"\bpivotal\b", "error", "specific / central"),
    (r"\bparamount\b", "error", "necessary / required"),
    (r"\bprofound(ly)?\b", "error",
     "large / drop / specific numeric adjective"),
    # Discourse markers / filler intensifiers.
    (r"\bcrucially,\b", "error", "drop"),
    (r"\bcrucial\b", "error", "quantify / specific"),
    (r"\bnotably,\b", "error", "drop"),
    (r"\bimportantly,\b", "error", "drop"),
    (r"\binterestingly,\b", "error", "drop"),
    (r"\bremarkably,\b", "error", "drop"),
    (r"\bsurprisingly,\b", "error", "drop"),
    (r"\bstrikingly,\b", "error", "drop"),
    (r"\bindeed,\b", "error", "drop"),
    (r"\bfurthermore,\b", "error", "drop or 'and'"),
    (r"\bmoreover,\b", "error", "drop or 'and'"),
    (r"\badditionally,\b", "error", "drop or 'and'"),
    (r"\bin addition,\b", "error", "drop or 'and'"),
    (r"\bin essence,?\b", "error", "drop"),
    (r"\bat the end of the day\b", "error", "drop"),
    (r"\bin today'?s world\b", "error", "drop"),
    (r"\bgoing forward,?\b", "error", "drop"),
    (r"\bmoving forward,?\b", "error", "drop"),
    (r"\bit is worth noting\b", "error", "drop"),
    (r"\bit should be noted\b", "error", "drop"),
    (r"\bit is important to note\b", "error", "drop"),
    (r"\bit bears (mentioning|noting|pointing out)\b", "error", "drop"),
    # Meta-qualifiers + soft claims.
    (r"\b(a |the )?wide range of\b", "warning",
     "specific count or 'several'"),
    (r"\bhighly (successful|capable|effective|accurate)\b", "error",
     "quantify instead"),
    (r"\bsignificantly (improved|enhanced|outperforms?)\b", "error",
     "give the number"),
    (r"\bnot only .{1,60}but also\b", "error",
     "drop 'not only ... but also' structure"),
    # Self-praise / vacuous adjectives.
    (r"\belegant(ly)?\b", "warning", "drop or describe specifically"),
    (r"\bbeautif(ul|ully)\b", "warning", "drop"),
    (r"\bamazingly\b|\bamazing\b", "error", "drop"),
    (r"\bincredibl[ey]\b", "error", "drop"),
    (r"\bstunning(ly)?\b", "error", "drop"),
    (r"\bremarkable\b", "error", "drop or quantify"),
    (r"\bdeeply\b", "warning", "drop or specify how"),
    (r"\bthoughtful(ly)?\b", "warning", "drop"),
    (r"\bcommendable\b", "error", "drop; specific praise"),
    (r"\bwhilst\b", "warning", "while"),
    (r"\bactionable\b", "warning", "useful / concrete"),
]

_VOCAB_COMPILED = [
    (re.compile(p, re.IGNORECASE), sev, sugg) for (p, sev, sugg) in _VOCAB
]


# ---------------------------------------------------------------------------
# README-specific patterns.
# ---------------------------------------------------------------------------

# A blockquote opener of the form `> *some tagline.*` is the prototypical
# LLM-generated marketing one-liner.
_TAGLINE_OPENER = re.compile(
    r"^\s*>\s*\*[^*\n]{4,160}\*\s*$",
    re.MULTILINE,
)

# Intent hedging — "X is a Y that wants to be the canonical Z" / "aims to be"
# / "is designed to be" all signal generated marketing.
_INTENT_HEDGE = re.compile(
    r"\b(wants? to be|aims? to be|strives? to|is designed to|seeks? to be)"
    r"\s+the\s+(canonical|definitive|leading|premier|go[- ]to|"
    r"best|primary|standard)\b",
    re.IGNORECASE,
)

# "Like X for Y" analogy lead-ins are a Claude-tell when followed by
# library-marketing structure.
_LIKE_ANALOGY = re.compile(
    r"\bLike\s+`?[A-Z][\w_]*`?\s+for\s+\w+,\s+`?[A-Z][\w_]*`?\b",
)

# "the headline / marquee / flagship X" — marketing labels.
_MARQUEE_LABEL = re.compile(
    r"\b(headline|marquee|flagship)\s+(tactic|library|tool|feature|product)\b",
    re.IGNORECASE,
)

# Field-rhetoric meta opener — paragraph-leading sentence that starts on
# field-level abstraction rather than on the artifact.
_FIELD_OPENER = re.compile(
    r"(^|\n\n)\s*(Computational|Modern|Contemporary|In recent years|"
    r"In the past decade|For decades|The field of|Over the past|"
    r"Recent advances|The development of|The emergence of|"
    r"In today's |Today's )",
    re.IGNORECASE,
)

# "We present X, a Y that ..." — pattern flagged when describing a
# library/tool that already exists (not "we present" in a paper context,
# which is a different style).
_WE_PRESENT_LIBRARY = re.compile(
    r"\bWe\s+present\s+\w+,\s+a\s+\w+\s+(library|tool|framework|package|"
    r"system)\s+that\b",
    re.IGNORECASE,
)


# ---------------------------------------------------------------------------
# Rules.
# ---------------------------------------------------------------------------

def _line_col(text: str, offset: int) -> tuple[int, int]:
    head = text[:offset]
    line = head.count("\n") + 1
    last_nl = head.rfind("\n")
    col = offset - last_nl
    return line, col


def _snippet(text: str, m: re.Match, pad: int = 40) -> str:
    s = max(0, m.start() - pad)
    e = min(len(text), m.end() + pad)
    snip = text[s:e].replace("\n", " ")
    return snip


def _strip_code_blocks(text: str) -> str:
    """Replace fenced ``` ``` blocks with blank lines (preserve line numbers).
    Inline `code spans` are left alone — they rarely contain prose violations."""
    out_lines: list[str] = []
    in_fence = False
    for line in text.splitlines():
        stripped = line.lstrip()
        if stripped.startswith("```") or stripped.startswith("~~~"):
            in_fence = not in_fence
            out_lines.append("")
            continue
        if in_fence:
            out_lines.append("")
        else:
            out_lines.append(line)
    return "\n".join(out_lines)


def check_vocabulary(text: str) -> list[Finding]:
    out: list[Finding] = []
    for pattern, sev, sugg in _VOCAB_COMPILED:
        for m in pattern.finditer(text):
            line, col = _line_col(text, m.start())
            out.append(Finding(
                rule="vocabulary",
                severity=sev,
                line=line,
                col=col,
                text=_snippet(text, m),
                reason=f"AI-fingerprint phrase: {m.group(0)!r}",
                suggestion=f"Replace with: {sugg}",
            ))
    return out


def check_tagline_opener(text: str) -> list[Finding]:
    out: list[Finding] = []
    for m in _TAGLINE_OPENER.finditer(text):
        line, col = _line_col(text, m.start())
        out.append(Finding(
            rule="tagline_opener",
            severity="error",
            line=line,
            col=col,
            text=m.group(0).strip(),
            reason="Italic-blockquote tagline reads as marketing copy.",
            suggestion=("Open on what the project does in plain prose. Show "
                        "a concrete example (code, command, output). Drop "
                        "the > *...* line."),
        ))
    return out


def check_intent_hedge(text: str) -> list[Finding]:
    out: list[Finding] = []
    for m in _INTENT_HEDGE.finditer(text):
        line, col = _line_col(text, m.start())
        out.append(Finding(
            rule="intent_hedge",
            severity="error",
            line=line,
            col=col,
            text=_snippet(text, m, pad=60),
            reason=("'wants to be the canonical X' / 'aims to be' / "
                    "'designed to be the leading Y' is intent-hedging "
                    "marketing prose."),
            suggestion=("State what the library actually does. If the "
                        "ambition is real, ship the evidence; if not, "
                        "drop the claim."),
        ))
    return out


def check_like_analogy(text: str) -> list[Finding]:
    out: list[Finding] = []
    for m in _LIKE_ANALOGY.finditer(text):
        line, col = _line_col(text, m.start())
        out.append(Finding(
            rule="like_analogy",
            severity="warning",
            line=line,
            col=col,
            text=_snippet(text, m, pad=60),
            reason=("'Like X for Y' analogy lead-ins are an LLM tell."),
            suggestion=("Drop the analogy. Describe the artifact directly."),
        ))
    return out


def check_marquee_label(text: str) -> list[Finding]:
    out: list[Finding] = []
    for m in _MARQUEE_LABEL.finditer(text):
        line, col = _line_col(text, m.start())
        out.append(Finding(
            rule="marquee_label",
            severity="error",
            line=line,
            col=col,
            text=_snippet(text, m, pad=40),
            reason=("'headline / marquee / flagship X' is marketing label."),
            suggestion=("Drop the adjective. Just say what the thing is."),
        ))
    return out


def check_field_opener(text: str) -> list[Finding]:
    out: list[Finding] = []
    for m in _FIELD_OPENER.finditer(text):
        line, col = _line_col(text, m.start())
        out.append(Finding(
            rule="field_opener",
            severity="warning",
            line=line,
            col=col,
            text=_snippet(text, m, pad=80),
            reason=("Paragraph opens on field-level abstraction "
                    "('Modern X', 'In recent years', 'The field of...'). "
                    "Real READMEs open on the artifact."),
            suggestion=("Open on what the project does, or on a concrete "
                        "example."),
        ))
    return out


def check_we_present_library(text: str) -> list[Finding]:
    out: list[Finding] = []
    for m in _WE_PRESENT_LIBRARY.finditer(text):
        line, col = _line_col(text, m.start())
        out.append(Finding(
            rule="we_present_library",
            severity="warning",
            line=line,
            col=col,
            text=_snippet(text, m, pad=80),
            reason=("'We present X, a library that...' is paper voice in "
                    "a README."),
            suggestion=("Use README voice: 'X is a library that does Y.'"),
        ))
    return out


_RULES = {
    "vocabulary": check_vocabulary,
    "tagline_opener": check_tagline_opener,
    "intent_hedge": check_intent_hedge,
    "like_analogy": check_like_analogy,
    "marquee_label": check_marquee_label,
    "field_opener": check_field_opener,
    "we_present_library": check_we_present_library,
}


# ---------------------------------------------------------------------------
# CLI.
# ---------------------------------------------------------------------------

def _format_text(path: Path, findings: list[Finding]) -> str:
    if not findings:
        return f"{path}: clean ({len(_RULES)} rules checked)\n"
    lines = [f"{path}: {len(findings)} finding(s)"]
    for f in findings:
        marker = "ERROR" if f.severity == "error" else "warn "
        lines.append(f"  [{marker}] {path}:{f.line}:{f.col}  ({f.rule})")
        lines.append(f"           {f.reason}")
        lines.append(f"           snippet: …{f.text}…")
        lines.append(f"           suggest: {f.suggestion}")
    return "\n".join(lines) + "\n"


def _format_github(path: Path, findings: list[Finding]) -> str:
    out: list[str] = []
    for f in findings:
        cmd = "error" if f.severity == "error" else "warning"
        msg = f"{f.rule}: {f.reason} — {f.suggestion}".replace(
            "\n", " ").replace("%", "%25")
        out.append(
            f"::{cmd} file={path},line={f.line},col={f.col}::{msg}"
        )
    return "\n".join(out) + ("\n" if out else "")


def main(argv: list[str] | None = None) -> int:
    p = argparse.ArgumentParser(
        prog="md_lint",
        description="Anti-LLM-slop linter for single Markdown files.",
    )
    p.add_argument("path", help="Path to .md file")
    p.add_argument("--rules", default="all",
                   help="Comma-separated rule names, or 'all' (default).")
    p.add_argument("--format", choices=["text", "github"], default="text")
    p.add_argument("--warn-only", action="store_true",
                   help="Exit 0 even when errors are found.")
    p.add_argument("--quiet", action="store_true",
                   help="Print nothing on clean files.")
    args = p.parse_args(argv)

    path = Path(args.path)
    if not path.is_file():
        print(f"md_lint: not a file: {path}", file=sys.stderr)
        return 2

    raw = path.read_text(encoding="utf-8", errors="replace")
    text = _strip_code_blocks(raw)

    if args.rules == "all":
        rules = list(_RULES.keys())
    else:
        rules = [r.strip() for r in args.rules.split(",") if r.strip()]
        unknown = [r for r in rules if r not in _RULES]
        if unknown:
            print(f"md_lint: unknown rule(s): {','.join(unknown)}",
                  file=sys.stderr)
            print(f"md_lint: known rules: {','.join(_RULES)}",
                  file=sys.stderr)
            return 2

    findings: list[Finding] = []
    for r in rules:
        findings.extend(_RULES[r](text))

    findings.sort(key=lambda f: (f.line, f.col, f.rule))

    if args.format == "github":
        out = _format_github(path, findings)
    else:
        out = _format_text(path, findings)

    if findings or not args.quiet:
        sys.stdout.write(out)

    n_errors = sum(1 for f in findings if f.severity == "error")
    if args.warn_only:
        return 0
    return 1 if n_errors > 0 else 0


if __name__ == "__main__":
    sys.exit(main())
