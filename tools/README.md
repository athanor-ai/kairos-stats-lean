# tools

Repo-local developer scripts.

## `md_lint.py`: anti-LLM-slop README linter

A single-file linter for Markdown READMEs. Flags the patterns
LLM-generated prose disproportionately produces vs. human-written
technical documentation.

### Usage

```bash
python3 tools/md_lint.py README.md
python3 tools/md_lint.py README.md --format github   # GH Actions
python3 tools/md_lint.py README.md --rules vocabulary,tagline_opener
python3 tools/md_lint.py README.md --warn-only       # exit 0 on errors
```

Exit codes: `0` clean, `1` error-level finding, `2` bad invocation.

### Rules

| Rule | Severity | Catches |
|------|----------|---------|
| `vocabulary` | error / warn | High-register filler (`cutting-edge`, `harness`, `leverage`, `load-bearing`, `transformative`, `delve`, ...) and discourse markers (`crucially,`, `notably,`, `moreover,`, ...) |
| `tagline_opener` | error | Italic-blockquote one-liner taglines: `> *Aesop-grade automation for ...*` |
| `intent_hedge` | error | `wants to be the canonical X` / `aims to be the leading Y` / `is designed to be the standard Z` |
| `like_analogy` | warn | `Like X for Y, Z is...` analogy lead-ins |
| `marquee_label` | error | `headline` / `marquee` / `flagship` modifying tactic / library / tool / feature / product |
| `field_opener` | warn | Paragraph opens on field-level abstraction (`Modern X`, `In recent years`, `The field of...`) |
| `we_present_library` | warn | Paper voice in a README: `We present X, a library that...` |

### CI integration

`.github/workflows/md-lint.yml` runs the linter on every push and PR
that touches `README.md`. Errors fail the workflow.

### Calibration

Vocabulary blacklist vendored from `paper_lint`, calibrated against
Tang 2024, BBRv3 paper, and CAV/FMCAD/PLDI reference set. None of
the flagged words appear in those corpora.

### Vendoring into another repo

The linter is a single self-contained file. Copy `md_lint.py` and the
workflow file into a target repo:

```bash
mkdir -p /path/to/other-repo/tools /path/to/other-repo/.github/workflows
cp tools/md_lint.py /path/to/other-repo/tools/
cp .github/workflows/md-lint.yml /path/to/other-repo/.github/workflows/
```
