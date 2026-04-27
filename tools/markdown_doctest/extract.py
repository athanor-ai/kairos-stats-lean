"""Extract Lean code blocks from markdown via the markdown-it AST.

NO regex on the raw markdown source — uses the structured AST produced
by ``markdown-it-py`` so that fence detection, nesting, and HTML-
comment adjacency are all handled by the parser, not by ad-hoc string
slicing.

The marker-detection step DOES use a small substring check on the
HTML-comment token's content, but the comment node itself is
identified through the AST (not by scanning raw lines for ``<!--``),
which means commented-out fences inside other commented blocks are
correctly skipped.
"""
from __future__ import annotations

from dataclasses import dataclass
from pathlib import Path
from typing import Optional

from markdown_it import MarkdownIt


# Doctest skip markers. The HTML comment must contain ONE of these
# strings; anything more elaborate goes in the free-text reason form
# (skip-reason:).
_SKIP_TOKENS = ("doctest: skip", "doctest: lakefile", "doctest: cmd-only")


@dataclass(frozen=True)
class CodeBlock:
    """One extracted Lean fenced code block.

    Attributes:
        path: source markdown file (relative to repo root).
        block_idx: 0-based ordinal of this block within the file
            (counting only Lean-tagged blocks, skipped or not).
        start_line: 1-based line number of the opening fence.
        info: the fence info string (``lean`` or ``lean4``).
        body: block contents WITHOUT the surrounding fences.
        skip_reason: None if the block should be compiled; otherwise
            the marker text (``doctest: skip``, ``doctest: lakefile``,
            etc.) or the free-text after ``skip-reason:``.
    """
    path: Path
    block_idx: int
    start_line: int
    info: str
    body: str
    skip_reason: Optional[str]

    @property
    def test_id(self) -> str:
        """Stable test-id for pytest parametrization. Survives renames
        of unrelated files because it's keyed on path + block-idx."""
        return f"{self.path}::block_{self.block_idx}"


def _parse_skip_marker(html_block_content: str) -> Optional[str]:
    """Return the skip reason string if this HTML comment is a doctest
    marker, else None. Uses substring containment, not regex.
    """
    s = html_block_content.strip()
    # Markdown-it emits the full ``<!-- ... -->`` text in html_block tokens;
    # strip the surrounding markers if present.
    if s.startswith("<!--") and s.endswith("-->"):
        s = s[4:-3].strip()
    # skip-reason: <text> takes precedence so the reason can carry
    # context like "lakefile fragment".
    if "doctest: skip-reason:" in s:
        idx = s.find("doctest: skip-reason:")
        return s[idx + len("doctest: skip-reason:"):].strip() or "skip-reason: <empty>"
    for tok in _SKIP_TOKENS:
        if tok in s:
            return tok
    return None


def extract_blocks(path: Path) -> list[CodeBlock]:
    """Walk the markdown AST of ``path``; yield every fenced lean/lean4
    block, with skip markers resolved to a non-None ``skip_reason`` if
    a doctest comment immediately precedes the fence.
    """
    md = MarkdownIt("commonmark")
    text = path.read_text(errors="replace")
    tokens = md.parse(text)

    out: list[CodeBlock] = []
    block_idx = 0
    pending_skip: Optional[str] = None

    for tok in tokens:
        if tok.type == "html_block":
            marker = _parse_skip_marker(tok.content)
            if marker:
                # Carry forward to the next fence; cleared after consumption
                # OR after a non-fence block, so a marker only applies to
                # the immediately following fence.
                pending_skip = marker
            else:
                # Some other HTML block; clear any prior pending marker
                # to enforce "immediately precedes" semantics.
                pending_skip = None
        elif tok.type == "fence" and tok.info.strip() in ("lean", "lean4"):
            start_line = (tok.map[0] + 1) if tok.map else 1
            body = tok.content
            # tok.content already strips the fences
            out.append(CodeBlock(
                path=path,
                block_idx=block_idx,
                start_line=start_line,
                info=tok.info.strip(),
                body=body,
                skip_reason=pending_skip,
            ))
            block_idx += 1
            pending_skip = None
        elif tok.type in ("paragraph_open", "paragraph_close",
                          "inline", "softbreak", "hardbreak"):
            # Inline whitespace doesn't break adjacency.
            continue
        else:
            # Any other block-level element separates the marker from
            # the next fence.
            pending_skip = None

    return out


def discover_markdown(repo_root: Path) -> list[Path]:
    """Yield every ``*.md`` file under ``repo_root`` excluding hidden
    dirs (``.git``, ``.lake``) and node_modules-style noise."""
    out: list[Path] = []
    for p in sorted(repo_root.rglob("*.md")):
        rel = p.relative_to(repo_root)
        if any(part.startswith(".") for part in rel.parts):
            continue
        if "node_modules" in rel.parts:
            continue
        out.append(p)
    return out
