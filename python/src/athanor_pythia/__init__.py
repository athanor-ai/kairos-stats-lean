"""athanor-pythia — Python sidecar for the pythia Lean 4 tactic library.

This is a name-reservation placeholder (v0.0.1). The actual product is the
Lean 4 library + headline `pythia` tactic at:

    https://github.com/athanor-ai/pythia

Aesop-grade automation for statistics in Lean 4. Domain hammer for
anytime-valid inference, sequential statistics, empirical processes,
and cross-domain stats (quant / actuarial / physics / biology / ML).

Lean tactics don't ship via PyPI; install the Lean library via:

    require pythia from git
      "https://github.com/athanor-ai/pythia.git" @ "main"

Future versions of this Python package will expose:

    - pythia.fleet.LeanProver (multi-agent cycle-driven proof closer)
    - lean-lsp-mcp helpers for pythia-aware tooling
    - LSP backend self-hosters for loogle / leanfinder / hammer-premise

Companion SDK: `athanor-pythia` (https://github.com/athanor-ai/athanor-sdk).
"""

__version__ = "0.0.1"


def lean_repo_url() -> str:
    """Return the URL of the Lean 4 library this package companions."""
    return "https://github.com/athanor-ai/pythia"
