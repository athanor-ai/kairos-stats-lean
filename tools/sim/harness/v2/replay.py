"""tools.sim.harness.v2.replay — counterexample recording + replay."""
from __future__ import annotations

import hashlib
import json
from pathlib import Path
from typing import Any, Callable

import pytest

_REPO_ROOT = Path(__file__).resolve().parents[4]
_CE_DIR = _REPO_ROOT / "tools" / "sim" / "counterexamples"


def _sim_dir(sim_name: str) -> Path:
    d = _CE_DIR / sim_name
    d.mkdir(parents=True, exist_ok=True)
    return d


def _hash_inputs(inputs: dict[str, Any]) -> str:
    return hashlib.sha256(json.dumps(inputs, sort_keys=True, default=str).encode()).hexdigest()[:16]


def record_failure(
    sim_name: str,
    seed: int,
    inputs: dict[str, Any],
    message: str,
) -> Path:
    """Persist a failing example to tools/sim/counterexamples/<sim_name>/seed_<hash>.json."""
    path = _sim_dir(sim_name) / f"seed_{_hash_inputs(inputs)}.json"
    path.write_text(json.dumps({"sim_name": sim_name, "seed": seed, "inputs": inputs, "message": message}, indent=2, default=str), encoding="utf-8")
    return path


def load_corpus(sim_name: str) -> list[dict[str, Any]]:
    """Load all persisted counterexamples for sim_name."""
    d = _CE_DIR / sim_name
    if not d.exists():
        return []
    entries = []
    for path in sorted(d.glob("seed_*.json")):
        try:
            entries.append(json.loads(path.read_text(encoding="utf-8")))
        except Exception:
            pass
    return entries


def replay_corpus(sim_name: str, property_fn: Callable[..., bool]) -> None:
    """Rerun every persisted counterexample. Raises AssertionError if any still fails."""
    still_failing = []
    for entry in load_corpus(sim_name):
        inputs = entry.get("inputs", {})
        try:
            ok = property_fn(**inputs)
        except Exception as exc:
            ok = False
            inputs = {**inputs, "_exception": str(exc)}
        if not ok:
            still_failing.append(inputs)
    if still_failing:
        raise AssertionError(
            f"replay_corpus({sim_name!r}): {len(still_failing)} counterexample(s) still failing:\n"
            + "\n".join(json.dumps(f, default=str) for f in still_failing)
        )


@pytest.fixture
def replay_corpus_fixture():
    """Pytest fixture: call replay_corpus_fixture(sim_name, property_fn)."""
    return lambda sim_name, property_fn: replay_corpus(sim_name, property_fn)


__all__ = ["load_corpus", "record_failure", "replay_corpus", "replay_corpus_fixture"]
