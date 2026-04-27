"""tools.sim.harness.v2.replay — counterexample recording + replay.

A failure recorded by :func:`record_failure` round-trips through JSON
and replays via :func:`replay_corpus`. The user's property is called
positionally with whatever the strategy emitted: a scalar, a list, or
a dict. ``record_failure`` and ``replay_corpus`` agree on this shape:
the saved JSON's ``sample`` field is the raw value, not wrapped in a
sentinel key.
"""
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


def _hash_sample(sample: Any) -> str:
    return hashlib.sha256(
        json.dumps(sample, sort_keys=True, default=str).encode()
    ).hexdigest()[:16]


def record_failure(
    sim_name: str,
    seed: int,
    sample: Any,
    message: str,
) -> Path:
    """Persist a failing example to ``tools/sim/counterexamples/<sim_name>/seed_<hash>.json``.

    ``sample`` is whatever the strategy returned (scalar / list / dict).
    Round-trips through JSON via :func:`json.dumps(..., default=str)`
    so any opaque object is at least repr'd into a string.
    """
    path = _sim_dir(sim_name) / f"seed_{_hash_sample(sample)}.json"
    path.write_text(
        json.dumps(
            {
                "sim_name": sim_name,
                "seed": seed,
                "sample": sample,
                "message": message,
            },
            indent=2,
            default=str,
        ),
        encoding="utf-8",
    )
    return path


def load_corpus(sim_name: str) -> list[dict[str, Any]]:
    """Load all persisted counterexamples for ``sim_name``."""
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
    """Rerun every persisted counterexample. Raises if any still fails.

    Calls ``property_fn(sample)`` positionally with the saved sample
    value. This matches the call shape used by
    :class:`Sim._run_property_strict` (``prop(sample)``).
    """
    still_failing = []
    for entry in load_corpus(sim_name):
        sample = entry.get("sample")
        try:
            ok = bool(property_fn(sample))
        except Exception as exc:
            ok = False
            entry = {**entry, "_replay_exception": str(exc)}
        if not ok:
            still_failing.append(entry)
    if still_failing:
        raise AssertionError(
            f"replay_corpus({sim_name!r}): {len(still_failing)} counterexample(s) still failing:\n"
            + "\n".join(json.dumps(f, default=str) for f in still_failing)
        )


@pytest.fixture
def replay_corpus_fixture():
    """Pytest fixture: ``replay_corpus_fixture(sim_name, property_fn)``."""
    return lambda sim_name, property_fn: replay_corpus(sim_name, property_fn)


__all__ = ["load_corpus", "record_failure", "replay_corpus", "replay_corpus_fixture"]
