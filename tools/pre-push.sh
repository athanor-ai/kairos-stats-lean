#!/usr/bin/env bash
# tools/pre-push.sh — local pre-push gate.
#
# Per Aidan 2026-04-25 mandate: never push anything (not even into a
# branch) if any Lean doesn't compile. This script enforces that
# locally before `git push`.
#
# Install as a git pre-push hook:
#
#     ln -s ../../tools/pre-push.sh .git/hooks/pre-push
#
# Or run manually before any push:
#
#     bash tools/pre-push.sh && git push
#
# Exits 0 only if `lake build` succeeds. Exits non-zero (blocking the
# push) on any build failure.

set -e

cd "$(git rev-parse --show-toplevel)"

echo "🔒 pre-push: running lake build (Aidan 2026-04-25 mainline-protection mandate)..."
lake build
echo "✅ lake build clean"

# README-stats-freshness gate (ATH-1300 structural lift, 5-incident receipt:
# fb8376f / bfc8921 / 47248da / cd271be / 4a2c366). Refresh README stats
# whenever any Pythia/**/*.lean change is in the push range; refuse the push
# if doing so produces a non-empty diff (i.e., stats were stale).
PUSH_RANGE="@{upstream}..HEAD"
if ! git rev-parse --verify --quiet "$PUSH_RANGE" >/dev/null; then
  PUSH_RANGE="HEAD~1..HEAD"
fi
PYTHIA_TOUCHED=$(git diff --name-only "$PUSH_RANGE" -- 'Pythia/**/*.lean' 2>/dev/null || true)
if [ -n "$PYTHIA_TOUCHED" ]; then
  echo "🔒 pre-push: Pythia/*.lean change detected — refreshing README stats..."
  python3 tools/refresh_readme_stats.py >/dev/null
  if ! git diff --quiet README.md; then
    echo "❌ pre-push: README stats are stale (refresh_readme_stats.py produced a diff)."
    echo "   Commit the refreshed README.md and re-push:"
    echo "     git add README.md && git commit -m 'chore(README): refresh stats' && git push"
    echo ""
    echo "   Diff preview:"
    git --no-pager diff README.md | head -20
    exit 1
  fi
  echo "✅ README stats fresh"
fi

# Umbrella-import gate (Aidan 2026-05-14 "main must never be red").
# The CI Lean Build per-file sweep fails if a Pythia/**/*.lean file
# is not reachable from the Pythia.lean umbrella. Check new additions.
PYTHIA_ADDED=$(git diff --name-only --diff-filter=A "$PUSH_RANGE" -- 'Pythia/**/*.lean' 2>/dev/null \
  | grep -vE '/Tactic/.*Test\.lean$|/Pythia/Scratch/|VilleMathlibPR\.lean$|AxiomAudit\.lean$' \
  || true)
if [ -n "$PYTHIA_ADDED" ]; then
  echo "pre-push: new Pythia/*.lean file(s) added, checking umbrella imports..."
  MISSING=""
  while IFS= read -r f; do
    [ -z "$f" ] && continue
    MOD=$(echo "$f" | sed 's|/|.|g; s|\.lean$||')
    if ! grep -qE "^import $MOD\$" Pythia.lean; then
      MISSING="${MISSING}  import $MOD    # $f"$'\n'
    fi
  done <<< "$PYTHIA_ADDED"
  if [ -n "$MISSING" ]; then
    echo ""
    echo "ERROR: this push adds new Pythia/*.lean files NOT imported by Pythia.lean."
    echo "The CI per-file Lean sweep will fail. Add these to Pythia.lean:"
    echo ""
    echo "$MISSING"
    exit 1
  fi
  echo "pre-push: umbrella imports clean for added files."
fi

# Fast CI-parity checks: catch sim-sweep failures locally.
RELEVANT_FOR_CI_PARITY=$(git diff --name-only "$PUSH_RANGE" -- 'README.md' 'tools/sim/theorem_manifest.py' 'tools/sim/test_theorem_manifest.py' 2>/dev/null || true)
if [ -n "$PYTHIA_TOUCHED" ] || [ -n "$RELEVANT_FOR_CI_PARITY" ]; then
  echo "pre-push: running CI-parity checks (manifest + README numbers)..."
  if ! python3 -m pytest tools/sim/test_theorem_manifest.py -q --no-header > /tmp/pre-push-pytest.log 2>&1; then
    echo "ERROR: tools/sim/test_theorem_manifest.py failed locally. The sim sweep will go red on push."
    tail -20 /tmp/pre-push-pytest.log
    exit 1
  fi
  if ! python3 tools/check_readme_numbers.py > /tmp/pre-push-readme.log 2>&1; then
    echo "ERROR: tools/check_readme_numbers.py drift detected. The README numbers gate will fail on push."
    cat /tmp/pre-push-readme.log
    exit 1
  fi
  echo "pre-push: CI-parity checks clean."
fi

echo "✅ all pre-push gates clean, push permitted"
