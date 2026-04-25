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
echo "✅ lake build clean — push permitted"
