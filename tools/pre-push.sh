#!/usr/bin/env bash
# pre-push hook: run pythia-prepush.sh local CI parity check.
# Aidan correction 2026-05-03: tooling enforcement, not memory.
# Bypass with --no-verify ONLY in emergencies (and you should ping
# Aidan first to explain why).

set -e

SCRIPT=/home/azureuser/bin/pythia-prepush.sh
if [ ! -x "$SCRIPT" ]; then
  echo "WARNING: $SCRIPT not executable; skipping prepush check (install it!)"
  exit 0
fi

echo ""
echo "=== Running pythia-prepush.sh before push ==="
"$SCRIPT" --quick
result=$?

if [ $result -ne 0 ]; then
  echo ""
  echo "✗ Pre-push check failed. Push aborted."
  echo "  Fix the failing checks above, OR bypass with: git push --no-verify"
  echo "  (only bypass after pinging Aidan to explain why.)"
  exit 1
fi

echo ""
echo "✓ Pre-push checks passed; proceeding with push."
