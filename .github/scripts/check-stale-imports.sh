#!/bin/bash
set -e
EXIT=0
for f in $(find Pythia/ -name "*.lean" -not -path "*/Frontier/*" -not -path "*/Scratch/*" -not -path "*/.lake/*"); do
  while IFS= read -r line; do
    mod=$(echo "$line" | sed 's/import //' | tr '.' '/')
    path="${mod}.lean"
    if [[ "$line" == *"Frontier"* ]] && [ ! -f "$path" ]; then
      echo "ERROR: $f imports non-existent module: $line (expected $path)"
      EXIT=1
    fi
  done < <(grep "^import Pythia" "$f" 2>/dev/null)
done
if [ $EXIT -ne 0 ]; then
  echo "FAILED: stale imports detected."
  exit 1
fi
echo "OK: no stale imports."
