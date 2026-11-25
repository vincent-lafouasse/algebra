#!/bin/bash
# Run the Batteries environment linters on `Base` and `Algebra`, ignoring missing docstrings
# (`docBlame`: this project documents with `--` comments). Bash 3.2 compatible.
#
#     scripts/lint.sh
#
# Exits 1 if any other linter reports something, or if the linter itself fails.

cd "$(dirname "$0")/.." || exit 1

out=$(lake exe runLinter Base 2>&1)
status=$?
out2=$(lake exe runLinter Algebra 2>&1)
status2=$?
out=$(printf '%s\n%s' "$out" "$out2")
[ "$status" -eq 0 ] && status=$status2

ignored=$(printf '%s\n' "$out" | grep -c 'missing documentation string')
errors=$(printf '%s\n' "$out" | grep 'error:' | grep -v 'missing documentation string')

if [ -n "$errors" ]; then
  printf '%s\n' "$errors"
  exit 1
fi

# runLinter failed, and not because of docstrings: show everything
if [ "$status" -ne 0 ] && [ "$ignored" -eq 0 ]; then
  printf '%s\n' "$out"
  exit "$status"
fi

echo "lint: ok ($ignored missing docstrings ignored)"
