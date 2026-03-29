#!/usr/bin/env bash
# Restores files where the only changes are:
# 1. Reordering the linter.listVariables comment above the set_option line
# 2. Collapsing consecutive blank lines into a single blank line
# These are formatting-only changes with no semantic effect.

set -euo pipefail

cd "$(git rev-parse --show-toplevel)"

git diff --name-only | while IFS= read -r f; do
  # Check pattern 1: the only diff lines are the comment/set_option reorder
  changes=$(git diff "$f" | grep -E '^\+[^+]|^-[^-]')
  expected='-set_option linter.listVariables true -- Enforce naming conventions for `List`/`Array`/`Vector` variables.
+-- Enforce naming conventions for `List`/`Array`/`Vector` variables.
+set_option linter.listVariables true'
  if [ "$changes" = "$expected" ]; then
    printf '%s\0' "$f"
    continue
  fi

  # Check pattern 2: HEAD and working tree are identical after collapsing
  # consecutive blank lines (cat -s)
  head_collapsed=$(git show "HEAD:$f" | cat -s)
  work_collapsed=$(cat "$f" | cat -s)
  if [ "$head_collapsed" = "$work_collapsed" ]; then
    printf '%s\0' "$f"
    continue
  fi
done | xargs -0 -r git checkout --
