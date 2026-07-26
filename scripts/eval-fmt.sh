#!/usr/bin/env bash
#
# Evaluate a change to the auto-formatter by formatting core twice and diffing.
#
# Given a jj change F that contains the formatter changes you want to evaluate,
# this script:
#   1. Creates a new change on top of F's parent (F without the formatter change).
#   2. Builds Lean there and runs `lake fmt` on core           -> baseline run.
#   3. Builds Lean at F (with the formatter change).
#   4. Creates a new change on top of the baseline run.
#   5. Runs `lake fmt` again with F's binary.
#
# The final change (@) then contains ONLY the delta produced by F's formatter
# change relative to the baseline, i.e. exactly what your change does to core.
#
# Usage:
#   scripts/eval-fmt.sh [FMT_REV] [BASE_REV]
#
#   FMT_REV    Revision of the change to evaluate. Default: @- (previous change).
#   BASE_REV   Revision to compare against, i.e. the baseline the formatter is
#              run on without FMT_REV's change. Default: the parent of FMT_REV.
#
# Environment:
#   LEAN_NUM_THREADS   Threads for `lake fmt`. Default: 40.

set -euo pipefail

FMT_REV="${1:-@-}"
BASE_REV="${2:-}"
: "${LEAN_NUM_THREADS:=12}"
export LEAN_NUM_THREADS

ROOT=$(jj root)
NPROC=$(command -v nproc >/dev/null && nproc || sysctl -n hw.logicalcpu)
LAKE="$ROOT/build/release/stage1/bin/lake"

# Resolve stable change IDs up front, because @-relative revsets shift as we
# create new changes below.
resolve() { jj log --no-graph -r "$1" -T 'change_id.short()'; }

FMT_CHANGE=$(resolve "$FMT_REV")
BASE_CHANGE=$(resolve "${BASE_REV:-${FMT_CHANGE}-}")

build() {
  echo ">>> building Lean (make -j$NPROC -C $ROOT/build/release)"
  make -j"$NPROC" -C "$ROOT/build/release"
}

run_fmt() {
  echo ">>> running formatter: LEAN_NUM_THREADS=$LEAN_NUM_THREADS lake fmt (in $ROOT/src)"
  # `lake fmt` exits non-zero when it reformats files (or on partial failures),
  # which is expected here -- we care about the resulting working-copy changes,
  # not the exit status. Don't let it abort the script under `set -e`.
  local rc=0
  ( cd "$ROOT/src" && "$LAKE" fmt ) || rc=$?
  if [ "$rc" -ne 0 ]; then
    echo ">>> lake fmt exited with status $rc (continuing)"
  fi
}

echo "=== Evaluating formatter change $FMT_CHANGE (parent: $BASE_CHANGE) ==="

# --- Baseline: format core WITHOUT the formatter change -----------------------
echo
echo "=== [1/2] Baseline run (without $FMT_CHANGE) ==="
jj new "$BASE_CHANGE" -m "fmt baseline: core formatted without $FMT_CHANGE"
BASELINE_RUN=$(resolve @)
build
run_fmt
echo ">>> baseline run recorded in change $BASELINE_RUN"

# --- Evaluation: format core WITH the formatter change ------------------------
echo
echo "=== [2/2] Evaluation run (with $FMT_CHANGE) ==="
# Build the binary WITH the formatter change; the resulting on-disk binary is
# what we use to format on top of the baseline run.
jj edit "$FMT_CHANGE"
build
# New change on top of the baseline-formatted core; formatting it with the
# updated binary yields only the delta relative to the baseline run.
jj new "$BASELINE_RUN" -m "fmt eval: delta from $FMT_CHANGE"
DELTA_RUN=$(resolve @)
run_fmt

echo
echo "=== Done ==="
echo "Baseline run:   $BASELINE_RUN"
echo "Evaluation run: $DELTA_RUN (current change @)"
echo
echo "The delta produced by $FMT_CHANGE:"
jj diff --stat -r @
