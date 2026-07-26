#!/usr/bin/env bash
#
# Evaluate a change to the auto-formatter by formatting core twice from the same
# unformatted input and diffing the two results.
#
# This is the layout-preserving variant of `scripts/eval-fmt.sh`. That script
# chains its two runs: the second one formats the output of the first, so it
# sees core as laid out by the baseline formatter rather than as laid out in the
# repository. Formatter changes that depend on the layout of their input -- e.g.
# anything that inspects whether a node was already on a single line -- are
# therefore evaluated against the wrong input there. (The two scripts agree once
# core is a fixpoint of the baseline formatter, since then the baseline run is a
# no-op.) Here both runs get the exact same input, so the delta is the true
# difference between the two formatters on core. Both scripts do the same two
# builds and two `lake fmt` runs.
#
# Given a jj change F that contains the formatter changes you want to evaluate,
# this script:
#   1. Creates a new change on top of F's parent (F without the formatter change).
#   2. Builds Lean there and runs `lake fmt` on core           -> baseline run.
#   3. Builds Lean at F (with the formatter change).
#   4. Creates a sibling change, again on top of F's parent, and runs `lake fmt`
#      there with F's binary                                   -> evaluation run.
#   5. Creates a change on top of the baseline run holding the evaluation run's
#      content.
#
# The final change (@) then contains ONLY the delta between the two runs, i.e.
# exactly what your change does to core.
#
# Usage:
#   scripts/eval-fmt-fresh.sh [FMT_REV] [BASE_REV]
#
#   FMT_REV    Revision of the change to evaluate. Default: @- (previous change).
#   BASE_REV   Revision to compare against, i.e. the baseline the formatter is
#              run on without FMT_REV's change. Default: the parent of FMT_REV.
#
# Environment:
#   LEAN_NUM_THREADS   Threads for `lake fmt`. Default: 40.
#   FMT_EVAL_LOG_DIR   Where to write logs. Default: `build/fmt-eval-logs`
#                      (inside `build/`, which is ignored, so the logs are not
#                      snapshotted into the changes this script creates).

set -euo pipefail

FMT_REV="${1:-@-}"
BASE_REV="${2:-}"
: "${LEAN_NUM_THREADS:=12}"
export LEAN_NUM_THREADS

ROOT=$(jj root)
NPROC=$(command -v nproc >/dev/null && nproc || sysctl -n hw.logicalcpu)
LAKE="$ROOT/build/release/stage1/bin/lake"

LOG_DIR="${FMT_EVAL_LOG_DIR:-$ROOT/build/fmt-eval-logs}/$(date +%Y%m%d-%H%M%S)"
mkdir -p "$LOG_DIR"

# Resolve stable change IDs up front, because @-relative revsets shift as we
# create new changes below.
resolve() { jj log --no-graph -r "$1" -T 'change_id.short()'; }

FMT_CHANGE=$(resolve "$FMT_REV")
BASE_CHANGE=$(resolve "${BASE_REV:-${FMT_CHANGE}-}")

build() {
  local log="$LOG_DIR/$1-build.log"
  echo ">>> building Lean (make -j$NPROC -C $ROOT/build/release), logging to $log"
  make -j"$NPROC" -C "$ROOT/build/release" 2>&1 | tee "$log"
}

run_fmt() {
  local log="$LOG_DIR/$1-fmt.log"
  local failedLog="$LOG_DIR/$1-fmt-failures.log"
  echo ">>> running formatter: LEAN_NUM_THREADS=$LEAN_NUM_THREADS lake fmt (in $ROOT/src)"
  echo ">>> logging to $log"
  # `lake fmt` exits non-zero when it reformats files (or on partial failures),
  # which is expected here -- we care about the resulting working-copy changes,
  # not the exit status. Don't let it abort the script under `set -e`.
  local rc=0
  ( cd "$ROOT/src" && "$LAKE" fmt ) 2>&1 | tee "$log" || rc=$?
  if [ "$rc" -ne 0 ]; then
    echo ">>> lake fmt exited with status $rc (continuing)"
  fi
  # A file that `lake fmt` fails on is left unchanged, which shows up in the
  # delta as a spurious whole-file revert of the other run's formatting. These
  # failures are per-run, so both runs need to be checked.
  grep '^Failed to format ' "$log" > "$failedLog" || true
  local failedCount
  failedCount=$(( $(wc -l < "$failedLog") ))
  if [ "$failedCount" -gt 0 ]; then
    echo ">>> WARNING: $failedCount file(s) failed to format and were left unchanged:"
    sed 's/^/      /' "$failedLog"
    echo ">>> They pollute the delta; see $failedLog"
  else
    echo ">>> all files formatted successfully"
  fi
}

echo "=== Evaluating formatter change $FMT_CHANGE (parent: $BASE_CHANGE) ==="
echo "=== Logs: $LOG_DIR ==="

# --- Baseline: format core WITHOUT the formatter change -----------------------
echo
echo "=== [1/2] Baseline run (without $FMT_CHANGE) ==="
jj new "$BASE_CHANGE" -m "fmt baseline: core formatted without $FMT_CHANGE"
BASELINE_RUN=$(resolve @)
build baseline
run_fmt baseline
echo ">>> baseline run recorded in change $BASELINE_RUN"

# --- Evaluation: format the same input WITH the formatter change --------------
echo
echo "=== [2/2] Evaluation run (with $FMT_CHANGE) ==="
# Build the binary WITH the formatter change; the resulting on-disk binary is
# what we use for the second run.
jj edit "$FMT_CHANGE"
build eval
# Sibling of the baseline run rather than a child, so that both runs format
# core exactly as it is committed in $BASE_CHANGE.
jj new "$BASE_CHANGE" -m "fmt eval: core formatted with $FMT_CHANGE"
EVAL_RUN=$(resolve @)
run_fmt eval
echo ">>> evaluation run recorded in change $EVAL_RUN"

# --- Delta --------------------------------------------------------------------
# A change parented on the baseline run but holding the evaluation run's content,
# so that its own diff is precisely the difference between the two runs.
jj new "$BASELINE_RUN" -m "fmt eval: delta from $FMT_CHANGE"
DELTA_RUN=$(resolve @)
jj restore --from "$EVAL_RUN"

{
  echo
  echo "=== Done ==="
  echo "Baseline run:   $BASELINE_RUN"
  echo "Evaluation run: $EVAL_RUN"
  echo "Delta:          $DELTA_RUN (current change @)"
  echo "Logs:           $LOG_DIR"

  # Files that only one of the two runs failed on are unformatted on that side,
  # so their whole-file diff is an artifact rather than an effect of the change.
  sed 's/^Failed to format //; s| ([0-9]*/[0-9]*)$||' "$LOG_DIR"/*-fmt-failures.log \
    | sort -u > "$LOG_DIR/all-failures.log"
  if [ -s "$LOG_DIR/all-failures.log" ]; then
    echo
    echo "WARNING: files that failed to format in at least one run, and whose diff in"
    echo "the delta is therefore an artifact rather than an effect of $FMT_CHANGE:"
    sed 's/^/  /' "$LOG_DIR/all-failures.log"
    echo "Reformat them individually (\`cd src && lake fmt <file>\`) with each build,"
    echo "or rerun the script, before reading the delta."
  fi

  echo
  echo "The delta produced by $FMT_CHANGE:"
  jj diff --stat -r @
  echo
  echo "Full effect of the updated formatter on core:"
  echo "  jj diff --from $BASE_CHANGE --to $EVAL_RUN"
} 2>&1 | tee "$LOG_DIR/summary.log"
