#!/usr/bin/env bash
#
# Spike failure-inventory harness for the v4.26.0 -> v4.31.0 toolchain bump
# (issue #37508). Runs inside the Docker image; builds each Proofs/*.lean file
# individually, capturing per-file logs so triage can grep failure classes
# (deprecated lemma / unknown identifier / tactic timeout / etc.) without
# re-running the build.
#
# NOT for merge to main as a functional change — this is spike instrumentation.
# The existing build-safe-subset.sh is unchanged.
#
set -uo pipefail

cd "$(dirname "$0")/.."

LOGDIR="${SPIKE_LOGDIR:-/workspace/proofs/spike-logs}"
mkdir -p "$LOGDIR"
RESULTS="$LOGDIR/results.tsv"
: > "$RESULTS"

EXCLUDE=("Erdos728FactorialDivisibility")

# Optional caps for time-budgeted runs: LIMIT=N builds only first N files.
LIMIT="${LIMIT:-0}"

echo "=== Spike Failure Inventory (v4.31.0) ==="
echo "Log dir: $LOGDIR"
echo ""

count=0
pass=0
fail=0
for file in Proofs/*.lean; do
  name=$(basename "$file" .lean)

  skip=false
  for exc in "${EXCLUDE[@]}"; do
    [[ "$name" == "$exc" ]] && skip=true && break
  done
  if $skip; then
    echo -e "$name\tSKIP" >> "$RESULTS"
    continue
  fi

  count=$((count + 1))
  if [[ "$LIMIT" -gt 0 && "$count" -gt "$LIMIT" ]]; then
    break
  fi

  if lake build "Proofs.$name" > "$LOGDIR/$name.log" 2>&1; then
    echo -e "$name\tPASS" >> "$RESULTS"
    pass=$((pass + 1))
    # keep log only on failure to save space
    rm -f "$LOGDIR/$name.log"
  else
    echo -e "$name\tFAIL" >> "$RESULTS"
    fail=$((fail + 1))
  fi
done

echo ""
echo "=== Done: $pass passed, $fail failed (of $count attempted) ==="
echo "Failure logs retained in $LOGDIR/*.log"
