#!/bin/bash
# usage: runner.sh <listfile> <resultfile>
cd /workspace/proofs
LIST=$1; OUT=$2
: > $OUT
# bulk parallel pass (ignore failures)
timeout 2400 lake build $(sed 's/^/Proofs./' $LIST) >/dev/null 2>&1 || true
# per-target recheck (cached => instant)
while read t; do
  if timeout 300 lake build Proofs.$t >/dev/null 2>&1; then echo "PASS $t"; else echo "FAIL $t"; fi >> $OUT
done < $LIST
