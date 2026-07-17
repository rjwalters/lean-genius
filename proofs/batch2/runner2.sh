#!/bin/bash
# usage: runner2.sh <listfile> <resultfile> <diagfile>
# Like runner.sh, but captures first error lines per FAIL target into <diagfile>.
cd /workspace/proofs
LIST=$1; OUT=$2; DIAG=$3
: > $OUT
: > $DIAG
# bulk parallel pass (ignore failures)
timeout 2400 lake build $(sed 's/^/Proofs./' $LIST) >/dev/null 2>&1 || true
# per-target recheck (cached => instant)
while read t; do
  log=$(timeout 300 lake build Proofs.$t 2>&1)
  if [ $? -eq 0 ]; then
    echo "PASS $t" >> $OUT
  else
    echo "FAIL $t" >> $OUT
    echo "===== $t" >> $DIAG
    echo "$log" | grep -E "error" | head -5 >> $DIAG
  fi
done < $LIST
