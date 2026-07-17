#!/bin/bash
# usage: diagnose-fast.sh <faillist> <diagfile>
# 60s/target: captures diagnostics for fast-failing targets (parse errors,
# unknown constants) — the mechanically fixable classes. Slow targets marked TIMEOUT.
cd /workspace/proofs
LIST=$1; OUT=$2
: > $OUT
while read t; do
  echo "===== $t" >> $OUT
  log=$(timeout 60 lake build Proofs.$t 2>&1)
  rc=$?
  if [ $rc -eq 124 ]; then
    echo "TIMEOUT-60s" >> $OUT
  else
    echo "$log" | grep -E "error" | head -5 >> $OUT
  fi
done < $LIST
