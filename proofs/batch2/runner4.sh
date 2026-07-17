#!/bin/bash
# usage: runner4.sh <listfile> <resultfile> <diagfile> [chunk-timeout-s]
# Like runner3.sh, but the bulk pass is CHUNKED (25 targets, -j4) with an
# orphan-lean pkill after every chunk: a timeout no longer leaves parallel
# lean processes starving the sequential recheck phase (DR6 lesson).
cd /workspace/proofs
LIST=$1; OUT=$2; DIAG=$3; CT=${4:-900}
: > $OUT
: > $DIAG
rm -f /tmp/chunk.*
split -l 25 "$LIST" /tmp/chunk.
for ch in /tmp/chunk.*; do
  timeout "$CT" lake build $(sed 's/^/Proofs./' "$ch") >/dev/null 2>&1 || true
  pkill -9 lean 2>/dev/null
  sleep 1
done
# per-target recheck (cached => instant for passes)
while read -r t; do
  log=$(timeout 300 lake build Proofs.$t 2>&1)
  if [ $? -eq 0 ]; then
    echo "PASS $t" >> $OUT
  else
    pkill -9 lean 2>/dev/null
    echo "FAIL $t" >> $OUT
    echo "===== $t" >> $DIAG
    echo "$log" | grep -E -m4 -A2 "error:" | grep -v '^--$' | head -12 >> $DIAG
  fi
done < "$LIST"
