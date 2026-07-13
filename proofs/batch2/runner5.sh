#!/bin/bash
# usage: runner5.sh <listfile> <resultfile> <logprefix> [chunk-timeout-s]
# Bulk-only verifier: chunked `lake build -j4` with per-chunk LOGS, orphan
# pkill after each chunk, then mtime-based PASS/FAIL (validated 289/289
# against runner4 sequential rechecks in wave DR6). No per-target
# re-elaboration — diags are extracted from the chunk logs on the host.
cd /workspace/proofs
LIST=$1; OUT=$2; LOGP=$3; CT=${4:-900}
: > $OUT
rm -f /tmp/chunk.*
split -l 25 "$LIST" /tmp/chunk.
i=0
for ch in /tmp/chunk.*; do
  i=$((i+1))
  timeout "$CT" lake build $(sed 's/^/Proofs./' "$ch") > "${LOGP}-$(printf %02d $i).log" 2>&1
  ec=$?
  pkill -9 lean 2>/dev/null
  [ $ec -eq 124 ] && echo "CHUNK-TIMEOUT $ch" >> "${LOGP}-timeouts.log"
  sleep 1
done
while read -r t; do
  lean="Proofs/$t.lean"
  ol=".lake/build/lib/lean/Proofs/$t.olean"
  if [ -f "$ol" ] && [ -f "$lean" ] && [ "$ol" -nt "$lean" ]; then
    echo "PASS $t" >> $OUT
  elif [ -f "$ol" ] && [ -f "$lean" ] && ! [ "$lean" -nt "$ol" ]; then
    echo "PASS $t" >> $OUT
  else
    echo "FAIL $t" >> $OUT
  fi
done < "$LIST"
