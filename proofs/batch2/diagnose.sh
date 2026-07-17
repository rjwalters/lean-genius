#!/bin/bash
cd /workspace/proofs
LIST=$1; OUT=$2
: > $OUT
while read t; do
  echo "===== $t" >> $OUT
  timeout 300 lake build Proofs.$t 2>&1 | grep -E "error" | head -5 >> $OUT
done < $LIST
