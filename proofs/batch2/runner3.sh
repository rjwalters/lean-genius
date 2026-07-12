#!/bin/bash
# usage: runner3.sh <listfile> <resultfile> <diagfile> [bulk-timeout-s]
# Like runner2.sh, but: (a) configurable bulk timeout, (b) diag keeps 2 context
# lines after each error line so instance-synth targets record WHICH instance
# failed to synthesize (runner2's `grep error | head -5` dropped those lines).
cd /workspace/proofs
LIST=$1; OUT=$2; DIAG=$3; BULK=${4:-3600}
: > $OUT
: > $DIAG
# bulk parallel pass (ignore failures)
timeout $BULK lake build $(sed 's/^/Proofs./' $LIST) >/dev/null 2>&1 || true
# per-target recheck (cached => instant for passes)
while read t; do
  log=$(timeout 300 lake build Proofs.$t 2>&1)
  if [ $? -eq 0 ]; then
    echo "PASS $t" >> $OUT
  else
    echo "FAIL $t" >> $OUT
    echo "===== $t" >> $DIAG
    echo "$log" | grep -E -m4 -A2 "error:" | grep -v '^--$' | head -12 >> $DIAG
  fi
done < $LIST
