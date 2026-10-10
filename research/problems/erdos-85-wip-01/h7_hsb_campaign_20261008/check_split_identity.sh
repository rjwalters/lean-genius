#!/usr/bin/env bash
# Run from proofs/ inside the pinned Lean image:
#   e85-remote run <sha> --full --mem 16 --threads 1 -- bash ../research/problems/erdos-85-wip-01/h7_hsb_campaign_20261008/check_split_identity.sh
# Elaborates EmitSplit.lean (incl. its rfl decomposition theorems) and compares the Lean tails of every
# split in receipts/split_identity_fixture.json with h7_common's. The receipt JSON is printed between markers.
set -euo pipefail
D=../research/problems/erdos-85-wip-01/h7_hsb_campaign_20261008
git -C .. rev-parse HEAD 2>/dev/null || true
sha256sum "$D/EmitSplit.lean" "$D/receipts/split_identity_fixture.json" Proofs/Erdos85OrderFortyNineSevenHighT0CanonicalHsbLeafSplit.lean \
  Proofs/Erdos85OrderFortyNineSevenHighT0CanonicalHsbLeaves.lean Proofs/Erdos85OrderFortyNineSevenHighT0CanonicalHsbGen.lean
rc=0
python3 "$D/check_split_identity.py" check --fixture "$D/receipts/split_identity_fixture.json" --out /tmp/split_identity.json \
  --emitter "$D/EmitSplit.lean" || rc=$?
echo "=====RECEIPT-BEGIN====="; cat /tmp/split_identity.json 2>/dev/null; echo "=====RECEIPT-END====="
exit $rc
