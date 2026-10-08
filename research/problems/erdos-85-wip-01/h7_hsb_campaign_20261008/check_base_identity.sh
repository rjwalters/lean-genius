#!/usr/bin/env bash
# Run from proofs/ inside the pinned Lean image (e85-remote run <branch> --full -- bash ../research/.../check_base_identity.sh).
# Prints the Lean cube term for all 28 structural cubes (interpreted `lean --run`) and compares
# sha256 with the frozen Python root hashes. The receipt JSON is printed between markers.
set -euo pipefail
D=../research/problems/erdos-85-wip-01/h7_hsb_campaign_20261008
ARGS="6 5 6 8 6 14 6 15 6 16 6 17 6 18 7 0 7 2 7 3 7 4 7 5 7 6 7 8 7 9 7 10 7 11 7 13 7 14 8 0 8 1 8 2 8 3 8 4 8 5 8 6 9 0 9 1"
git -C .. rev-parse HEAD 2>/dev/null || true
sha256sum "$D/EmitCube.lean" Proofs/Erdos85OrderFortyNineSevenHighT0CanonicalEmptyCubeCnf.lean Proofs/Erdos85OrderFortyNineSevenHighT0CanonicalCnf.lean
rc=0
# shellcheck disable=SC2086
lake env lean --run "$D/EmitCube.lean" $ARGS | python3 "$D/check_base_identity.py" /tmp/base_identity.json || rc=$?
echo "=====RECEIPT-BEGIN====="; cat /tmp/base_identity.json 2>/dev/null; echo "=====RECEIPT-END====="
exit $rc
