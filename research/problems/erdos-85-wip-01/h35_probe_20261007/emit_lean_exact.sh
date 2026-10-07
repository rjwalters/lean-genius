#!/bin/bash
# Emit Lean-exact CNF orderFortyNineGeneratedCanonicalSatCnf h (…RepresentativeMasks i) via interpreted
# `lake env lean --run` in the pinned image (same mounts as proofs/scripts/docker-build.sh), 16 GiB cap, no network.
# usage: emit_lean_exact.sh <h3|h5> <index>
set -u
REPO=/Volumes/Stripe/lean-genius/erdos85-certpilot
OUT=/Volumes/Stripe/lean-genius/artifacts/erdos85-sat49/h35-probe-20261007/lean
h=$1; i=$2; name="${h}_t${i}.canonical.lean-exact.cnf"
start=$(date +%s)
docker run --rm --network none --memory=16384m --memory-swap=16384m --cpus=1 \
  -v "$REPO:/workspace:delegated" \
  -v lean-mathlib-cache:/workspace/proofs/.lake/build:delegated \
  -v lean-mathlib-packages:/workspace/proofs/.lake/packages:delegated \
  -v "$OUT:/out" -w /workspace/proofs --name "e85-h35emit-$h-$i" lean4-arm64:v4.31.0 \
  /bin/bash -c "timeout 3600 lake env lean --run /workspace/research/problems/erdos-85-wip-01/h35_probe_20261007/EmitCanonical.lean $h $i > /out/$name.tmp && mv /out/$name.tmp /out/$name"
rc=$?
echo "{\"cell\":\"${h}_t${i}\",\"rc\":$rc,\"wall_s\":$(( $(date +%s)-start ))}" >> "$OUT/emit_runs.jsonl"
