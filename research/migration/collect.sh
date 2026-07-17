#!/bin/bash
# Conflict-proof collector for the single-proof migration fleet.
#
# For each pushed mig/<file>: apply ONLY its .lean, re-verify it compiles EXIT=0 in a
# CLEAN container, then flip its single ledger row. NEVER `git merge` a mig branch —
# that avoids verify-results.tsv conflicts AND catches false-greens / case-collisions.
#
# usage: collect.sh <verify-cache-vol> <cpuset> <collect-worktree> <file1> <file2> ...
# env (override per migration): REPO (default cwd), FEATURE_BRANCH, PKGS_VOL, IMAGE, LEDGER
set +e   # a NO-BRANCH / FAILED-VERIFY on one file must not abort the loop

CACHE=$1; CPUS=$2; CWT=$3; shift 3
REPO="${REPO:-$(git -C "$CWT" rev-parse --show-toplevel)}"
FEATURE_BRANCH="${FEATURE_BRANCH:-feature/issue-37508}"
PKGS_VOL="${PKGS_VOL:-lean-mathlib-packages-v431}"
IMAGE="${IMAGE:-lean4-arm64:v4.31.0}"
LEDGER="${LEDGER:-proofs/batch2/verify-results.tsv}"

git -C "$CWT" fetch origin "$FEATURE_BRANCH" -q
git -C "$CWT" checkout -q -B collect-robust "origin/$FEATURE_BRANCH"
git -C "$CWT" clean -fdq

for f in "$@"; do
  git -C "$CWT" fetch origin "mig/$f" -q 2>/dev/null || { echo "NO-BRANCH $f"; continue; }
  git -C "$CWT" checkout "origin/mig/$f" -- "proofs/Proofs/$f.lean" 2>/dev/null || { echo "NO-FILE $f"; continue; }
  # Re-verify in a clean container (builds so the olean lands for downstream children).
  ec=$(timeout 400 docker run --rm --memory 8g --cpuset-cpus "$CPUS" \
    -v "$CWT:/workspace" -v "$PKGS_VOL:/workspace/proofs/.lake/packages" \
    -v "$CACHE:/workspace/proofs/.lake/build" -w /workspace/proofs "$IMAGE" \
    bash -c "lake build Proofs.$f >/dev/null 2>&1; echo \${PIPESTATUS:-\$?}" 2>/dev/null | tail -1)
  if [ "$ec" = "0" ]; then
    # Flip the single ledger row (col1 is the BARE module name — match exactly, not by path/.lean).
    python3 - "$CWT/$LEDGER" "$f" <<'PY'
import sys
p, f = sys.argv[1], sys.argv[2]
L = open(p).read().splitlines()
out = [(f + "\tGREEN\t") if (c := l.split("\t")) and c[0] == f else l for l in L]
open(p, "w").write("\n".join(out) + "\n")
PY
    git -C "$CWT" add "proofs/Proofs/$f.lean" "$LEDGER"
    echo "VERIFIED-GREEN $f"
  else
    git -C "$CWT" checkout -- "proofs/Proofs/$f.lean" 2>/dev/null || true
    echo "FAILED-VERIFY $f (ec=$ec)"   # false-green caught — do NOT merge
  fi
done
