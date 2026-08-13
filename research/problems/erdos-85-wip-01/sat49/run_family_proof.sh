#!/usr/bin/env bash
set -euo pipefail

if [[ $# -ne 4 ]]; then
  echo "usage: $0 CNF EXPECTED_SHA256 OUTDIR NAME" >&2
  exit 2
fi

cnf=$1
expected=$2
outdir=$3
name=$4
glucose_bin=${GLUCOSE_BIN:-glucose}
drat_trim_bin=${DRAT_TRIM_BIN:-drat-trim}
max_proof_gb=${MAX_PROOF_GB:-140}
min_free_gb=${MIN_FREE_GB:-30}

mkdir -p "$outdir"
actual=$(sha256sum "$cnf" | awk '{print $1}')
if [[ "$actual" != "$expected" ]]; then
  echo "CNF hash mismatch: expected $expected, got $actual" >&2
  exit 3
fi

proof="$outdir/$name.drat"
solve_log="$outdir/$name.solve.log"
verify_log="$outdir/$name.verify.log"
verdict="$outdir/$name.verdict.tsv"
started=$(date -u +%Y-%m-%dT%H:%M:%SZ)
start_epoch=$(date +%s)

set +e
"$glucose_bin" -verb=1 -certified \
  -certified-output="$proof" "$cnf" >"$solve_log" 2>&1 &
solver_pid=$!
resource_limit=""
while kill -0 "$solver_pid" 2>/dev/null; do
  proof_bytes=$(stat -c '%s' "$proof" 2>/dev/null || echo 0)
  free_kb=$(df -Pk "$outdir" | awk 'NR == 2 {print $4}')
  if (( proof_bytes > max_proof_gb * 1024 * 1024 * 1024 )); then
    resource_limit="proof>${max_proof_gb}GiB"
    kill "$solver_pid" 2>/dev/null || true
    break
  fi
  if (( free_kb < min_free_gb * 1024 * 1024 )); then
    resource_limit="free-disk<${min_free_gb}GiB"
    kill "$solver_pid" 2>/dev/null || true
    break
  fi
  sleep 5
done
wait "$solver_pid"
solve_rc=$?
set -e
solve_seconds=$(( $(date +%s) - start_epoch ))

if [[ -n "$resource_limit" ]]; then
  printf '%s\t%s\t%s\t%s\t%s\t%s\n' \
    "$name" "RESOURCE_LIMIT" "$resource_limit" "$solve_rc" \
    "$solve_seconds" "$actual" >"$verdict"
  exit 6
fi

if ! grep -q '^s UNSATISFIABLE' "$solve_log"; then
  printf '%s\t%s\t%s\t%s\t%s\n' \
    "$name" "NO_UNSAT" "$solve_rc" "$solve_seconds" "$actual" >"$verdict"
  exit 4
fi

verify_start=$(date +%s)
set +e
"$drat_trim_bin" "$cnf" "$proof" >"$verify_log" 2>&1
verify_rc=$?
set -e
verify_seconds=$(( $(date +%s) - verify_start ))
if [[ $verify_rc -ne 0 ]] || ! grep -q 's VERIFIED' "$verify_log"; then
  printf '%s\t%s\t%s\t%s\t%s\t%s\n' \
    "$name" "NOT_VERIFIED" "$solve_rc" "$solve_seconds" \
    "$verify_seconds" "$actual" >"$verdict"
  exit 5
fi

proof_sha=$(sha256sum "$proof" | awk '{print $1}')
gzip -9 "$proof"
printf '%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\n' \
  "$name" "UNSAT_VERIFIED" "$started" "$solve_seconds" \
  "$verify_seconds" "$actual" "$proof_sha" "$proof.gz" >"$verdict"
echo "$name: UNSAT and DRAT verified"
