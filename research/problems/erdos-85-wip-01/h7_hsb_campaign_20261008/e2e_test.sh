#!/usr/bin/env bash
# End-to-end test of cert_worker.py / cert_batch.py / collect_receipts.py on the builder, against a
# local directory store (no S3, no instances). 21 real items in the exact campaign format (leaves
# known from the cost sample to take 0.4-50 s), plus:
#   * a simulated spot reclaim (claim + ledger removed, 3 receipts left as partial/) -> carry-forward
#   * a must-ALARM run with a fake checker that never prints `s VERIFIED UNSAT` -> ALARM + STOP
#   * a worker started after STOP must claim nothing
#   * a 5 s solver cap -> INCOMPLETE ledger (timeouts are not alarms)
# usage: e2e_test.sh <inputs dir> <out dir> <cadical> <cake_lpr> [slots]
set -uo pipefail
IN=$1; OUT=$2; CAD=$3; CAKE=$4; SLOTS=${5:-2}
HERE=$(cd "$(dirname "$0")" && pwd); PY=${PY:-python3.12}
rm -rf "$OUT"; mkdir -p "$OUT"
cat > "$OUT/manifest.jsonl" <<'M'
{"cube": "cube_F6_t14", "id": "cube_F6_t14-cover", "kind": "cover"}
{"cube": "cube_F6_t14", "end": 5, "id": "cube_F6_t14-b0000", "kind": "leaves", "start": 0}
{"cube": "cube_F6_t14", "end": 10, "id": "cube_F6_t14-b0001", "kind": "leaves", "start": 5}
{"cube": "cube_F9_t1", "id": "cube_F9_t1-x0", "kind": "leaves", "leaves": [4890, 4571, 6823, 4349, 4067]}
{"cube": "cube_F7_t5", "id": "cube_F7_t5-x0", "kind": "leaves", "leaves": [469, 1410, 814, 1035, 1336]}
M
MS=$(sha256sum "$OUT/manifest.jsonl" | cut -d' ' -f1); IS=$(sha256sum "$IN/inputs.json" | cut -d' ' -f1)
W() { # W <tag> <store> <cake> [extra args]
  local tag=$1 store=$2 cake=$3; shift 3
  $PY -B "$HERE/cert_worker.py" --inputs "$IN" --inputs-sha256 "$IS" --manifest "$OUT/manifest.jsonl" --manifest-sha256 "$MS" \
    --iid "i-test-$tag" --itype builder --head "$(git -C "$HERE" rev-parse HEAD 2>/dev/null || echo unknown)" --slots "$SLOTS" \
    --heap-mb 2000 --cap 900 --lifetime 86400 --min-left 60 --partial-seconds 20 --cadical "$CAD" --cake-lpr "$cake" \
    --work "/dev/shm/h7camp-e2e" --out "$OUT/node-$tag" --log "$OUT/worker-$tag.log" --local-store "$store" --no-poweroff "$@"
}
fail=0; chk() { if eval "$2"; then echo "PASS $1"; else echo "FAIL $1"; fail=1; fi; }
S=$OUT/store
echo "== plan"; W plan "$S" "$CAKE" --plan
echo "== run 1 (all rows)"; t0=$(date +%s); W a "$S" "$CAKE"; echo "run1 wall $(( $(date +%s) - t0 ))s"
chk "5 claims" '[ $(ls "$S/claims" | wc -l) = 5 ]'
chk "5 CERTIFIED ledgers" '[ $(grep -l "\"status\": \"CERTIFIED\"" "$S"/ledger/*.json | wc -l) = 5 ]'
chk "claim body is the instance id" '[ "$(cat "$S/claims/cube_F9_t1-x0")" = i-test-a ]'
echo "== simulated reclaim of cube_F9_t1-x0 (3 receipts survive as a partial)"
f=$(ls "$S"/results/cube_F9_t1-x0.*.jsonl.zst); zstd -dc "$f" | head -3 > "$S/partial/cube_F9_t1-x0.i-dead.jsonl" 2>/dev/null || { mkdir -p "$S/partial"; zstd -dc "$f" | head -3 > "$S/partial/cube_F9_t1-x0.i-dead.jsonl"; }
mkdir -p "$OUT/removed"; mv "$f" "$S"/ledger/cube_F9_t1-x0.* "$OUT/removed/"; rm "$S/claims/cube_F9_t1-x0"
W b "$S" "$CAKE"
L=$(ls "$S"/ledger/cube_F9_t1-x0.i-test-b.*.json)
chk "re-claimed batch CERTIFIED with 3 carried" 'grep -q "\"carried\": 3" "$L" && grep -q "\"status\": \"CERTIFIED\"" "$L"'
echo "== collect"; $PY -B "$HERE/collect_receipts.py" --inputs "$IN" --results "$S/results" --out "$OUT/collected" --cubes cube_F6_t14 | tee "$OUT/collect.json" | head -40
chk "collector sees cover + 10 leaves of cube_F6_t14" 'grep -q "\"certified_leaves\": 10" "$OUT/collect.json" && grep -q "\"cover_certified\": true" "$OUT/collect.json"'
echo "== must-ALARM: fake checker that never verifies"
printf '#!/bin/sh\ncat "$2" > /dev/null\necho "c fake checker"\nexit 0\n' > "$OUT/fake_cake"; chmod +x "$OUT/fake_cake"
S2=$OUT/store-alarm
W c "$S2" "$OUT/fake_cake" --only cube_F6_t14-b0000 --slots 1
chk "ALARM + STOP written, nothing CERTIFIED" '[ -f "$S2/control/STOP" ] && ls "$S2"/control/ALARM-* >/dev/null && ! grep -l "\"status\": \"CERTIFIED\"" "$S2"/ledger/*.json'
W d "$S2" "$CAKE"
chk "worker after STOP claims nothing" '[ $(ls "$S2/claims" | wc -l) = 1 ]'
echo "== cap path: 5 s cap on a batch with leaves that need 7-50 s -> INCOMPLETE, no alarm"
S3=$OUT/store-cap
W e "$S3" "$CAKE" --only cube_F9_t1-x0 --slots 1 --cap 5
chk "INCOMPLETE ledger lists SOLVER_TIMEOUT leaves, no STOP" 'grep -q "\"status\": \"INCOMPLETE\"" "$S3"/ledger/*.json && grep -q SOLVER_TIMEOUT "$S3"/ledger/*.json && [ ! -e "$S3/control/STOP" ]'
echo "== ledgers"; for l in "$S"/ledger/*.json; do $PY -c "import json,sys; l=json.load(open(sys.argv[1])); print(l['id'], l['node'], l['status'], l['certified'], '/', l['items'], 'carried', l['carried'], 'solver_cpu', round(l['solver_cpu_seconds'],1), 'checker_cpu', round(l['checker_cpu_seconds'],1), 'proof', l['proof_bytes'])" "$l"; done
[ $fail = 0 ] && echo "E2E_ALL_PASS" || echo "E2E_FAILED"
exit $fail
