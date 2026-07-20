#!/bin/bash
# Integration test for the OQ-recursion-depth cap in
# .lean/scripts/extract-problems.ts (issue #39827).
#
# Runs the REAL extractor against a synthetic src/data/proofs tree in a temp
# cwd and asserts that a proof whose id is already at/over the cap does NOT
# spawn `-oq-` children, while shallower proofs still do. Also verifies the
# MAX_OQ_DEPTH env override and the telemetry line on stderr.
#
# Requires `tsx` on PATH (the extractor imports only Node builtins, so no
# node_modules install is needed).
#
# Run: bash scripts/tests/extract-problems-oq-cap.test.sh
# Exits non-zero if any assertion fails.
set -u

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
EXTRACTOR="$SCRIPT_DIR/../../.lean/scripts/extract-problems.ts"

if ! command -v tsx >/dev/null 2>&1 && ! command -v npx >/dev/null 2>&1; then
    echo "SKIP: neither tsx nor npx on PATH" >&2
    exit 0
fi
TSX_CMD=(tsx)
command -v tsx >/dev/null 2>&1 || TSX_CMD=(npx tsx)

PASS=0; FAIL=0
assert_eq() { if [[ "$3" == "$2" ]]; then echo "  ok: $1 -> $3"; ((PASS++)); else echo "  FAIL: $1 expected '$2' got '$3'"; ((FAIL++)); fi; }
assert_contains() { if [[ "$3" == *"$2"* ]]; then echo "  ok: $1"; ((PASS++)); else echo "  FAIL: $1 (missing '$2')"; ((FAIL++)); fi; }

WORK="$(mktemp -d)"
trap 'rm -rf "$WORK"' EXIT

# make_proof <id>  -- writes a verified proof meta.json with one open question.
make_proof() {
    local id="$1"
    mkdir -p "$WORK/src/data/proofs/$id"
    cat > "$WORK/src/data/proofs/$id/meta.json" <<EOF
{
  "id": "$id",
  "title": "Proof $id",
  "slug": "$id",
  "description": "test",
  "meta": { "status": "verified", "badge": "original", "tags": ["t"], "sorries": 0 },
  "conclusion": { "openQuestions": [ { "id": "q1", "question": "Can we generalize $id?" } ] }
}
EOF
}

mkdir -p "$WORK/.lean/config" "$WORK/.lean/research"
printf '{"maxOqDepth": 3}\n' > "$WORK/.lean/config/oq-policy.json"

# Depths: root(0), 2, 3(at cap), 4(over cap).
make_proof "alpha"
make_proof "beta-oq-01-oq-02"
make_proof "gamma-oq-01-oq-02-oq-03"
make_proof "delta-oq-01-oq-02-oq-03-oq-04"

echo "--- Run 1: default cap (config=3) ---"
ERRFILE="$WORK/err1.txt"
( cd "$WORK" && "${TSX_CMD[@]}" "$EXTRACTOR" --json ) >/dev/null 2>"$ERRFILE"
IDS="$(python3 -c "import json;print('\n'.join(p['id'] for p in json.load(open('$WORK/.lean/research/problems.json'))))")"

assert_contains "root proof spawns oq child" "alpha-oq-01" "$IDS"
assert_contains "depth-2 proof spawns oq child" "beta-oq-01-oq-02-oq-01" "$IDS"
# gamma is AT the cap (depth 3): must NOT spawn a depth-4 child.
if [[ "$IDS" == *"gamma-oq-01-oq-02-oq-03-oq-01"* ]]; then
    echo "  FAIL: at-cap proof spawned a child"; ((FAIL++))
else
    echo "  ok: at-cap proof (depth 3) spawned no child"; ((PASS++))
fi
# delta is OVER the cap (depth 4): must NOT spawn a child either.
if [[ "$IDS" == *"delta-oq-01-oq-02-oq-03-oq-04-oq-01"* ]]; then
    echo "  FAIL: over-cap proof spawned a child"; ((FAIL++))
else
    echo "  ok: over-cap proof (depth 4) spawned no child"; ((PASS++))
fi
assert_contains "telemetry line emitted" "OQ-cap: capped OQ recursion" "$(cat "$ERRFILE")"

echo "--- Run 2: MAX_OQ_DEPTH=4 admits gamma's child ---"
( cd "$WORK" && MAX_OQ_DEPTH=4 "${TSX_CMD[@]}" "$EXTRACTOR" --json ) >/dev/null 2>/dev/null
IDS2="$(python3 -c "import json;print('\n'.join(p['id'] for p in json.load(open('$WORK/.lean/research/problems.json'))))")"
assert_contains "gamma spawns child when cap raised to 4" "gamma-oq-01-oq-02-oq-03-oq-01" "$IDS2"
# delta (depth 4) is now AT cap 4 -> still no child.
if [[ "$IDS2" == *"delta-oq-01-oq-02-oq-03-oq-04-oq-01"* ]]; then
    echo "  FAIL: depth-4 proof spawned child at cap=4"; ((FAIL++))
else
    echo "  ok: depth-4 proof still capped at cap=4"; ((PASS++))
fi

echo ""
echo "Passed: $PASS  Failed: $FAIL"
[[ $FAIL -eq 0 ]]
