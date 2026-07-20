#!/bin/bash
# Integration tests for the OQ-recursion-depth cap in
# scripts/research/claim-problem.sh:claim_random_problem() (issue #39827).
#
# Drives the REAL shipped CLI (`claim-random`) inside throwaway git sandboxes so
# find_repo_root resolves entirely into mktemp dirs and no shared coordination
# state is touched. Asserts the three policy behaviors:
#
#   1. Over-cap exclusion: chains deeper than the cap are never selected and are
#      reported as excluded/saturated.
#   2. Breadth preference: when a shallow problem and an at-cap chain are both
#      available, the shallow one is selected and the at-cap one is deprioritized.
#   3. Fallback: when ONLY at-cap chains are available, one is still selected
#      (with a "falling back" notice) rather than starving the pipeline.
#
# Run: bash scripts/tests/claim-problem-oq-cap.test.sh
# Exits non-zero if any assertion fails.
set -u

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
CLAIM_SCRIPT="$SCRIPT_DIR/../research/claim-problem.sh"

PASS=0; FAIL=0
assert_eq() { # <desc> <expected> <actual>
    if [[ "$3" == "$2" ]]; then echo "  ok: $1 -> $3"; ((PASS++)); else echo "  FAIL: $1 expected '$2' got '$3'"; ((FAIL++)); fi
}
assert_contains() { # <desc> <needle> <haystack>
    if [[ "$3" == *"$2"* ]]; then echo "  ok: $1"; ((PASS++)); else echo "  FAIL: $1 (missing '$2')"; ((FAIL++)); fi
}
assert_not_contains() { # <desc> <needle> <haystack>
    if [[ "$3" != *"$2"* ]]; then echo "  ok: $1"; ((PASS++)); else echo "  FAIL: $1 (should not contain '$2')"; ((FAIL++)); fi
}

if [[ ! -f "$CLAIM_SCRIPT" ]]; then
    echo "FAIL: claim-problem.sh not found at $CLAIM_SCRIPT" >&2
    exit 1
fi

# new_sandbox <pool-json> -> echoes sandbox path
new_sandbox() {
    local pool="$1" sb
    sb="$(mktemp -d)"
    mkdir -p "$sb/research/claims" "$sb/.lean/state" \
             "$sb/.lean/config" "$sb/src/data/research/problems" "$sb/.loom/locks"
    # Ship the same policy config the repo tracks so the cap resolves to 3.
    printf '{"maxOqDepth": 3}\n' > "$sb/.lean/config/oq-policy.json"
    # Make the shared lib importable at $sb/scripts/lib/oq-policy.sh.
    mkdir -p "$sb/scripts/lib"
    cp "$SCRIPT_DIR/../lib/oq-policy.sh" "$sb/scripts/lib/oq-policy.sh"
    printf '%s\n' "$pool" > "$sb/.lean/state/candidate-pool.json"
    git -C "$sb" init -q
    echo "$sb"
}

# run_claim_random <sandbox> -> populates OUT (stdout) and ERR (stderr), RC
run_claim_random() {
    local sb="$1"
    OUT="$( cd "$sb" && MAX_OQ_DEPTH=3 RESEARCHER_ID=test-agent bash "$CLAIM_SCRIPT" claim-random 2>/tmp/oq_err_$$ )"
    RC=$?
    ERR="$(cat /tmp/oq_err_$$ 2>/dev/null)"
    rm -f /tmp/oq_err_$$
}

echo "--- Case 1: over-cap chain is excluded, never re-served ---"
POOL='{"candidates":[{"id":"foo-oq-01-oq-02-oq-03-oq-04","status":"available"}]}'
SB="$(new_sandbox "$POOL")"
run_claim_random "$SB"
assert_eq "no claimable problem (only over-cap present)" "1" "$RC"
assert_contains "excluded saturated chain logged" "excluded 1 saturated chain" "$ERR"
assert_not_contains "over-cap id never selected" "Selected foo-oq-01-oq-02-oq-03-oq-04" "$OUT"
rm -rf "$SB"

echo "--- Case 2: breadth preference (shallow beats at-cap) ---"
POOL='{"candidates":[
  {"id":"shallow-problem","status":"available"},
  {"id":"deep-oq-01-oq-02-oq-03","status":"available"}
]}'
SB="$(new_sandbox "$POOL")"
run_claim_random "$SB"
assert_eq "a problem was claimed" "0" "$RC"
assert_contains "shallow problem selected" "Selected shallow-problem" "$OUT"
assert_contains "at-cap chain deprioritized" "deprioritized 1 at-cap chain" "$ERR"
rm -rf "$SB"

echo "--- Case 3: fallback to at-cap when nothing shallower exists ---"
POOL='{"candidates":[{"id":"only-oq-01-oq-02-oq-03","status":"available"}]}'
SB="$(new_sandbox "$POOL")"
run_claim_random "$SB"
assert_eq "at-cap chain claimed as fallback" "0" "$RC"
assert_contains "at-cap chain selected" "Selected only-oq-01-oq-02-oq-03" "$OUT"
assert_contains "fallback logged" "falling back to 1 at-cap chain" "$ERR"
rm -rf "$SB"

echo "--- Case 4: raising the cap admits a deeper chain ---"
# Same pool as Case 1 but MAX_OQ_DEPTH=4 -> depth-4 chain is now at-cap (servable).
POOL='{"candidates":[{"id":"foo-oq-01-oq-02-oq-03-oq-04","status":"available"}]}'
SB="$(new_sandbox "$POOL")"
OUT="$( cd "$SB" && MAX_OQ_DEPTH=4 RESEARCHER_ID=test-agent bash "$CLAIM_SCRIPT" claim-random 2>/tmp/oq_err_$$ )"
RC=$?; ERR="$(cat /tmp/oq_err_$$ 2>/dev/null)"; rm -f /tmp/oq_err_$$
assert_eq "depth-4 chain claimable at cap=4" "0" "$RC"
assert_contains "depth-4 chain selected at cap=4" "Selected foo-oq-01-oq-02-oq-03-oq-04" "$OUT"
rm -rf "$SB"

echo ""
echo "Passed: $PASS  Failed: $FAIL"
[[ $FAIL -eq 0 ]]
