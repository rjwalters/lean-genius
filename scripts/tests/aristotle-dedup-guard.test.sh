#!/bin/bash
# Guards the repeat-submission dedup guard in
# scripts/aristotle/find-candidates.sh (get_repeat_offender_files).
#
# Root cause (issue #43033): after research/aristotle-jobs.json tracking was
# lost, the existing "already submitted" filters (which key off the *current*
# status of the most recent job) had nothing to dedupe against, and the
# candidate queue re-served the same top files every cycle — 90 of 100
# recovered projects were duplicate submissions of just three files. This
# test verifies the independent repeat-offender backstop: a file submitted
# ARISTOTLE_DEDUP_MAX_ATTEMPTS+ times (any status, summed across all of
# jobs.json history) with no "integrated" job among them is excluded from
# candidate selection, regardless of what the status-based filters allow.
#
# Run: bash scripts/tests/aristotle-dedup-guard.test.sh
# Exits non-zero if any assertion fails.
set -u

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
FIND_CANDIDATES="$SCRIPT_DIR/../aristotle/find-candidates.sh"

PASS=0
FAIL=0

pass() { echo "  ok: $1"; ((PASS++)); }
fail() { echo "  FAIL: $1"; ((FAIL++)); }

TMPDIR_TEST="$(mktemp -d)"
trap 'rm -rf "$TMPDIR_TEST"' EXIT

JOBS_FILE="$TMPDIR_TEST/aristotle-jobs.json"

# Extract get_repeat_offender_files() so it can be sourced in isolation
# without pulling in main()'s side effects (it invokes `main` unconditionally
# at the bottom of the real script).
guard_src="$(awk '
    /^get_repeat_offender_files\(\) \{/ { capture=1 }
    capture { print }
    capture && /^\}$/ { exit }
' "$FIND_CANDIDATES")"

if [[ -z "$guard_src" ]]; then
    fail "could not locate get_repeat_offender_files() body in $FIND_CANDIDATES"
    echo ""
    echo "PASS=$PASS FAIL=$FAIL"
    exit 1
fi

run_guard() {
    local max="$1"
    (
        ARISTOTLE_DEDUP_MAX_ATTEMPTS="$max"
        eval "$guard_src"
        get_repeat_offender_files
    )
}

# 1) A file submitted 3+ times with no "integrated" job is a repeat offender.
cat > "$JOBS_FILE" <<'EOF'
{"jobs": [
  {"file": "proofs/Proofs/ChebyshevBounds.lean", "status": "failed"},
  {"file": "proofs/Proofs/ChebyshevBounds.lean", "status": "expired"},
  {"file": "proofs/Proofs/ChebyshevBounds.lean", "status": "submitted"}
]}
EOF
out="$(run_guard 3)"
if grep -qx "ChebyshevBounds" <<<"$out"; then
    pass "3 non-integrated submissions -> flagged as repeat offender"
else
    fail "3 non-integrated submissions should be flagged (got: $out)"
fi

# 2) A file submitted 3+ times that eventually reached "integrated" is NOT
#    excluded — the whole point of the guard is stopping unproductive churn,
#    not permanently banning files that did eventually succeed.
cat > "$JOBS_FILE" <<'EOF'
{"jobs": [
  {"file": "proofs/Proofs/SumOfOddsStatementOnly.lean", "status": "failed"},
  {"file": "proofs/Proofs/SumOfOddsStatementOnly.lean", "status": "expired"},
  {"file": "proofs/Proofs/SumOfOddsStatementOnly.lean", "status": "integrated"}
]}
EOF
out="$(run_guard 3)"
if grep -qx "SumOfOddsStatementOnly" <<<"$out"; then
    fail "a file that eventually integrated must not be a permanent repeat offender (got: $out)"
else
    pass "file with an 'integrated' job in its history is never flagged"
fi

# 3) Below the threshold: 2 submissions with max=3 should not be flagged.
cat > "$JOBS_FILE" <<'EOF'
{"jobs": [
  {"file": "proofs/Proofs/SchroederBernstein.lean", "status": "failed"},
  {"file": "proofs/Proofs/SchroederBernstein.lean", "status": "expired"}
]}
EOF
out="$(run_guard 3)"
if [[ -z "$out" ]]; then
    pass "2 submissions below default threshold (3) -> not flagged"
else
    fail "2 submissions should be below threshold (got: $out)"
fi

# 4) ARISTOTLE_DEDUP_MAX_ATTEMPTS is configurable: lowering it to 2 flags the
#    same file from case 3.
out="$(run_guard 2)"
if grep -qx "SchroederBernstein" <<<"$out"; then
    pass "ARISTOTLE_DEDUP_MAX_ATTEMPTS=2 flags a file at exactly 2 submissions"
else
    fail "ARISTOTLE_DEDUP_MAX_ATTEMPTS=2 should flag 2 submissions (got: $out)"
fi

# 5) Missing jobs.json -> no repeat offenders, no error.
rm -f "$JOBS_FILE"
out="$(run_guard 3)"
if [[ -z "$out" ]]; then
    pass "missing jobs.json -> empty result, no error"
else
    fail "missing jobs.json should produce empty output (got: $out)"
fi

echo ""
echo "PASS=$PASS FAIL=$FAIL"
[[ "$FAIL" -eq 0 ]]
