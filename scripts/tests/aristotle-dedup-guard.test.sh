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

# Extract individual functions so they can be sourced in isolation without
# pulling in main()'s side effects (the real script invokes `main`
# unconditionally at the bottom).
extract_fn() {
    awk -v fn="$1" '
        $0 ~ "^" fn "\\(\\) \\{" { capture=1 }
        capture { print }
        capture && /^\}$/ { exit }
    ' "$FIND_CANDIDATES"
}

guard_src="$(extract_fn get_repeat_offender_files)"
log_src="$(extract_fn dedup_log)"
count_src="$(extract_fn count_matches)"
analyze_src="$(extract_fn analyze_file)"
collect_src="$(extract_fn collect_candidates)"

for pair in "guard_src:get_repeat_offender_files" "log_src:dedup_log" \
            "count_src:count_matches" "analyze_src:analyze_file" \
            "collect_src:collect_candidates"; do
    var="${pair%%:*}"
    fn="${pair##*:}"
    if [[ -z "${!var}" ]]; then
        fail "could not locate ${fn}() body in $FIND_CANDIDATES"
        echo ""
        echo "PASS=$PASS FAIL=$FAIL"
        exit 1
    fi
done

# PROJECT_ROOT is where the guard resolves a job's relative `.file` path to
# decide whether the file has been modified since its last submission. Default
# to an empty sandbox so files referenced by fixtures do not exist unless a
# test deliberately creates them.
FAKE_ROOT="$TMPDIR_TEST/root"
mkdir -p "$FAKE_ROOT/proofs/Proofs"

run_guard() {
    local max="$1"
    local project_root="${2:-$TMPDIR_TEST/empty-root}"
    (
        ARISTOTLE_DEDUP_MAX_ATTEMPTS="$max"
        ARISTOTLE_QUIET="${ARISTOTLE_QUIET:-false}"
        # shellcheck disable=SC2034  # read by the eval'd function bodies below
        PROJECT_ROOT="$project_root"
        eval "$log_src"
        eval "$guard_src"
        get_repeat_offender_files
    )
}

# Exercises the real collect_candidates() — including its `shift 4` and the
# positional order of the three filter lists — rather than the guard function
# in isolation. Args: tier submitted blocked offenders file...
run_collect() {
    (
        ARISTOTLE_DEDUP_MAX_ATTEMPTS="${ARISTOTLE_DEDUP_MAX_ATTEMPTS:-3}"
        ARISTOTLE_QUIET="${ARISTOTLE_QUIET:-false}"
        eval "$log_src"
        eval "$count_src"
        eval "$analyze_src"
        eval "$collect_src"
        collect_candidates "$@"
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

# 6) THE ESCAPE HATCH (issue #43033 review blocker): a file repaired after N
#    failed attempts — mtime newer than its last recorded submission — is
#    eligible again. Without this, crossing the threshold excluded a file
#    permanently and silently defeated get_blocked_files()' own mtime escape.
cat > "$JOBS_FILE" <<'EOF'
{"jobs": [
  {"file": "proofs/Proofs/RepairedTarget.lean", "status": "failed", "submitted": "2026-01-01T00:00:00Z"},
  {"file": "proofs/Proofs/RepairedTarget.lean", "status": "failed", "submitted": "2026-01-02T00:00:00Z"},
  {"file": "proofs/Proofs/RepairedTarget.lean", "status": "expired", "submitted": "2026-01-03T00:00:00Z"}
]}
EOF
REPAIRED="$FAKE_ROOT/proofs/Proofs/RepairedTarget.lean"
printf 'theorem t : 1 = 1 := by sorry\n' > "$REPAIRED"
touch -t 202601040000 "$REPAIRED"   # a day after the last submission
out="$(run_guard 3 "$FAKE_ROOT" 2>/dev/null)"
if [[ -z "$out" ]]; then
    pass "repaired after 3 attempts (mtime > last_submitted) -> eligible again"
else
    fail "a file modified since its last submission must not be a repeat offender (got: $out)"
fi

# 7) ... and the exclusion still holds while the file is untouched.
touch -t 202512310000 "$REPAIRED"   # older than the last submission
out="$(run_guard 3 "$FAKE_ROOT" 2>/dev/null)"
if grep -qx "RepairedTarget" <<<"$out"; then
    pass "unmodified since last submission -> still excluded"
else
    fail "an unmodified repeat offender must stay excluded (got: $out)"
fi

# 8) Fails CLOSED when "modified since" cannot be established: the
#    `"submitted": "unknown"` records recovered during the #43006 backlog
#    recovery carry no parseable timestamp, so a freshly-touched file stays
#    excluded rather than disabling the guard for the corrupt-history case it
#    exists to backstop.
cat > "$JOBS_FILE" <<'EOF'
{"jobs": [
  {"file": "proofs/Proofs/RepairedTarget.lean", "status": "archived", "submitted": "unknown"},
  {"file": "proofs/Proofs/RepairedTarget.lean", "status": "archived", "submitted": "unknown"},
  {"file": "proofs/Proofs/RepairedTarget.lean", "status": "archived", "submitted": "unknown"}
]}
EOF
touch "$REPAIRED"
out="$(run_guard 3 "$FAKE_ROOT" 2>/dev/null)"
if grep -qx "RepairedTarget" <<<"$out"; then
    pass "unparseable 'submitted' timestamp -> fails closed, still excluded"
else
    fail "unparseable timestamp must not un-exclude an offender (got: $out)"
fi

# 9) Un-exclusion is attributable: the escape hatch logs one line to stderr,
#    and stdout stays machine-readable.
cat > "$JOBS_FILE" <<'EOF'
{"jobs": [
  {"file": "proofs/Proofs/RepairedTarget.lean", "status": "failed", "submitted": "2026-01-01T00:00:00Z"},
  {"file": "proofs/Proofs/RepairedTarget.lean", "status": "failed", "submitted": "2026-01-02T00:00:00Z"},
  {"file": "proofs/Proofs/RepairedTarget.lean", "status": "failed", "submitted": "2026-01-03T00:00:00Z"}
]}
EOF
touch -t 202601040000 "$REPAIRED"
err_file="$TMPDIR_TEST/guard.err"
out="$(run_guard 3 "$FAKE_ROOT" 2>"$err_file")"
if [[ -z "$out" ]] && grep -q "RepairedTarget" "$err_file" && grep -q "exclusion lifted" "$err_file"; then
    pass "escape hatch logs a one-line notice to stderr, not stdout"
else
    fail "escape hatch should log to stderr (stdout: $out / stderr: $(cat "$err_file"))"
fi

# --------------------------------------------------------------------------
# Call-site wiring smoke tests: collect_candidates() takes the offender list as
# its 4th positional arg and then `shift 4`s. A mis-wired call site (or a
# forgotten shift) would silently corrupt the `files` array, so exercise the
# real function rather than the guard alone.
# --------------------------------------------------------------------------
PROBE="$FAKE_ROOT/proofs/Proofs/WiringProbe.lean"
printf 'theorem probe : 1 = 1 := by sorry\n' > "$PROBE"

# 10) With all three filter lists empty, the probe file is emitted (proving the
#     `shift 4` left the file arguments intact).
out="$(run_collect 1 "" "" "" "$PROBE" 2>/dev/null)"
if [[ "$out" == WiringProbe\|* && "${out##*|}" == "1" ]]; then
    pass "collect_candidates shift 4 -> file args intact, tier preserved"
else
    fail "collect_candidates should emit 'WiringProbe|...|1' (got: $out)"
fi

# 11) Each filter list is honored in its own positional slot.
wiring_ok=true
for slot in 2 3 4; do
    args=(1 "" "" "")
    args[$((slot - 1))]="WiringProbe"
    if [[ -n "$(run_collect "${args[@]}" "$PROBE" 2>/dev/null)" ]]; then
        wiring_ok=false
        fail "collect_candidates ignored its filter list in positional slot $slot"
    fi
done
if [[ "$wiring_ok" == true ]]; then
    pass "submitted/blocked/repeat-offender lists each filter from their own slot"
fi

# 12) The repeat-offender skip is no longer silent.
err_file="$TMPDIR_TEST/collect.err"
out="$(run_collect 1 "" "" "WiringProbe" "$PROBE" 2>"$err_file")"
if [[ -z "$out" ]] && grep -q "WiringProbe" "$err_file" && grep -q "dedup guard" "$err_file"; then
    pass "repeat-offender skip emits an attributable notice on stderr"
else
    fail "repeat-offender skip should log to stderr (stdout: $out / stderr: $(cat "$err_file"))"
fi

# 13) ARISTOTLE_QUIET=true suppresses the notices (stdout behavior unchanged).
err_file="$TMPDIR_TEST/collect-quiet.err"
out="$(ARISTOTLE_QUIET=true run_collect 1 "" "" "WiringProbe" "$PROBE" 2>"$err_file")"
if [[ -z "$out" && ! -s "$err_file" ]]; then
    pass "ARISTOTLE_QUIET=true silences dedup notices"
else
    fail "ARISTOTLE_QUIET=true should silence notices (stderr: $(cat "$err_file"))"
fi

# 14) All three collect_candidates call sites pass the offender list, and the
#     function shifts past exactly four leading positionals.
call_sites=$(grep -c 'collect_candidates [0-9] "\$submitted_files" "\$blocked_files" "\$repeat_offender_files" "\${tier[0-9]_files\[@\]}"' "$FIND_CANDIDATES" || true)
shift_count=$(grep -c '^    shift 4$' "$FIND_CANDIDATES" || true)
if [[ "$call_sites" -eq 3 && "$shift_count" -eq 1 ]]; then
    pass "all 3 collect_candidates call sites pass the offender list; shift 4 present"
else
    fail "expected 3 wired call sites and one 'shift 4' (got $call_sites call sites, $shift_count shifts)"
fi

echo ""
echo "PASS=$PASS FAIL=$FAIL"
[[ "$FAIL" -eq 0 ]]
