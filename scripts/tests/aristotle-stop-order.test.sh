#!/bin/bash
# Guards the load-bearing ordering in scripts/aristotle/launch-agent.sh
# stop_agent(): in-flight Aristotle job state must be persisted by
# salvage_jobs_file BEFORE the worktree is reclaimed by remove_own_worktree,
# or job state is lost (issue #25350, Phase 2b).
#
# Also asserts neither call leaks into the DRY_RUN early-return branch (a
# --dry-run --stop must touch nothing).
#
# Run: bash scripts/tests/aristotle-stop-order.test.sh
# Exits non-zero if any assertion fails.
set -u

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
LAUNCHER="$SCRIPT_DIR/../aristotle/launch-agent.sh"

PASS=0
FAIL=0

pass() { echo "  ok: $1"; ((PASS++)); }
fail() { echo "  FAIL: $1"; ((FAIL++)); }

# Extract the body of stop_agent(): from "stop_agent() {" up to the first line
# that is exactly "}".
stop_body="$(awk '
    /^stop_agent\(\) \{/ { capture=1; next }
    capture && /^\}$/ { capture=0 }
    capture { print }
' "$LAUNCHER")"

if [[ -z "$stop_body" ]]; then
    fail "could not locate stop_agent() body in $LAUNCHER"
    echo ""
    echo "PASS=$PASS FAIL=$FAIL"
    exit 1
fi

# 1) Both salvage and remove are present in stop_agent() as actual calls.
# Match invocation lines (token at start of a line, ignoring leading whitespace)
# so prose mentions inside `#` comments do not count.
salvage_line="$(grep -nE '^[[:space:]]*salvage_jobs_file([[:space:]]|$)' <<<"$stop_body" | head -n1 | cut -d: -f1)"
remove_line="$(grep -nE '^[[:space:]]*remove_own_worktree([[:space:]]|$)' <<<"$stop_body" | head -n1 | cut -d: -f1)"

if [[ -n "$salvage_line" ]]; then
    pass "stop_agent() calls salvage_jobs_file"
else
    fail "stop_agent() does not call salvage_jobs_file"
fi

if [[ -n "$remove_line" ]]; then
    pass "stop_agent() calls remove_own_worktree"
else
    fail "stop_agent() does not call remove_own_worktree"
fi

# 2) salvage runs BEFORE remove (load-bearing ordering).
if [[ -n "$salvage_line" && -n "$remove_line" ]]; then
    if (( salvage_line < remove_line )); then
        pass "salvage_jobs_file precedes remove_own_worktree (job state persisted first)"
    else
        fail "salvage_jobs_file must precede remove_own_worktree (got salvage@$salvage_line, remove@$remove_line)"
    fi
fi

# 3) Neither call appears in the DRY_RUN early-return branch. Extract the lines
# between the DRY_RUN guard and its `return`.
dry_body="$(awk '
    /if \[\[ "\$DRY_RUN" == "true" \]\]; then/ { capture=1; next }
    capture && /return/ { capture=0 }
    capture { print }
' <<<"$stop_body")"

if grep -qE '^[[:space:]]*(salvage_jobs_file|remove_own_worktree)([[:space:]]|$)' <<<"$dry_body"; then
    fail "DRY_RUN branch must NOT actually salvage or remove (a preview line is fine, an actual call is not)"
else
    pass "DRY_RUN branch does not invoke salvage/remove"
fi

# 4) The launcher sources the shared helper exactly once.
src_count="$(grep -cE '^source .*scripts/lib/worktree-cleanup\.sh' "$LAUNCHER")"
if [[ "$src_count" -eq 1 ]]; then
    pass "sources scripts/lib/worktree-cleanup.sh exactly once"
else
    fail "expected exactly one source of worktree-cleanup.sh, found $src_count"
fi

echo ""
echo "PASS=$PASS FAIL=$FAIL"
[[ "$FAIL" -eq 0 ]]
