#!/bin/bash
# Concurrency harness for the stale-reclaim race in
# scripts/research/claim-problem.sh:claim_problem() (issue #35319).
#
# Bug (pre-fix): the stale-reclaim retry path was
#   is_claim_expired -> rm -rf "$lock_dir" -> retry mkdir "$lock_dir"
# with no lock around the *sequence*. Two agents that both observe an EXPIRED
# claim can interleave so agent B's `rm -rf` wipes agent A's freshly-created
# lock dir, letting B's retry mkdir also succeed — both agents then believe
# they exclusively hold the same claim (duplicate work / duplicate PRs).
#
# The fix wraps the whole reclaim decision behind a per-claim advisory lock
# (acquire_generic_lock / release_generic_lock, mkdir-fallback on macOS where
# flock is unavailable), so exactly one agent can reclaim-and-reclaim while the
# other backs off cleanly with "already claimed".
#
# This test exercises the REAL script (not a reimplementation) two ways:
#
#   PART A (deterministic, in-process): source the real functions with all
#   shared state (CLAIMS_DIR / POOL_FILE / LOCKS_DIR / PROBLEMS_DIR) redirected
#   into a mktemp sandbox, then launch two background agents that call the real
#   claim_problem(). A file barrier released from INSIDE is_claim_expired forces
#   both agents to enter the stale-reclaim window simultaneously, so the buggy
#   interleaving is provoked on essentially every run. Asserts a single winner
#   and a clean loser.
#
#   PART B (end-to-end, looped): drive the real CLI as two barrier-synchronized
#   subprocesses over many iterations, catching any residual race and confirming
#   the normal exit statuses / stderr messages of the shipped command.
#
# Plus regression coverage for the normal claim / release / expiry flow.
#
# Run: bash scripts/tests/claim-problem-reclaim-race.test.sh
# Exits non-zero if any assertion fails.
set -u

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
CLAIM_SCRIPT="$SCRIPT_DIR/../research/claim-problem.sh"

PASS=0
FAIL=0
assert() { # <desc> <expected> <actual>
    if [[ "$3" == "$2" ]]; then
        echo "  ok: $1 -> $3"
        ((PASS++))
    else
        echo "  FAIL: $1 expected [$2] got [$3]"
        ((FAIL++))
    fi
}
assert_true() { # <desc> <0-or-nonzero>
    if [[ "$2" == "0" ]]; then
        echo "  ok: $1"
        ((PASS++))
    else
        echo "  FAIL: $1"
        ((FAIL++))
    fi
}

if [[ ! -f "$CLAIM_SCRIPT" ]]; then
    echo "FAIL: claim-problem.sh not found at $CLAIM_SCRIPT" >&2
    exit 1
fi

PROBLEM_ID="sandbox-fake-problem"

# count_matches <pattern> <file> : emit exactly one integer (0 if no match /
# missing file). grep -c prints "0" AND exits non-zero on no-match, which breaks
# `$(... || echo 0)` (yields "0\n0"); this wrapper normalizes that.
count_matches() {
    local n
    n=$(grep -c "$1" "$2" 2>/dev/null) || n=0
    [[ "$n" =~ ^[0-9]+$ ]] || n=0
    echo "$n"
}

# -----------------------------------------------------------------------------
# Sandbox factory: a throwaway git repo root so the real script's
# find_repo_root resolves entirely inside our mktemp dir and touches no shared
# coordination state.
# -----------------------------------------------------------------------------
new_sandbox() { # -> echoes sandbox path
    local sb
    sb="$(mktemp -d)"
    mkdir -p "$sb/research/claims" "$sb/.lean/state" \
             "$sb/src/data/research/problems" "$sb/.loom/locks"
    cat > "$sb/.lean/state/candidate-pool.json" <<EOF
{ "candidates": [ { "id": "$PROBLEM_ID", "status": "available" } ] }
EOF
    git -C "$sb" init -q
    echo "$sb"
}

# Write an EXPIRED claim (held by "ghost-agent") into a sandbox's claims dir.
seed_expired_claim() { # <sandbox>
    local sb="$1"
    local lock_dir="$sb/research/claims/${PROBLEM_ID}.lock"
    local claim_file="$sb/research/claims/${PROBLEM_ID}.json"
    mkdir -p "$lock_dir"
    cat > "$claim_file" <<EOF
{
  "problem_id": "$PROBLEM_ID",
  "agent_id": "ghost-agent",
  "claimed_at": "2000-01-01T00:00:00Z",
  "expires_at": "2000-01-01T01:00:00Z",
  "ttl_minutes": 180,
  "knowledge_score": 0,
  "knowledge_tier": "EMPTY"
}
EOF
}

# =============================================================================
# PART A: deterministic in-process race (arrival-ordered barrier).
# =============================================================================
# This reproduces the EXACT interleaving from the issue (curator steps 3-8),
# not merely a hopeful "release both and pray for a scheduler collision" — the
# unguarded rm/mkdir window is too small to hit reliably by timing alone.
#
# Both agents run the REAL claim_problem(). We wrap is_claim_expired so that the
# FIRST agent to reach the reclaim decision is sequenced ahead of the SECOND:
#
#   - Arrival order is assigned atomically (mkdir on a shared token dir).
#   - The 1st arrival proceeds immediately: it runs rm -rf + mkdir + write and
#     fully (re)claims (curator steps 5-6), then its process exits.
#   - The 2nd arrival BLOCKS at the expiry decision until the 1st agent's
#     process has fully exited (a completion marker), THEN proceeds into its own
#     rm/mkdir window (steps 7-8) with the 1st agent's claim already live.
#
# With the BUGGY code the 2nd agent is already committed past its own expiry
# read, so it unconditionally rm -rf's the 1st agent's fresh lock and mkdir's
# its own — two winners, the 1st agent's claim_file clobbered. With the FIX the
# 2nd agent re-checks under the per-claim reclaim lock, sees the now-live claim,
# and backs off cleanly with "already claimed".
#
# Note: which physical agent (A or B) arrives first is not fixed — the barrier
# sequences by ARRIVAL, so the test is robust to lock-acquisition order in the
# fixed code (where the 2nd agent can only reach is_claim_expired after the 1st
# releases the reclaim lock).
#
# The wrapper delegates to the sourced _real_is_claim_expired so it only gates,
# never alters the expiry decision.
run_agent_inproc() { # <sandbox> <agent-id> <coord-dir> <outfile>
    local sb="$1" agent="$2" coord="$3" outfile="$4"
    (
        cd "$sb" || exit 99
        set -uo pipefail
        # shellcheck disable=SC1090
        source "$CLAIM_SCRIPT" help >/dev/null 2>&1

        # Re-point AGENT_ID (script read RESEARCHER_ID at source time). Consumed
        # by the sourced claim_problem, so shellcheck's unused warning is a false
        # positive here.
        # shellcheck disable=SC2034
        AGENT_ID="$agent"

        # Preserve real expiry logic, then wrap it with an arrival-ordered gate.
        # is_claim_expired is invoked indirectly by the sourced claim_problem.
        eval "_real_is_claim_expired() $(declare -f is_claim_expired | sed '1d')"
        __arrived_once=0
        # shellcheck disable=SC2329
        is_claim_expired() {
            local result=1
            _real_is_claim_expired "$@" && result=0
            # Only the FIRST is_claim_expired call per agent participates in the
            # ordering (the fixed code may call it twice under the reclaim lock;
            # subsequent calls must not re-block).
            if [[ "$__arrived_once" -eq 0 ]]; then
                __arrived_once=1
                # Claim an arrival slot atomically. mkdir succeeds for exactly
                # one agent as "first".
                if mkdir "$coord/first" 2>/dev/null; then
                    : # first arrival: proceed immediately
                else
                    # second arrival: wait until the first agent has fully
                    # exited (marker) before entering the rm/mkdir window.
                    while [[ ! -f "$coord/first-done" ]]; do :; done
                fi
            fi
            return "$result"
        }

        if claim_problem "$PROBLEM_ID" > "$outfile" 2>&1; then
            echo "EXIT:0" >> "$outfile"
        else
            echo "EXIT:$?" >> "$outfile"
        fi
        # Announce exit so the coordinator can publish first-done and release
        # the second arrival into its rm/mkdir window.
        echo "$agent" >> "$coord/exited"
    ) &
}

echo "== PART A: deterministic in-process concurrent stale reclaim (looped) =="
A_ITER=15
A_double=0; A_crash=0; A_mismatch=0; A_orphan=0
for i in $(seq 1 "$A_ITER"); do
    sb="$(new_sandbox)"
    seed_expired_claim "$sb"
    coord="$sb/coord"; mkdir -p "$coord"
    outA="$sb/outA"; outB="$sb/outB"

    run_agent_inproc "$sb" "agentA-$i" "$coord" "$outA"
    pidA=$!
    run_agent_inproc "$sb" "agentB-$i" "$coord" "$outB"
    pidB=$!

    # The coordinator drives the sequencing: as soon as ONE agent has exited
    # (the first arrival, which proceeds without blocking), publish first-done
    # so the second arrival may enter its rm/mkdir window.
    for _ in $(seq 1 500); do
        [[ -s "$coord/exited" ]] && break
        sleep 0.02
    done
    touch "$coord/first-done"

    wait "$pidA" 2>/dev/null || true
    wait "$pidB" 2>/dev/null || true

    winsA=$(count_matches "Claimed $PROBLEM_ID by agentA-$i" "$outA")
    winsB=$(count_matches "Claimed $PROBLEM_ID by agentB-$i" "$outB")
    total_wins=$(( winsA + winsB ))
    losesA=$(count_matches "already claimed" "$outA")
    losesB=$(count_matches "already claimed" "$outB")
    total_loses=$(( losesA + losesB ))

    if [[ "$total_wins" -ne 1 ]]; then
        A_double=1
        echo "  [A iter $i] BAD: $total_wins winners (expected 1)"
        echo "    --- A ---"; cat "$outA"; echo "    --- B ---"; cat "$outB"
    fi
    if [[ "$total_wins" -eq 1 && "$total_loses" -ne 1 ]]; then
        A_crash=1
        echo "  [A iter $i] BAD: winner=1 but loser did not report 'already claimed'"
        echo "    --- A ---"; cat "$outA"; echo "    --- B ---"; cat "$outB"
    fi
    # Loser must exit non-zero cleanly under set -euo pipefail.
    [[ "$winsA" -eq 0 && "$(grep -o 'EXIT:[0-9]*' "$outA" | tail -1)" == "EXIT:0" ]] && { A_crash=1; echo "  [A iter $i] BAD: loser A exited 0"; }
    [[ "$winsB" -eq 0 && "$(grep -o 'EXIT:[0-9]*' "$outB" | tail -1)" == "EXIT:0" ]] && { A_crash=1; echo "  [A iter $i] BAD: loser B exited 0"; }

    if [[ "$total_wins" -eq 1 ]]; then
        persisted=$(jq -r '.agent_id' "$sb/research/claims/${PROBLEM_ID}.json" 2>/dev/null || echo MISSING)
        expected=""; [[ "$winsA" -eq 1 ]] && expected="agentA-$i"; [[ "$winsB" -eq 1 ]] && expected="agentB-$i"
        [[ "$persisted" != "$expected" ]] && { A_mismatch=1; echo "  [A iter $i] BAD: persisted=$persisted winner=$expected"; }
    fi
    [[ -d "$sb/research/claims/${PROBLEM_ID}.lock.reclaim-lock.d" ]] && { A_orphan=1; echo "  [A iter $i] BAD: orphaned reclaim-lock dir"; }

    rm -rf "$sb"
done
assert "PART A: single winner (no double-claim) across $A_ITER iterations" "0" "$A_double"
assert "PART A: loser backs off cleanly across $A_ITER iterations" "0" "$A_crash"
assert "PART A: persisted claim matches winner across $A_ITER iterations" "0" "$A_mismatch"
assert "PART A: no orphaned reclaim-lock dir across $A_ITER iterations" "0" "$A_orphan"

# =============================================================================
# Shared end-to-end CLI runner for PART B + regressions.
# =============================================================================
# run_claim <sandbox> <agent-id> <outfile> : runs the shipped CLI, appends the
# exit status as the final line of <outfile>.
run_claim() {
    local sb="$1" agent="$2" outfile="$3"
    (
        cd "$sb" || exit 99
        RESEARCHER_ID="$agent" bash "$CLAIM_SCRIPT" claim "$PROBLEM_ID"
    ) > "$outfile" 2>&1
    echo "$?" >> "$outfile"
}

# =============================================================================
# Regression 1: fresh claim / duplicate rejection / release / re-claim.
# =============================================================================
echo "== Regression: fresh claim / release / re-claim =="
sb="$(new_sandbox)"; out="$sb/out"
run_claim "$sb" "agent-fresh" "$out"
assert "fresh claim exit status" "0" "$(tail -n1 "$out")"
grep -q "Claimed $PROBLEM_ID by agent-fresh" "$out"; assert_true "fresh claim prints Claimed by winner" "$?"
assert_true "claim file exists after fresh claim" "$([[ -f "$sb/research/claims/${PROBLEM_ID}.json" ]] && echo 0 || echo 1)"

run_claim "$sb" "agent-second" "$out"
assert "second claim on live claim exit status" "1" "$(tail -n1 "$out")"
grep -q "already claimed" "$out"; assert_true "second claim on live claim reports already claimed" "$?"

( cd "$sb" && RESEARCHER_ID=agent-fresh bash "$CLAIM_SCRIPT" release "$PROBLEM_ID" ) >/dev/null 2>&1
assert_true "release removes lock dir" "$([[ ! -d "$sb/research/claims/${PROBLEM_ID}.lock" ]] && echo 0 || echo 1)"
run_claim "$sb" "agent-third" "$out"
grep -q "Claimed $PROBLEM_ID by agent-third" "$out"; assert_true "re-claim after release succeeds" "$?"
rm -rf "$sb"

# =============================================================================
# Regression 2: single-agent stale reclaim (no contention).
# =============================================================================
echo "== Regression: single-agent stale reclaim =="
sb="$(new_sandbox)"; seed_expired_claim "$sb"; out="$sb/out"
run_claim "$sb" "agent-reclaimer" "$out"
assert "single stale reclaim exit status" "0" "$(tail -n1 "$out")"
grep -q "Stale claim detected, reclaiming" "$out"; assert_true "single stale reclaim announces reclaim" "$?"
grep -q "Claimed $PROBLEM_ID by agent-reclaimer" "$out"; assert_true "single stale reclaim wins the claim" "$?"
assert "single stale reclaim persists winner agent_id" "agent-reclaimer" \
    "$(jq -r '.agent_id' "$sb/research/claims/${PROBLEM_ID}.json")"
assert_true "no orphaned reclaim-lock dir after single reclaim" \
    "$([[ ! -d "$sb/research/claims/${PROBLEM_ID}.lock.reclaim-lock.d" ]] && echo 0 || echo 1)"
rm -rf "$sb"

# =============================================================================
# PART B: end-to-end concurrent stale reclaim via the shipped CLI (looped).
# =============================================================================
echo "== PART B: end-to-end concurrent stale reclaim via CLI (looped) =="
B_ITER=20
B_double=0; B_crash=0; B_mismatch=0; B_orphan=0
for i in $(seq 1 "$B_ITER"); do
    sb="$(new_sandbox)"; seed_expired_claim "$sb"
    outA="$sb/outA"; outB="$sb/outB"; barrier="$sb/barrier"

    ( while [[ ! -f "$barrier" ]]; do :; done; run_claim "$sb" "agentA-$i" "$outA" ) & pidA=$!
    ( while [[ ! -f "$barrier" ]]; do :; done; run_claim "$sb" "agentB-$i" "$outB" ) & pidB=$!
    touch "$barrier"
    wait "$pidA"; wait "$pidB"

    winsA=$(count_matches "Claimed $PROBLEM_ID by agentA-$i" "$outA")
    winsB=$(count_matches "Claimed $PROBLEM_ID by agentB-$i" "$outB")
    total_wins=$(( winsA + winsB ))
    total_loses=$(( $(count_matches "already claimed" "$outA") + $(count_matches "already claimed" "$outB") ))
    statusA=$(tail -n1 "$outA"); statusB=$(tail -n1 "$outB")

    [[ "$total_wins" -ne 1 ]] && { B_double=1; echo "  [B iter $i] BAD: $total_wins winners"; echo "  A:"; cat "$outA"; echo "  B:"; cat "$outB"; }
    [[ "$total_wins" -eq 1 && "$total_loses" -ne 1 ]] && { B_crash=1; echo "  [B iter $i] BAD: loser did not report already claimed"; }
    [[ "$winsA" -eq 1 && "$statusA" != "0" ]] && { B_crash=1; echo "  [B iter $i] BAD: winner A exit $statusA"; }
    [[ "$winsB" -eq 1 && "$statusB" != "0" ]] && { B_crash=1; echo "  [B iter $i] BAD: winner B exit $statusB"; }
    [[ "$winsA" -eq 0 && "$statusA" != "1" ]] && { B_crash=1; echo "  [B iter $i] BAD: loser A exit $statusA"; }
    [[ "$winsB" -eq 0 && "$statusB" != "1" ]] && { B_crash=1; echo "  [B iter $i] BAD: loser B exit $statusB"; }

    if [[ "$total_wins" -eq 1 ]]; then
        persisted=$(jq -r '.agent_id' "$sb/research/claims/${PROBLEM_ID}.json" 2>/dev/null || echo MISSING)
        expected=""; [[ "$winsA" -eq 1 ]] && expected="agentA-$i"; [[ "$winsB" -eq 1 ]] && expected="agentB-$i"
        [[ "$persisted" != "$expected" ]] && { B_mismatch=1; echo "  [B iter $i] BAD: persisted=$persisted winner=$expected"; }
    fi
    [[ -d "$sb/research/claims/${PROBLEM_ID}.lock.reclaim-lock.d" ]] && { B_orphan=1; echo "  [B iter $i] BAD: orphaned reclaim-lock dir"; }
    rm -rf "$sb"
done
assert "PART B: single winner (no double-claim) across $B_ITER iterations" "0" "$B_double"
assert "PART B: loser backs off cleanly across $B_ITER iterations" "0" "$B_crash"
assert "PART B: persisted claim matches winner across $B_ITER iterations" "0" "$B_mismatch"
assert "PART B: no orphaned reclaim-lock dir across $B_ITER iterations" "0" "$B_orphan"

echo ""
echo "PASS=$PASS FAIL=$FAIL"
[[ "$FAIL" -eq 0 ]]
