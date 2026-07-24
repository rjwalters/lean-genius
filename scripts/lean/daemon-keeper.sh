#!/usr/bin/env bash
#
# daemon-keeper.sh — supervise the Lean Genius supervisor.
#
# The monitoring daemon (`launch.sh daemon`) runs under `set -euo pipefail`, so
# any unguarded non-zero exit in its ~60s loop (a transient git/tmux/jq/network
# failure, a `grep` with no match, an arithmetic expansion to 0, …) terminates
# the whole process. When that happens the agent tmux sessions it spawned keep
# running, but nothing respawns crashed agents or enforces pool counts — the
# fleet silently drifts (see the June incident: researcher-11 hit 222 failures
# with no supervisor to recycle it).
#
# This keeper closes that gap: it runs the daemon in a loop and restarts it if it
# exits for any reason other than a clean stop signal, with crash-loop protection
# and persistent crash logging so the *next* failure is diagnosable (the daemon's
# own daemon_log only echoes to its tmux pane, which dies with it).
#
# Usage:
#   ./scripts/lean/daemon-keeper.sh [daemon args...]
#
# Typically launched in tmux so it survives the controlling terminal:
#   tmux new-session -d -s lean-daemon \
#     './scripts/lean/daemon-keeper.sh --monitor-only --interval 60 \
#        --researcher 3 --enricher 1 --aristotle 1 --auditor 1 \
#        --seeker 1 --deployer 1 --tester 1 --herald 1 --mechanic 1'
#
# Clean shutdown (keeper + daemon both exit, agents stopped by the daemon):
#   touch .loom/signals/stop-lean-daemon
# or stop the tmux session after the daemon has settled.
#
# Note: the keeper intentionally does NOT use `set -e`. It must survive the
# daemon's failures, not share them.

set -uo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
REPO_ROOT="$(cd "$SCRIPT_DIR/../.." && pwd)"
cd "$REPO_ROOT"

# Per-role model tiering (gitignored, host-local — see .loom/model-config.env.example).
# Exports CLAUDE_MODEL (global default) + <ROLE>_CLAUDE_MODEL overrides that the
# daemon reads at agent-spawn time (resolution chain: <ROLE>_<slot> > <ROLE> >
# CLAUDE_MODEL > wrapper default). Sourced here so the whole fleet inherits it and
# it survives daemon crash/respawn. Absent → wrapper default (opus) for all roles.
if [[ -f "$REPO_ROOT/.loom/model-config.env" ]]; then
    # shellcheck disable=SC1091
    source "$REPO_ROOT/.loom/model-config.env"
fi

DAEMON="$SCRIPT_DIR/launch.sh"
SIGNALS_DIR=".loom/signals"
STOP_SIGNAL_FILE="$SIGNALS_DIR/stop-lean-daemon"
KEEPER_LOG="research/lean-daemon-keeper.log"          # gitignored; persists across daemon crashes
KEEPER_PID_FILE="research/lean-daemon-keeper.pid"

# Crash-loop protection: if the daemon dies in under MIN_HEALTHY_SECONDS, treat it
# as a fast failure. After MAX_FAST_FAILS consecutive fast failures, back off for
# CRASH_LOOP_BACKOFF instead of hot-looping (and keep logging so it's visible).
RESTART_BACKOFF="${KEEPER_RESTART_BACKOFF:-5}"        # normal pause between restarts
MIN_HEALTHY_SECONDS="${KEEPER_MIN_HEALTHY_SECONDS:-120}"
MAX_FAST_FAILS="${KEEPER_MAX_FAST_FAILS:-5}"
CRASH_LOOP_BACKOFF="${KEEPER_CRASH_LOOP_BACKOFF:-300}"

mkdir -p "$(dirname "$KEEPER_LOG")" "$SIGNALS_DIR"

keeper_log() {
    local ts
    ts=$(date -u +"%Y-%m-%dT%H:%M:%SZ")
    echo "[$ts] [keeper] $*" | tee -a "$KEEPER_LOG"
}

# Infra guardian: a separate process that watches Docker health, disk space, and
# git-worktree leaks and remediates them (restart wedged Docker, reclaim disk,
# reap merged/stale worktrees). Kept out-of-process from the daemon so its
# remediation can never crash the fleet supervisor. Launched once below.
GUARDIAN="$SCRIPT_DIR/infra-guardian.sh"
GUARDIAN_PID=""

# Best-effort cleanup of our own pid file (and the guardian) on exit.
cleanup() {
    rm -f "$KEEPER_PID_FILE" 2>/dev/null || true
    [[ -n "$GUARDIAN_PID" ]] && kill "$GUARDIAN_PID" 2>/dev/null || true
}
trap cleanup EXIT
# Forward termination signals: on TERM/INT, drop a stop signal so the daemon
# tears down cleanly, then exit the keeper loop.
trap 'keeper_log "received termination signal — requesting daemon stop"; touch "$STOP_SIGNAL_FILE" 2>/dev/null || true; exit 0' TERM INT

echo $$ > "$KEEPER_PID_FILE"

keeper_log "starting; daemon=$DAEMON args: $*"

if [[ ! -x "$DAEMON" ]]; then
    keeper_log "FATAL: daemon script not found or not executable: $DAEMON"
    exit 1
fi

# Launch the infra guardian once, in the background, unless disabled. It watches
# Docker/disk/worktrees for the whole life of the fleet; cleanup() kills it.
if [[ "${KEEPER_DISABLE_GUARDIAN:-0}" != "1" && -x "$GUARDIAN" ]]; then
    "$GUARDIAN" &
    GUARDIAN_PID=$!
    keeper_log "launched infra-guardian (pid $GUARDIAN_PID)"
elif [[ ! -x "$GUARDIAN" ]]; then
    keeper_log "WARN: infra-guardian not found/executable at $GUARDIAN — skipping"
fi

fast_fails=0
run=0
while true; do
    # Honor an existing stop signal before (re)starting.
    if [[ -f "$STOP_SIGNAL_FILE" ]]; then
        keeper_log "stop signal present ($STOP_SIGNAL_FILE) — not starting daemon; keeper exiting"
        exit 0
    fi

    run=$((run + 1))
    start_epoch=$(date +%s)
    keeper_log "launching daemon (run #$run): $DAEMON daemon $*"

    # Run the daemon in the foreground so we observe its exit. Its own output
    # still streams to our stdout (the tmux pane); we add lifecycle lines here.
    "$DAEMON" daemon "$@"
    rc=$?

    end_epoch=$(date +%s)
    elapsed=$((end_epoch - start_epoch))

    # A clean stop (stop signal) means the daemon shut the fleet down on purpose.
    if [[ -f "$STOP_SIGNAL_FILE" ]]; then
        keeper_log "daemon exited (rc=$rc) after ${elapsed}s with stop signal present — clean shutdown; keeper exiting"
        exit 0
    fi

    if [[ "$elapsed" -lt "$MIN_HEALTHY_SECONDS" ]]; then
        fast_fails=$((fast_fails + 1))
        keeper_log "daemon exited (rc=$rc) after only ${elapsed}s — fast failure ${fast_fails}/${MAX_FAST_FAILS}"
        if [[ "$fast_fails" -ge "$MAX_FAST_FAILS" ]]; then
            keeper_log "crash-loop detected (${fast_fails} fast failures) — backing off ${CRASH_LOOP_BACKOFF}s before retrying"
            sleep "$CRASH_LOOP_BACKOFF"
            fast_fails=0
            continue
        fi
    else
        # Ran long enough to be considered healthy; reset the fast-fail counter.
        keeper_log "daemon exited (rc=$rc) after ${elapsed}s — restarting after ${RESTART_BACKOFF}s"
        fast_fails=0
    fi

    sleep "$RESTART_BACKOFF"
done
