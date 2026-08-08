#!/usr/bin/env bash
#
# infra-guardian.sh — infrastructure watchdog for the Lean Genius fleet.
#
# The fleet depends on three host resources that silently fail and stall
# everything (observed repeatedly): the Docker daemon (proof build-verification),
# free disk space, and git worktrees. When the disk fills, Docker Desktop's Linux
# VM wedges (socket accepts connections but `dockerd` never responds), which hangs
# the deployer/auditor mid-build for hours; and per-task agent worktrees leak
# because the role launchers create them (`git worktree add`) but never remove
# them — and even the ones that would clean up don't when the agent crashes.
#
# This guardian runs ALONGSIDE the daemon (launched by daemon-keeper.sh), in its
# own process, so its remediation can never crash the fleet supervisor. Every
# cycle it:
#   1. reclaims disk when low (reap worktrees, git gc, truncate huge logs),
#   2. restarts Docker Desktop if the daemon is wedged (rate-limited),
#   3. reaps merged/stale git worktrees to stop the leak from filling the disk.
#
# It is intentionally conservative: it only removes worktrees whose branch is
# already merged into origin/main, or that are unlocked and older than
# INFRA_WORKTREE_STALE_HOURS; and it only restarts Docker when `docker ps` times
# out (a healthy-but-busy daemon answers `docker ps` instantly, so an in-progress
# build is never interrupted).
#
# Usage:  ./scripts/lean/infra-guardian.sh
# Tunables (env):
#   INFRA_GUARDIAN_INTERVAL       seconds between cycles          (default 120)
#   INFRA_DISK_MIN_FREE_GB        cleanup trigger, GB free        (default 15)
#   INFRA_WORKTREE_STALE_HOURS    reap unmerged worktrees older   (default 24)
#   INFRA_DOCKER_RESTART_COOLDOWN min seconds between restarts     (default 600)
#   INFRA_GIT_GC_THRESHOLD_MB     git gc when .git exceeds, MB     (default 3000)
#
# Like the keeper, this does NOT use `set -e`: it must outlive transient failures.

set -uo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
REPO_ROOT="$(cd "$SCRIPT_DIR/../.." && pwd)"
cd "$REPO_ROOT"

# Resolved worktree base (LOOM_WORKTREE_ROOT env var / .loom/config.json
# worktree.root override; default $REPO_ROOT/.loom/worktrees). The reaper's
# allow-pattern must match worktrees at the override root, or leaked worktrees
# there would never be reaped (issue #37509).
# shellcheck source=../lib/worktree-root.sh
source "$SCRIPT_DIR/../lib/worktree-root.sh"
WORKTREE_ROOT_RESOLVED="$(loom_worktree_root "$REPO_ROOT")"

LOG="research/infra-guardian.log"          # gitignored; persists across restarts
STOP_SIGNAL_FILE=".loom/signals/stop-lean-daemon"

INTERVAL="${INFRA_GUARDIAN_INTERVAL:-120}"
DISK_MIN_FREE_GB="${INFRA_DISK_MIN_FREE_GB:-15}"
WORKTREE_STALE_HOURS="${INFRA_WORKTREE_STALE_HOURS:-24}"
DOCKER_RESTART_COOLDOWN="${INFRA_DOCKER_RESTART_COOLDOWN:-600}"
GIT_GC_THRESHOLD_MB="${INFRA_GIT_GC_THRESHOLD_MB:-3000}"

mkdir -p "$(dirname "$LOG")" ".loom/signals"

log() { echo "[$(date -u +"%Y-%m-%dT%H:%M:%SZ")] [guardian] $*" | tee -a "$LOG"; }

# Free space on / in whole GB (macOS `df -g`, Avail column).
free_gb() { df -g / 2>/dev/null | awk 'NR==2 {print $4}'; }

docker_present() {
    [[ "$(uname)" == "Darwin" ]] && command -v docker >/dev/null 2>&1 \
        && [[ -d "/Applications/Docker.app" ]]
}

last_docker_restart=0

# Restart Docker Desktop iff the daemon is wedged. `docker ps` answers instantly
# on a healthy daemon even during a heavy build, so a busy build is never hit.
check_docker() {
    docker_present || return 0
    if timeout 15 docker ps >/dev/null 2>&1; then return 0; fi

    local now; now=$(date +%s)
    if (( now - last_docker_restart < DOCKER_RESTART_COOLDOWN )); then
        log "docker unresponsive, but within restart cooldown ($((DOCKER_RESTART_COOLDOWN - (now - last_docker_restart)))s left) — skipping"
        return 0
    fi

    log "docker daemon unresponsive (docker ps timed out) — restarting Docker Desktop"
    last_docker_restart=$now
    osascript -e 'quit app "Docker Desktop"' >/dev/null 2>&1 || true
    sleep 2
    pkill -9 -f "com.docker.backend" 2>/dev/null || true
    pkill -9 -f "com.docker.build"   2>/dev/null || true
    pkill -9 -f "Docker Desktop"     2>/dev/null || true
    sleep 3
    open -a Docker >/dev/null 2>&1 || true

    local i
    for i in $(seq 1 30); do
        if timeout 8 docker ps >/dev/null 2>&1; then
            log "docker recovered ~$((i * 6))s after restart"
            return 0
        fi
        sleep 6
    done
    log "WARN: docker did NOT recover within ~3min of restart"
}

# Remove a worktree path if it is not the main checkout and not locked.
_reap_one() {
    local wt="$1" reason="$2"
    [[ "$wt" == "$REPO_ROOT" ]] && return 1
    git worktree remove --force "$wt" >/dev/null 2>&1 && log "reaped ($reason): ${wt##*/}"
}

# Reap worktrees whose branch is merged into origin/main, plus unlocked worktrees
# whose HEAD commit is older than the staleness window. Only touches known
# agent/temp worktree roots; never the main checkout.
reap_worktrees() {
    git fetch -q origin main 2>/dev/null || true
    git worktree prune 2>/dev/null || true

    local now; now=$(date +%s)
    local stale_secs=$(( WORKTREE_STALE_HOURS * 3600 ))

    # Snapshot locked worktrees so we never remove one an agent pinned.
    local locked; locked=$(git worktree list --porcelain 2>/dev/null \
        | awk '/^worktree /{wt=$2} /^locked/{print wt}')

    local wt ref
    while IFS=$'\t' read -r wt ref; do
        [[ -z "$wt" ]] && continue
        case "$wt" in
            *"/.loom/worktrees/"*|*"/.claude/worktrees/"*|/private/tmp/*|"$WORKTREE_ROOT_RESOLVED/"*) ;;
            *) continue ;;
        esac
        grep -qxF "$wt" <<<"$locked" && continue

        # Fixed, long-lived role worktrees are reused every cycle rather than
        # created per-task, and some (the deployer) fast-forward their branch
        # to exactly match origin/main as part of normal operation -- which
        # makes the "merged" check below trivially true every cycle. Without
        # this guard the guardian reaps the deployer's own worktree mid-run
        # (observed 2026-07-24: fired between the deploy pipeline's "Sync
        # Branch" step and the rest of the cycle, deregistering the worktree
        # out from under an in-flight PR-merge loop and requiring manual
        # `git worktree add` recovery).
        case "${wt##*/}" in
            deployer) continue ;;
        esac

        if [[ "$ref" != "DETACHED" ]] && git merge-base --is-ancestor "$ref" origin/main 2>/dev/null; then
            _reap_one "$wt" "merged"
            continue
        fi
        local head_epoch
        head_epoch=$(git -C "$wt" log -1 --format=%ct 2>/dev/null || echo "$now")
        if (( now - head_epoch > stale_secs )); then
            _reap_one "$wt" "stale>${WORKTREE_STALE_HOURS}h"
        fi
    done < <(git worktree list --porcelain 2>/dev/null \
        | awk '/^worktree /{wt=$2} /^branch /{print wt"\t"$2} /^detached/{print wt"\tDETACHED"}')

    git worktree prune 2>/dev/null || true
}

# Reclaim disk when low: reap worktrees, gc a bloated .git, truncate huge logs.
check_disk() {
    local free; free=$(free_gb)
    [[ -z "$free" ]] && return 0
    if (( free >= DISK_MIN_FREE_GB )); then return 0; fi

    log "low disk: ${free}GB free (< ${DISK_MIN_FREE_GB}GB) — reclaiming"
    reap_worktrees

    local git_mb; git_mb=$(du -sm "$REPO_ROOT/.git" 2>/dev/null | cut -f1)
    if [[ -n "$git_mb" ]] && (( git_mb > GIT_GC_THRESHOLD_MB )); then
        log "git gc (.git is ${git_mb}MB)"
        git gc --prune=now >/dev/null 2>&1 || true
    fi

    # Truncate any runaway logs (agent panes redirect here).
    find .loom/logs research -name '*.log' -size +200M 2>/dev/null \
        | while read -r f; do : > "$f.tmp" 2>/dev/null && tail -c 50m "$f" > "$f.tmp" 2>/dev/null && mv "$f.tmp" "$f" 2>/dev/null && log "truncated large log ${f##*/}"; done

    log "post-cleanup: $(free_gb)GB free"
}

trap 'log "received termination signal — exiting"; exit 0' TERM INT

log "starting (interval=${INTERVAL}s disk_min=${DISK_MIN_FREE_GB}GB stale=${WORKTREE_STALE_HOURS}h docker_cooldown=${DOCKER_RESTART_COOLDOWN}s)"

# Reap on the half-hour even when disk is healthy, so the leak never builds toward
# a disk emergency in the first place.
reap_every=$(( 1800 / INTERVAL )); (( reap_every < 1 )) && reap_every=1
cyc=0
while true; do
    if [[ -f "$STOP_SIGNAL_FILE" ]]; then
        log "stop signal present — exiting"
        exit 0
    fi
    cyc=$(( cyc + 1 ))
    check_disk   || log "WARN: check_disk returned non-zero"
    check_docker || log "WARN: check_docker returned non-zero"
    if (( cyc % reap_every == 0 )); then
        reap_worktrees || log "WARN: reap_worktrees returned non-zero"
    fi
    sleep "$INTERVAL"
done
