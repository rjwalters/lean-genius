#!/bin/bash
# worktree-cleanup.sh - shared per-workflow worktree reclaim helper.
#
# Provides `remove_own_worktree <worktree_path>`: safely removes an agent's own
# worktree once the agent has stopped. This is the per-workflow ("at the
# source") counterpart to the centralized backstop janitor in
# scripts/clean-branches.sh Phase 4 (issue #24857 / PR #25343). It reuses the
# EXACT structural safety guards 1-5 from that janitor so the two paths share a
# single decision contract and a crashed agent mid-edit never loses work.
#
# On the janitor side, those guards 1-5 (plus the reclaim-eligibility triggers)
# live in a single `reclaim_worktree` function shared by both the
# `.loom/worktrees/*` scratch pass and the pass that reclaims git-registered
# worktrees located OUTSIDE `.loom/worktrees/` (issue #35257); this helper stays
# in lock-step with those guards.
#
# Guards (a worktree is removed ONLY when ALL hold):
#   1. Not the current checkout (real-path normalized compare).
#   2. Not locked (`git worktree list --porcelain` does not flag it `locked`).
#   3. No active owning process (`pgrep -f "<path>"`).
#   4. Clean working tree (`git -C <path> status --porcelain` empty).
#   5. No commits that exist on no remote:
#        - upstream configured  => `@{u}..HEAD` must be empty.
#        - no upstream          => HEAD must be reachable from some remote ref
#                                  (`git branch -r --contains HEAD` non-empty).
#
# Unlike the backstop janitor, this helper does NOT re-implement the reclaim
# *trigger* logic (PR merged/closed, upstream-gone, mtime-stale). At agent-stop
# time the worktree being removed is, by construction, the agent's own and is
# meant to be reclaimed; the structural guards above are the only protection
# required. The backstop janitor remains responsible for crashed-without-stop
# cases.
#
# Usage (source then call):
#   source "$REPO_ROOT/scripts/lib/worktree-cleanup.sh"
#   remove_own_worktree "$WORKTREE_PATH"
#
# Return codes:
#   0 - worktree removed, OR nothing to remove (idempotent), OR preserved by a
#       guard. The caller's stop path should not treat a preserved/absent
#       worktree as a failure, so guard-preservation is NOT an error.
#
# The helper is intentionally quiet by default. Set WORKTREE_CLEANUP_VERBOSE=1
# to emit a one-line reason on every decision (useful for debugging / tests).

# Emit a message only when verbose mode is enabled. Goes to stderr so it never
# pollutes a caller that captures stdout.
_wc_log() {
    [[ "${WORKTREE_CLEANUP_VERBOSE:-0}" == "1" ]] && echo "worktree-cleanup: $*" >&2
    return 0
}

# would_remove_own_worktree <worktree_path>
#
# Predicate-only variant of the guards used by remove_own_worktree. Runs the
# read-only structural guards 1-5 WITHOUT performing any removal, and echoes a
# single word describing the decision to stdout:
#
#   remove   - all guards pass; a real run would remove this worktree.
#   absent   - path is empty or does not exist (nothing to remove).
#   current  - guard 1: this is the current checkout.
#   locked   - guard 2: worktree is locked.
#   busy     - guard 3: an owning process is alive.
#   dirty    - guard 4: working tree has uncommitted changes.
#   unpushed - guard 5: carries commits that exist on no remote.
#
# Return code: 0 when the decision is "remove", 1 otherwise (preserve/absent).
# This lets callers implement an honest --dry-run that reflects the same guard
# decision a real remove_own_worktree call would make, rather than a weaker
# claim-state check. All guard logic here is intentionally kept in lock-step
# with remove_own_worktree below.
would_remove_own_worktree() {
    local wt_path="$1"

    # Idempotency: nothing to remove.
    if [[ -z "$wt_path" || ! -d "$wt_path" ]]; then
        echo "absent"
        return 1
    fi

    local wt_real
    wt_real="$(cd "$wt_path" 2>/dev/null && pwd -P || echo "$wt_path")"

    # GUARD 1: never remove the current checkout.
    local current_wt_path current_real
    current_wt_path="$(git rev-parse --show-toplevel 2>/dev/null || echo "")"
    if [[ -n "$current_wt_path" ]]; then
        current_real="$(cd "$current_wt_path" 2>/dev/null && pwd -P || echo "$current_wt_path")"
        if [[ "$wt_real" == "$current_real" ]]; then
            echo "current"
            return 1
        fi
    fi

    # GUARD 2: never remove a locked worktree.
    local locked_wt_paths
    locked_wt_paths="$(git worktree list --porcelain 2>/dev/null \
        | awk '/^worktree /{p=$2} /^locked/{print p}')"
    if [[ -n "$locked_wt_paths" ]]; then
        local locked_path locked_real
        while IFS= read -r locked_path; do
            [[ -z "$locked_path" ]] && continue
            locked_real="$(cd "$locked_path" 2>/dev/null && pwd -P || echo "$locked_path")"
            if [[ "$locked_real" == "$wt_real" ]]; then
                echo "locked"
                return 1
            fi
        done <<< "$locked_wt_paths"
    fi

    # GUARD 3: never remove a worktree with an active owning process.
    if pgrep -f "$wt_path" &>/dev/null; then
        echo "busy"
        return 1
    fi

    # GUARD 4: never remove a worktree with a dirty working tree.
    if [[ -n "$(git -C "$wt_path" status --porcelain 2>/dev/null)" ]]; then
        echo "dirty"
        return 1
    fi

    # GUARD 5: never remove a worktree carrying commits that exist on no remote.
    if git -C "$wt_path" rev-parse --abbrev-ref --symbolic-full-name '@{u}' &>/dev/null; then
        local unpushed
        unpushed="$(git -C "$wt_path" log --oneline '@{u}..HEAD' 2>/dev/null || echo "")"
        if [[ -n "$unpushed" ]]; then
            echo "unpushed"
            return 1
        fi
    else
        local remote_containing
        remote_containing="$(git -C "$wt_path" branch -r --contains HEAD 2>/dev/null \
            | grep -v '\->' | sed 's/^[[:space:]]*//' | head -n 1)"
        if [[ -z "$remote_containing" ]]; then
            echo "unpushed"
            return 1
        fi
    fi

    echo "remove"
    return 0
}

# remove_own_worktree <worktree_path>
#
# Idempotent: if the path does not exist (already removed), returns 0 quietly.
# Applies structural guards 1-5; on any guard hit, preserves and returns 0.
# Only when all guards pass does it `git worktree remove` (no --force; if git
# refuses because state changed since the guards ran, the worktree is
# preserved — `rm -rf` + `git worktree prune` applies only to directories git
# no longer registers as worktrees).
remove_own_worktree() {
    local wt_path="$1"

    # Idempotency: nothing to remove.
    if [[ -z "$wt_path" || ! -d "$wt_path" ]]; then
        _wc_log "skip (absent): ${wt_path:-<empty>}"
        return 0
    fi

    local wt_real
    wt_real="$(cd "$wt_path" 2>/dev/null && pwd -P || echo "$wt_path")"

    # GUARD 1: never remove the current checkout.
    local current_wt_path current_real
    current_wt_path="$(git rev-parse --show-toplevel 2>/dev/null || echo "")"
    if [[ -n "$current_wt_path" ]]; then
        current_real="$(cd "$current_wt_path" 2>/dev/null && pwd -P || echo "$current_wt_path")"
        if [[ "$wt_real" == "$current_real" ]]; then
            _wc_log "preserve (current checkout): $wt_path"
            return 0
        fi
    fi

    # GUARD 2: never remove a locked worktree. Porcelain marks them `locked`.
    # Compare on real paths: `git worktree list` emits canonical paths (e.g.
    # /private/tmp on macOS) while the caller may pass a symlinked path
    # (/tmp), so a literal string compare can miss a genuine lock.
    local locked_wt_paths
    locked_wt_paths="$(git worktree list --porcelain 2>/dev/null \
        | awk '/^worktree /{p=$2} /^locked/{print p}')"
    if [[ -n "$locked_wt_paths" ]]; then
        local locked_path locked_real
        while IFS= read -r locked_path; do
            [[ -z "$locked_path" ]] && continue
            locked_real="$(cd "$locked_path" 2>/dev/null && pwd -P || echo "$locked_path")"
            if [[ "$locked_real" == "$wt_real" ]]; then
                _wc_log "preserve (locked): $wt_path"
                return 0
            fi
        done <<< "$locked_wt_paths"
    fi

    # GUARD 3: never remove a worktree with an active owning process.
    if pgrep -f "$wt_path" &>/dev/null; then
        _wc_log "preserve (active process): $wt_path"
        return 0
    fi

    # GUARD 4: never remove a worktree with a dirty working tree.
    if [[ -n "$(git -C "$wt_path" status --porcelain 2>/dev/null)" ]]; then
        _wc_log "preserve (uncommitted changes): $wt_path"
        return 0
    fi

    # GUARD 5: never remove a worktree carrying commits that exist on no remote.
    #   - upstream IS configured: preserve if `@{u}..HEAD` is non-empty (real
    #     commits ahead of the tracked remote branch).
    #   - upstream is NOT configured: "no upstream" is NOT "nothing to lose". A
    #     never-pushed branch can carry local-only commits. Preserve unless HEAD
    #     is reachable from some remote ref (`git branch -r --contains HEAD`).
    if git -C "$wt_path" rev-parse --abbrev-ref --symbolic-full-name '@{u}' &>/dev/null; then
        local unpushed
        unpushed="$(git -C "$wt_path" log --oneline '@{u}..HEAD' 2>/dev/null || echo "")"
        if [[ -n "$unpushed" ]]; then
            _wc_log "preserve (unpushed commits): $wt_path"
            return 0
        fi
    else
        local remote_containing
        remote_containing="$(git -C "$wt_path" branch -r --contains HEAD 2>/dev/null \
            | grep -v '\->' | sed 's/^[[:space:]]*//' | head -n 1)"
        if [[ -z "$remote_containing" ]]; then
            _wc_log "preserve (no upstream; HEAD not on any remote): $wt_path"
            return 0
        fi
    fi

    # All guards passed: this worktree is the agent's own, idle, clean, and
    # fully backed up. Remove it. No --force and no blind rm -rf fallback: if
    # git refuses the removal (state changed between the guards and now), the
    # worktree is preserved for the backstop janitor's next pass. rm -rf
    # applies only to directories git no longer registers as worktrees.
    local wt_list
    wt_list="$(git worktree list --porcelain 2>/dev/null || true)"
    if git worktree remove "$wt_path" 2>/dev/null; then
        _wc_log "removed: $wt_path"
    elif ! grep -qxF "worktree $wt_real" <<< "$wt_list"; then
        # Stale/orphaned dir git no longer tracks: remove on disk, prune ref.
        rm -rf "$wt_path" 2>/dev/null || true
        git worktree prune 2>/dev/null || true
        _wc_log "removed (orphaned dir): $wt_path"
    else
        _wc_log "preserve (git refused removal; state changed?): $wt_path"
    fi
    return 0
}
