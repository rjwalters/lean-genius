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

# remove_own_worktree <worktree_path>
#
# Idempotent: if the path does not exist (already removed), returns 0 quietly.
# Applies structural guards 1-5; on any guard hit, preserves and returns 0.
# Only when all guards pass does it `git worktree remove --force` (falling back
# to `rm -rf` + `git worktree prune` if the git removal fails).
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
    # fully backed up. Remove it.
    if git worktree remove "$wt_path" --force 2>/dev/null; then
        _wc_log "removed: $wt_path"
    else
        # Fallback: directory may be a stale/orphaned worktree git no longer
        # tracks. Remove on disk and prune the dangling reference.
        rm -rf "$wt_path" 2>/dev/null || true
        git worktree prune 2>/dev/null || true
        _wc_log "removed (rm -rf fallback): $wt_path"
    fi
    return 0
}
