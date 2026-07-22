#!/usr/bin/env bash
#
# completions-dir.sh - Canonical location for daemon completion signals.
#
# Source this file, then call `resolve_completions_dir` to get the ONE
# directory where completion signals must live so the lean daemon can see
# them:
#
#     .../.loom/signals/completions
#
# Why this exists
# ---------------
# Completion signals are produced by agents (enricher, researcher, deployer,
# aristotle) that run inside *git worktrees*, and consumed by the lean daemon
# running in the *main checkout*. `.loom/` is per-worktree, gitignored runtime
# state, so a signal written to a worktree's `.loom/signals/completions` is
# invisible to the daemon reading the main checkout's directory -- the
# `session_stats` counters (Deployments / enriched / research / proofs) then
# never increment (issue #41047).
#
# The fix is a single source of truth: anchor on the git *common* dir. From any
# linked worktree, `git rev-parse --git-common-dir` returns the absolute path to
# the main repository's `.git`; from the main checkout it returns a path we
# normalise via `--show-toplevel`. Either way every script resolves to the SAME
# main-checkout `.loom/signals/completions`.
#
# Producers and the daemon consumer must both use this resolver so they agree.

# Resolve the canonical completions directory (absolute path). Falls back to a
# repo-relative path only when git metadata is unavailable.
resolve_completions_dir() {
    local common root
    if common="$(git rev-parse --git-common-dir 2>/dev/null)"; then
        case "$common" in
            /*)
                # Linked worktree: common dir is the absolute main `.git`.
                root="$(cd "$(dirname "$common")" && pwd)"
                ;;
            *)
                # Main checkout: common dir is relative; the working-tree top
                # is the main root.
                root="$(git rev-parse --show-toplevel 2>/dev/null || pwd)"
                ;;
        esac
    else
        root="$(pwd)"
    fi
    printf '%s/.loom/signals/completions\n' "$root"
}
