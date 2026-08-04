#!/usr/bin/env bash
# worktree-root.sh — Resolve the base directory that holds agent worktrees.
#
# Lean-fleet port of Loom's resolver. Keep this file in LOCK-STEP with the
# upstream helper (rjwalters/loom `defaults/scripts/lib/worktree-root.sh`,
# v0.10.6, issue #3530 / PR #3538): same function name, same precedence, same
# env var and config key, so one knob moves both Loom-managed (issue-N / pr-N)
# and lean-fleet (enricher-N, researcher-N, erdos-N, …) worktrees.
#
# Source this file (do not exec). Defines a single function:
#
#   loom_worktree_root <repo_root> -> echoes the absolute worktree base dir
#
# Resolution precedence (first match wins), all opt-in:
#
#   1. LOOM_WORKTREE_ROOT env var          — highest priority
#   2. .loom/config.json → worktree.root   — jq-guarded, same namespace as
#                                            worktree.linkPaths (#3534)
#   3. ${repo_root}/.loom/worktrees        — default, UNCHANGED behavior
#
# When an override (env var or config key) is set, the returned path is
# namespaced by repo basename so multiple workspaces can share one external
# volume without colliding:
#
#     ${override%/}/<repo-basename>
#
# Callers then append their leaf names (`enricher-1`, `erdos-42`, …) as
# before. With neither override set, the function returns
# `${repo_root}/.loom/worktrees` verbatim — the result is byte-for-byte
# identical to the historical hardcoded path, so default installations see
# zero behavior change.
#
# Design notes:
#   - The env-var branch imitates other Loom env overrides (e.g.
#     LOOM_WORKTREE_ALWAYS_INCLUDE) and always wins over config.
#   - The config read reuses the exact guard pattern worktree.sh uses for
#     worktree.linkPaths: only attempt jq when it exists AND the config file
#     is present, and fall through softly (missing jq / missing key / malformed
#     JSON → default) so a broken config never breaks worktree creation.
#   - A RELATIVE override is rejected with a stderr warning and the function
#     falls back to the default. An external worktree root must be absolute so
#     that cleanup/GC comparison sites (which resolve absolute paths) match.
#   - Repo namespacing uses `basename "$repo_root"`. Two repos whose basenames
#     collide under the same override root would share a namespace; that is a
#     documented v1 limitation (see the issue), not a bug this helper guards.
#   - This helper never creates directories; callers `mkdir -p` the parent as
#     needed (git worktree add creates only the leaf).
#   - LOCAL DIVERGENCE from the upstream helper (#43644): an override root
#     that exists but cannot be read (macOS TCC denial on an external volume
#     returns EPERM from readdir while stat still succeeds) is rejected with
#     a loud stderr warning and the function falls back to the default root,
#     instead of letting every agent die mid-session on an unreadable volume.

# _loom_root_unreadable <dir>
#
# True (0) iff <dir> exists but its contents cannot be listed. In that state
# `[[ -d ]]` and `stat` still succeed, so an actual readdir is the only
# reliable probe. A nonexistent dir returns 1 (not-unreadable): callers may
# legitimately `mkdir -p` it later.
_loom_root_unreadable() {
    local d="$1"
    [[ -d "$d" ]] || return 1
    ! command ls "$d" >/dev/null 2>&1
}

# loom_worktree_root <repo_root>
#
# Echoes the absolute worktree base directory. `repo_root` must be an absolute
# path to the main workspace (the parent of the git common dir).
loom_worktree_root() {
    local repo_root="$1"

    # 1. Env var override — highest priority.
    if [[ -n "${LOOM_WORKTREE_ROOT:-}" ]]; then
        if [[ "$LOOM_WORKTREE_ROOT" == /* ]]; then
            local env_base="${LOOM_WORKTREE_ROOT%/}"
            local env_resolved
            env_resolved="$env_base/$(basename "$repo_root")"
            if _loom_root_unreadable "$env_base" || _loom_root_unreadable "$env_resolved"; then
                echo "loom_worktree_root: WARNING: worktree root '$env_resolved' exists but is UNREADABLE (EPERM — volume access lost? macOS TCC denial? see #43644); falling back to default $repo_root/.loom/worktrees" >&2
                echo "$repo_root/.loom/worktrees"
                return 0
            fi
            echo "$env_resolved"
            return 0
        fi
        echo "loom_worktree_root: LOOM_WORKTREE_ROOT must be an absolute path (got: '$LOOM_WORKTREE_ROOT'); falling back to default" >&2
        echo "$repo_root/.loom/worktrees"
        return 0
    fi

    # 2. Config key override — .loom/config.json → worktree.root.
    #    Same jq guard pattern as worktree.linkPaths (worktree.sh).
    local config_file="$repo_root/.loom/config.json"
    if command -v jq >/dev/null 2>&1 && [[ -f "$config_file" ]]; then
        local cfg_root
        cfg_root=$(jq -r '.worktree.root? // empty' "$config_file" 2>/dev/null)
        if [[ -n "$cfg_root" ]]; then
            if [[ "$cfg_root" == /* ]]; then
                local cfg_base="${cfg_root%/}"
                local cfg_resolved
                cfg_resolved="$cfg_base/$(basename "$repo_root")"
                if _loom_root_unreadable "$cfg_base" || _loom_root_unreadable "$cfg_resolved"; then
                    echo "loom_worktree_root: WARNING: worktree root '$cfg_resolved' exists but is UNREADABLE (EPERM — volume access lost? macOS TCC denial? see #43644); falling back to default $repo_root/.loom/worktrees" >&2
                    echo "$repo_root/.loom/worktrees"
                    return 0
                fi
                echo "$cfg_resolved"
                return 0
            fi
            echo "loom_worktree_root: worktree.root in .loom/config.json must be an absolute path (got: '$cfg_root'); falling back to default" >&2
            echo "$repo_root/.loom/worktrees"
            return 0
        fi
    fi

    # 3. Default — unchanged historical behavior.
    echo "$repo_root/.loom/worktrees"
}
