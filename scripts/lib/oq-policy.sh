#!/bin/bash
#
# oq-policy.sh - Shared open-question (OQ) recursion policy for research agents.
#
# Sourced by the researcher/seeker problem-selection scripts to keep the
# OQ-recursion-depth cap in ONE place (issue #39827 / #39821). Without a cap the
# depth-first tier recurses into a result's open questions indefinitely,
# producing degenerate chains like
#   abel-ruffini-oq-04-oq-02-oq-02-oq-08-oq-01-oq-01-oq-01-oq-01-oq-01-oq-01-oq-01
# and single problems with 15+ descendants (erdos-396).
#
# A gallery entry's "OQ depth" is the number of `-oq-NN` segments in its slug/id.
#
# Configuration precedence (highest first):
#   1. MAX_OQ_DEPTH environment variable
#   2. maxOqDepth in .lean/config/oq-policy.json
#   3. built-in default (OQ_POLICY_DEFAULT_DEPTH below)
#
# Functions:
#   oq_depth <slug>       Echo the number of -oq- segments in <slug>.
#   oq_max_depth          Echo the configured max OQ depth.
#   oq_over_cap <slug>    Return 0 (true) if <slug> is strictly deeper than the
#                         cap (an entry that should never have been spawned).
#   oq_at_or_over_cap <slug>
#                         Return 0 (true) if <slug> is at OR beyond the cap
#                         (a leaf that must not spawn further children).

# Built-in default cap. Matches the prose guards in the seeker/researcher roles
# (at most 3 -oq- segments in a chain).
OQ_POLICY_DEFAULT_DEPTH=3

# Resolve the repo root so we can find the config file regardless of the caller's
# cwd (agents run from linked worktrees). Falls back to the default when git or
# the config file is unavailable.
_oq_policy_repo_root() {
    local common_dir
    if common_dir="$(git rev-parse --git-common-dir 2>/dev/null)" \
        && common_dir="$(cd "$common_dir" 2>/dev/null && pwd)"; then
        dirname "$common_dir"
        return 0
    fi
    local dir="$PWD"
    while [[ "$dir" != "/" ]]; do
        if [[ -e "$dir/.git" ]]; then
            echo "$dir"
            return 0
        fi
        dir="$(dirname "$dir")"
    done
    echo "$PWD"
}

# oq_depth <slug> — count of -oq- segments (0 for a root entry).
oq_depth() {
    local slug="$1"
    [[ -z "$slug" ]] && { echo 0; return; }
    # Count occurrences of "-oq-" followed by digits. grep -o prints one match
    # per line; wc -l counts them. `|| true` keeps set -e callers happy on 0.
    local n
    n=$(printf '%s\n' "$slug" | grep -o -- '-oq-[0-9]*' | wc -l | tr -d ' ')
    echo "${n:-0}"
}

# oq_max_depth — resolve the configured cap (env > config file > default).
oq_max_depth() {
    if [[ -n "${MAX_OQ_DEPTH:-}" ]]; then
        # Validate: must be a non-negative integer, else fall through.
        if [[ "$MAX_OQ_DEPTH" =~ ^[0-9]+$ ]]; then
            echo "$MAX_OQ_DEPTH"
            return
        fi
    fi

    local root config depth
    root="$(_oq_policy_repo_root)"
    config="$root/.lean/config/oq-policy.json"
    if [[ -f "$config" ]] && command -v jq >/dev/null 2>&1; then
        depth=$(jq -r '.maxOqDepth // empty' "$config" 2>/dev/null || true)
        if [[ "$depth" =~ ^[0-9]+$ ]]; then
            echo "$depth"
            return
        fi
    fi

    echo "$OQ_POLICY_DEFAULT_DEPTH"
}

# oq_over_cap <slug> — true (0) if slug is strictly deeper than the cap.
oq_over_cap() {
    local depth cap
    depth="$(oq_depth "$1")"
    cap="$(oq_max_depth)"
    [[ "$depth" -gt "$cap" ]]
}

# oq_at_or_over_cap <slug> — true (0) if slug is at or beyond the cap; such an
# entry must not spawn further OQ children.
oq_at_or_over_cap() {
    local depth cap
    depth="$(oq_depth "$1")"
    cap="$(oq_max_depth)"
    [[ "$depth" -ge "$cap" ]]
}
