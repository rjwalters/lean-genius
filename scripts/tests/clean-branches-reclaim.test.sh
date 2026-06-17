#!/bin/bash
# Isolated harness for the .loom/worktrees/* reclaim predicates in
# scripts/clean-branches.sh (issue #24857, PR #25343).
#
# It replicates the no-upstream/unpushed guard, the OPEN-PR guard, and the
# mtime path against real throwaway git worktrees in a sandbox, stubbing
# get_pr_status via the PR_STATUS env var. It asserts the full reclaim
# decision table, including the two cases the Judge flagged as previously
# unguarded:
#   - OPEN-PR + stale                    => PRESERVE (open-pr guard)
#   - no-upstream + unbacked commits     => PRESERVE (local-only commits)
# plus the contrasting safe-to-remove case:
#   - no-upstream + HEAD-on-remote + stale => REMOVE (stale)
#
# Run: bash scripts/tests/clean-branches-reclaim.test.sh
# Exits non-zero if any assertion fails.
set -u
WORKTREE_MAX_AGE_DAYS=30
PASS=0; FAIL=0

# get_pr_status is stubbed per-case via PR_STATUS env.
get_pr_status() { echo "${PR_STATUS:-NONE}"; }

# decide <wt_path> -> echoes PRESERVE:<reason> or REMOVE:<reason>
decide() {
    local wt_path="$1"

    # --- unpushed / no-upstream guard (Fix 2) ---
    if git -C "$wt_path" rev-parse --abbrev-ref --symbolic-full-name '@{u}' &>/dev/null; then
        unpushed=$(git -C "$wt_path" log --oneline '@{u}..HEAD' 2>/dev/null || echo "")
        if [[ -n "$unpushed" ]]; then echo "PRESERVE:unpushed"; return; fi
    else
        remote_containing=$(git -C "$wt_path" branch -r --contains HEAD 2>/dev/null \
            | grep -v '\->' | sed 's/^[[:space:]]*//' | head -n 1)
        if [[ -z "$remote_containing" ]]; then echo "PRESERVE:no-upstream-unbacked"; return; fi
    fi

    local wt_branch reclaim_reason=""
    wt_branch=$(git -C "$wt_path" symbolic-ref --short HEAD 2>/dev/null || echo "")
    if [[ -n "$wt_branch" ]]; then
        pr_status=$(get_pr_status "$wt_branch")
        if [[ "$pr_status" == "OPEN" ]]; then echo "PRESERVE:open-pr"; return; fi
        if [[ "$pr_status" == "MERGED" || "$pr_status" == "CLOSED" ]]; then reclaim_reason="PR $pr_status"; fi
    fi
    if [[ -z "$reclaim_reason" && -n "$wt_branch" ]]; then
        upstream=$(git -C "$wt_path" rev-parse --abbrev-ref --symbolic-full-name '@{u}' 2>/dev/null || echo "")
        if [[ -n "$upstream" ]] && ! git -C "$wt_path" rev-parse --verify --quiet "refs/remotes/$upstream" &>/dev/null; then
            reclaim_reason="upstream gone on origin"
        fi
    fi
    if [[ -z "$reclaim_reason" ]]; then
        now_epoch=$(date +%s)
        wt_mtime=$(stat -f %m "$wt_path" 2>/dev/null || stat -c %Y "$wt_path" 2>/dev/null || echo "$now_epoch")
        age_days=$(( (now_epoch - wt_mtime) / 86400 ))
        if [[ "$age_days" -gt "$WORKTREE_MAX_AGE_DAYS" ]]; then reclaim_reason="stale ${age_days}d"; fi
    fi
    if [[ -z "$reclaim_reason" ]]; then echo "PRESERVE:unmerged-recent"; return; fi
    echo "REMOVE:$reclaim_reason"
}

assert() { # <desc> <expected-prefix> <actual>
    if [[ "$3" == "$2"* ]]; then echo "  ok: $1 -> $3"; ((PASS++)); else echo "  FAIL: $1 expected $2 got $3"; ((FAIL++)); fi
}

# Build a sandbox bare "remote" + clones.
ROOT=$(mktemp -d)
REMOTE="$ROOT/remote.git"
git init -q --bare "$REMOTE"; git -C "$REMOTE" symbolic-ref HEAD refs/heads/main
seed=$(mktemp -d); git -C "$seed" init -q; git -C "$seed" checkout -q -b main
echo base > "$seed/f"; git -C "$seed" add f; git -C "$seed" -c user.email=t@t -c user.name=t commit -qm base
git -C "$seed" remote add origin "$REMOTE"; git -C "$seed" push -q origin main

mkwt() { # <name> -> path; fresh clone of remote on a branch
    local p="$ROOT/$1"; git clone -q "$REMOTE" "$p"; echo "$p"
}
age_dir() { touch -t 202601010000 "$1"; }   # ~5+ months old => stale

# Case 1: OPEN PR + stale => PRESERVE (Fix 1 core)
w=$(mkwt c1); git -C "$w" checkout -q -b feature/open; echo x >> "$w/f"
git -C "$w" -c user.email=t@t -c user.name=t commit -qam edit; git -C "$w" push -q -u origin feature/open
age_dir "$w"
assert "OPEN-PR + stale" "PRESERVE:open-pr" "$(PR_STATUS=OPEN decide "$w")"

# Case 2: no upstream + local-only commits + stale => PRESERVE (Fix 2 core)
w=$(mkwt c2); git -C "$w" checkout -q -b feature/scratch
echo y >> "$w/f"; git -C "$w" -c user.email=t@t -c user.name=t commit -qam local-only
# never pushed: no upstream, HEAD on no remote ref
age_dir "$w"
assert "no-upstream + unbacked commits + stale" "PRESERVE:no-upstream-unbacked" "$(PR_STATUS=NONE decide "$w")"

# Case 3: no upstream + HEAD reachable from a remote ref + stale => REMOVE
w=$(mkwt c3)
# detach onto origin/main so HEAD is contained by a remote ref, no upstream set
git -C "$w" checkout -q --detach origin/main
age_dir "$w"
assert "no-upstream + HEAD-on-remote + stale" "REMOVE:stale" "$(PR_STATUS=NONE decide "$w")"

# Case 4: no upstream + HEAD reachable from remote + recent => PRESERVE
w=$(mkwt c4); git -C "$w" checkout -q --detach origin/main
assert "no-upstream + HEAD-on-remote + recent" "PRESERVE:unmerged-recent" "$(PR_STATUS=NONE decide "$w")"

# Case 5: MERGED PR => REMOVE (regression: existing behavior preserved)
w=$(mkwt c5); git -C "$w" checkout -q -b feature/merged
echo z >> "$w/f"; git -C "$w" -c user.email=t@t -c user.name=t commit -qam m; git -C "$w" push -q -u origin feature/merged
assert "MERGED-PR" "REMOVE:PR MERGED" "$(PR_STATUS=MERGED decide "$w")"

# Case 6: upstream present + unpushed ahead => PRESERVE (regression)
w=$(mkwt c6); git -C "$w" checkout -q -b feature/ahead
echo q >> "$w/f"; git -C "$w" -c user.email=t@t -c user.name=t commit -qam p; git -C "$w" push -q -u origin feature/ahead
echo q2 >> "$w/f"; git -C "$w" -c user.email=t@t -c user.name=t commit -qam ahead
age_dir "$w"
assert "upstream + commits-ahead" "PRESERVE:unpushed" "$(PR_STATUS=OPEN decide "$w")"

# Case 7: upstream present + fully pushed + recent + no/none PR => PRESERVE
w=$(mkwt c7); git -C "$w" checkout -q -b feature/clean
echo r >> "$w/f"; git -C "$w" -c user.email=t@t -c user.name=t commit -qam c; git -C "$w" push -q -u origin feature/clean
assert "upstream + clean + recent" "PRESERVE:unmerged-recent" "$(PR_STATUS=NONE decide "$w")"

# Case 8: upstream present + fully pushed + stale + no PR => REMOVE
w=$(mkwt c8); git -C "$w" checkout -q -b feature/old
echo s >> "$w/f"; git -C "$w" -c user.email=t@t -c user.name=t commit -qam c; git -C "$w" push -q -u origin feature/old
age_dir "$w"
assert "upstream + clean + stale" "REMOVE:stale" "$(PR_STATUS=NONE decide "$w")"

# -----------------------------------------------------------------------------
# get_pr_status real-lookup tests (issue #25342): exact literal field match.
# The `decide` cases above stub get_pr_status via PR_STATUS, so they do not
# exercise the real PR_MAP_FILE lookup. Here we run the real function against a
# tab-separated map to prove (a) regex metacharacters in the branch name do not
# false-match another branch, (b) last-wins (open-overrides-closed) is kept, and
# (c) an absent branch returns NONE.
# This definition mirrors scripts/clean-branches.sh:get_pr_status.
get_pr_status_real() {
    local branch="$1"
    local status
    status=$(awk -F'\t' -v b="$branch" '$1==b {s=$2} END{print s}' "$PR_MAP_FILE")
    echo "${status:-NONE}"
}

PR_MAP_FILE=$(mktemp)
printf 'fixxfoo\tMERGED\n'  >> "$PR_MAP_FILE"   # would be false-matched by `fix.foo` under grep BRE
printf 'fix.foo\tOPEN\n'    >> "$PR_MAP_FILE"
printf 'feature/a*b\tCLOSED\n' >> "$PR_MAP_FILE"
printf 'feature/ladder\tCLOSED\n' >> "$PR_MAP_FILE"
printf 'feature/ladder\tOPEN\n'   >> "$PR_MAP_FILE"   # later entry wins (open overrides closed)
printf 'fix-2\tMERGED\n'    >> "$PR_MAP_FILE"

assert "metachar literal: fix.foo not matching fixxfoo" "OPEN"   "$(get_pr_status_real 'fix.foo')"
assert "metachar literal: fixxfoo own status"           "MERGED" "$(get_pr_status_real 'fixxfoo')"
assert "metachar literal: a*b own status"               "CLOSED" "$(get_pr_status_real 'feature/a*b')"
assert "last-wins: closed-then-open => OPEN"            "OPEN"   "$(get_pr_status_real 'feature/ladder')"
assert "absent branch => NONE"                          "NONE"   "$(get_pr_status_real 'feature/missing')"
assert "substring guard: fix vs fix-2"                  "NONE"   "$(get_pr_status_real 'fix')"
rm -f "$PR_MAP_FILE"

echo ""
echo "PASS=$PASS FAIL=$FAIL"
rm -rf "$ROOT" "$seed"
[[ "$FAIL" -eq 0 ]]
