#!/bin/bash
# Isolated harness for remove_own_worktree in scripts/lib/worktree-cleanup.sh
# (issue #25344, Phase 2a per-workflow worktree cleanup contract).
#
# Exercises the decision table against real throwaway git worktrees in a
# sandbox. A worktree must be REMOVED only when it is clean AND fully backed up
# (merged/stale-but-pushed); it must be PRESERVED when dirty, when it carries
# unpushed or unbacked commits, when locked, or when it is the current checkout.
#
# Run: bash scripts/tests/worktree-cleanup.test.sh
# Exits non-zero if any assertion fails.
set -u

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
# shellcheck source=../lib/worktree-cleanup.sh
source "$SCRIPT_DIR/../lib/worktree-cleanup.sh"

PASS=0
FAIL=0

assert_removed() { # <desc> <wt_path>
    if [[ -d "$2" ]]; then
        echo "  FAIL: $1 -> expected REMOVED, dir still present: $2"
        ((FAIL++))
    else
        echo "  ok: $1 -> REMOVED"
        ((PASS++))
    fi
}

assert_preserved() { # <desc> <wt_path>
    if [[ -d "$2" ]]; then
        echo "  ok: $1 -> PRESERVED"
        ((PASS++))
    else
        echo "  FAIL: $1 -> expected PRESERVED, dir gone: $2"
        ((FAIL++))
    fi
}

# Build a sandbox bare "remote" + a main worktree we attach throwaway worktrees
# to. We operate the worktrees relative to MAIN (so they are real linked
# worktrees of one repo and `git worktree remove` works).
ROOT="$(mktemp -d)"
REMOTE="$ROOT/remote.git"
git init -q --bare "$REMOTE"
git -C "$REMOTE" symbolic-ref HEAD refs/heads/main

MAIN="$ROOT/main"
git clone -q "$REMOTE" "$MAIN" 2>/dev/null
echo base > "$MAIN/f"
git -C "$MAIN" -c user.email=t@t -c user.name=t add f
git -C "$MAIN" -c user.email=t@t -c user.name=t commit -qm base
git -C "$MAIN" push -q -u origin main

WT_DIR="$ROOT/worktrees"
mkdir -p "$WT_DIR"

# Helper: add a linked worktree on a fresh branch off main.
add_wt() { # <name> <branch> -> echoes path
    local name="$1" branch="$2" path="$WT_DIR/$1"
    git -C "$MAIN" worktree add -q -b "$branch" "$path" main
    echo "$path"
}

run() { # run remove_own_worktree from inside MAIN so guard-1 compares vs MAIN
    ( cd "$MAIN" && remove_own_worktree "$1" )
}

# --- Case 1: clean + merged (pushed, branch on remote) => REMOVE ---
w="$(add_wt c1_clean_merged feat/c1)"
echo a >> "$w/f"
git -C "$w" -c user.email=t@t -c user.name=t commit -qam edit
git -C "$w" push -q -u origin feat/c1   # fully pushed: @{u}..HEAD empty
run "$w"
assert_removed "clean + fully-pushed (merged/stale)" "$w"

# --- Case 2: clean + stale-but-pushed via detached HEAD on a remote ref => REMOVE ---
# No upstream configured, but HEAD reachable from origin/main => backed up.
w="$(add_wt c2_detached_remote feat/c2)"
git -C "$w" checkout -q --detach origin/main
run "$w"
assert_removed "no-upstream + HEAD on remote ref" "$w"

# --- Case 3: dirty working tree => PRESERVE ---
w="$(add_wt c3_dirty feat/c3)"
echo a >> "$w/f"
git -C "$w" -c user.email=t@t -c user.name=t commit -qam edit
git -C "$w" push -q -u origin feat/c3       # backed up...
echo uncommitted >> "$w/f"                  # ...but now dirty (guard 4)
run "$w"
assert_preserved "dirty working tree" "$w"
[[ "$(tail -n1 "$w/f" 2>/dev/null)" == "uncommitted" ]] \
    && { echo "    (dirty change survived)"; } \
    || { echo "    FAIL: dirty change lost!"; ((FAIL++)); }

# --- Case 4: upstream configured + unpushed commits ahead => PRESERVE ---
w="$(add_wt c4_unpushed feat/c4)"
echo a >> "$w/f"
git -C "$w" -c user.email=t@t -c user.name=t commit -qam base-edit
git -C "$w" push -q -u origin feat/c4
echo b >> "$w/f"
git -C "$w" -c user.email=t@t -c user.name=t commit -qam ahead   # @{u}..HEAD non-empty
run "$w"
assert_preserved "upstream + unpushed commits ahead" "$w"

# --- Case 5: no upstream + local-only (unbacked) commits => PRESERVE ---
w="$(add_wt c5_unbacked feat/c5)"
echo a >> "$w/f"
git -C "$w" -c user.email=t@t -c user.name=t commit -qam local-only  # never pushed
run "$w"
assert_preserved "no upstream + unbacked local commits" "$w"

# --- Case 6: locked => PRESERVE (even though clean + pushed) ---
w="$(add_wt c6_locked feat/c6)"
echo a >> "$w/f"
git -C "$w" -c user.email=t@t -c user.name=t commit -qam edit
git -C "$w" push -q -u origin feat/c6
git -C "$MAIN" worktree lock "$w"
run "$w"
assert_preserved "locked worktree" "$w"
git -C "$MAIN" worktree unlock "$w" 2>/dev/null || true

# --- Case 7: current checkout => PRESERVE ---
# Run remove_own_worktree from INSIDE the target so guard 1 fires.
w="$(add_wt c7_current feat/c7)"
echo a >> "$w/f"
git -C "$w" -c user.email=t@t -c user.name=t commit -qam edit
git -C "$w" push -q -u origin feat/c7
( cd "$w" && remove_own_worktree "$w" )
assert_preserved "current checkout" "$w"

# --- Case 8: idempotent / absent path => no error, quiet ---
out="$(run "$WT_DIR/does-not-exist" 2>&1)"
rc=$?
if [[ $rc -eq 0 && -z "$out" ]]; then
    echo "  ok: absent path -> quiet no-op (rc=0)"
    ((PASS++))
else
    echo "  FAIL: absent path -> rc=$rc out='$out'"
    ((FAIL++))
fi

# --- Case 9: idempotent second call on an already-removed worktree ---
w="$(add_wt c9_twice feat/c9)"
echo a >> "$w/f"
git -C "$w" -c user.email=t@t -c user.name=t commit -qam edit
git -C "$w" push -q -u origin feat/c9
run "$w"
assert_removed "second-call setup: first removal" "$w"
out="$(run "$w" 2>&1)"; rc=$?
if [[ $rc -eq 0 && -z "$out" ]]; then
    echo "  ok: second call -> quiet no-op (rc=0)"
    ((PASS++))
else
    echo "  FAIL: second call -> rc=$rc out='$out'"
    ((FAIL++))
fi

echo ""
echo "PASS=$PASS FAIL=$FAIL"
rm -rf "$ROOT"
[[ "$FAIL" -eq 0 ]]
