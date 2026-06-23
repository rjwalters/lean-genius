#!/bin/bash
# Decision-equivalence + perf harness for the Phase 3 batch optimization in
# scripts/clean-branches.sh (issue #25345).
#
# Phase 3 used to spawn, per local branch:
#   - one `awk` over the whole PR_MAP_FILE (get_pr_status), and
#   - on the NONE path, `git merge-base` + `git rev-list --count` (ahead count).
# Both are replaced with two one-shot passes:
#   (1) a single awk-join resolving every branch's PR status, and
#   (2) a single `git for-each-ref --merged main` set for "0 commits ahead".
#
# This test builds a sandbox repo with one branch of each class and asserts the
# NEW batched resolution produces a BYTE-IDENTICAL DELETE/KEEP verdict to the
# OLD per-branch logic, for every branch. It also demonstrates the two batch
# primitives are correct and shows a before/after timing for the ahead-count
# hot path. Runs on bash 3.2 (no `declare -A`).
#
# Run: bash scripts/tests/clean-branches-phase3.test.sh
# Exits non-zero if any assertion fails.
set -u
PASS=0; FAIL=0
assert() { # <desc> <expected> <actual>
    if [[ "$3" == "$2" ]]; then echo "  ok: $1 -> $3"; ((PASS++))
    else echo "  FAIL: $1 expected [$2] got [$3]"; ((FAIL++)); fi
}

GIT="git -c user.email=t@t -c user.name=t -c commit.gpgsign=false"

# -----------------------------------------------------------------------------
# Reference implementations of the OLD (per-branch) and NEW (batched) verdict
# logic. Both consume the SAME inputs and must agree on every branch.
# -----------------------------------------------------------------------------

# verdict_for STATUS NOPR_DELETE KEEP_NO_PR -> DELETE | KEEP
# Mirrors the Phase 3 case/NONE decision tree: DELETE for MERGED/CLOSED, KEEP
# for OPEN; on NONE: --keep-no-pr=>KEEP, else the no-PR-deletable flag decides
# (1 => DELETE, 0 => KEEP).
verdict_for() {
    local status="$1" nopr_del="$2" keep="$3"
    case "$status" in
        MERGED|CLOSED) echo DELETE ;;
        OPEN)          echo KEEP ;;
        NONE)
            if [[ "$keep" == true ]]; then echo KEEP
            elif [[ "$nopr_del" -eq 1 ]]; then echo DELETE
            else echo KEEP; fi ;;
        *) echo KEEP ;;
    esac
}

# OLD per-branch resolution: awk-scan PR_MAP_FILE + merge-base/rev-list ahead.
old_status() {
    local b="$1"
    local s; s=$(awk -F'\t' -v b="$b" '$1==b {s=$2} END{print s}' "$PR_MAP_FILE")
    echo "${s:-NONE}"
}
# OLD no-PR DELETE decision (1=delete, 0=keep), reproducing the old code:
#   merge_base = git merge-base main b   (EMPTY if no common ancestor)
#   ahead = (merge_base != "") ? rev-list --count merge_base..b : 0
#   delete iff ahead == 0   (note: empty merge-base => ahead defaults 0 => delete)
old_nopr_delete() {
    local b="$1" mb a=0
    mb=$($GIT -C "$REPO" merge-base main "$b" 2>/dev/null || echo "")
    if [[ -n "$mb" ]]; then a=$($GIT -C "$REPO" rev-list --count "$mb..$b" 2>/dev/null || echo 0); fi
    [[ "$a" -eq 0 ]] && echo 1 || echo 0
}

# NEW batched resolution: one awk-join + the NOPR_DELETE set (merged ∪ orphans).
# NOPR_DELETE = MERGED ∪ (ALL \ SHARES), where SHARES = branches containing a
# root of main (non-empty merge-base). Its complement of SHARES is exactly the
# empty-merge-base orphan set, so this reproduces the old empty-merge-base
# DELETE behavior without per-branch git spawns.
build_new_caches() {
    RESOLVED=$(mktemp)
    printf '%s\n' "$ALL_BRANCHES" \
        | awk -F'\t' '
            NR==FNR { if ($1 != "") m[$1]=$2; next }
            { print $0 "\t" (($1 in m) ? m[$1] : "NONE") }
          ' "$PR_MAP_FILE" - > "$RESOLVED"
    MERGED_SET=$(mktemp); SHARES_SET=$(mktemp); NOPR_DELETE=$(mktemp)
    $GIT -C "$REPO" for-each-ref --format='%(refname:short)' --merged main refs/heads | sort -u > "$MERGED_SET"
    : > "$SHARES_SET"
    while IFS= read -r r; do
        [[ -z "$r" ]] && continue
        $GIT -C "$REPO" for-each-ref --format='%(refname:short)' --contains "$r" refs/heads >> "$SHARES_SET"
    done < <($GIT -C "$REPO" rev-list --max-parents=0 main)
    sort -u -o "$SHARES_SET" "$SHARES_SET"
    {
        cat "$MERGED_SET"
        printf '%s\n' "$ALL_BRANCHES" | sort -u | comm -23 - "$SHARES_SET"
    } | sort -u > "$NOPR_DELETE"
}
new_status()      { awk -F'\t' -v b="$1" '$1==b {print $2; exit}' "$RESOLVED"; }
new_nopr_delete() { if grep -qxF "$1" "$NOPR_DELETE"; then echo 1; else echo 0; fi; }

# -----------------------------------------------------------------------------
# Build a sandbox repo with one branch of each class.
# -----------------------------------------------------------------------------
ROOT=$(mktemp -d)
REPO="$ROOT/repo"
$GIT init -q "$REPO"; $GIT -C "$REPO" checkout -q -b main
echo base > "$REPO/f"; $GIT -C "$REPO" add f; $GIT -C "$REPO" commit -qm base

# Class: no-PR, even with main (branch points at main's tip) -> DELETE
$GIT -C "$REPO" branch nopr-even main

# Class: no-PR, ahead of main (unique commit) -> KEEP
$GIT -C "$REPO" checkout -q -b nopr-ahead
echo ahead >> "$REPO/f"; $GIT -C "$REPO" commit -qam ahead
$GIT -C "$REPO" checkout -q main

# Class: merged-PR branch (has unique commit but PR is MERGED) -> DELETE
$GIT -C "$REPO" checkout -q -b feat-merged
echo m >> "$REPO/f"; $GIT -C "$REPO" commit -qam merged
$GIT -C "$REPO" checkout -q main

# Class: closed-PR branch -> DELETE
$GIT -C "$REPO" checkout -q -b feat-closed
echo c >> "$REPO/f"; $GIT -C "$REPO" commit -qam closed
$GIT -C "$REPO" checkout -q main

# Class: open-PR branch (must be preserved even though ahead) -> KEEP
$GIT -C "$REPO" checkout -q -b feat-open
echo o >> "$REPO/f"; $GIT -C "$REPO" commit -qam open
$GIT -C "$REPO" checkout -q main

# Class: merged-PR branch that is ALSO even with main (0 ahead) -> DELETE
$GIT -C "$REPO" branch feat-merged-even main

# Edge: branch name with a regex metacharacter, no PR, even with main -> DELETE
$GIT -C "$REPO" branch 'odd.name' main

# Class: ORPHAN-history branch, no PR (empty merge-base with main). The OLD code
# leaves `ahead` at its default 0 when merge-base is empty, so it DELETES these
# (this is the #13577 retired-master-root situation). The batched logic must
# reproduce that exactly via the SHARES (contains-root) complement. -> DELETE
$GIT -C "$REPO" checkout -q --orphan orphan-nopr
echo orphan > "$REPO/g"; $GIT -C "$REPO" add g; $GIT -C "$REPO" rm -q --cached f 2>/dev/null || true
$GIT -C "$REPO" commit -qm orphan-root
$GIT -C "$REPO" checkout -q main

# Class: ORPHAN-history branch WITH a CLOSED PR. Both old and new DELETE via the
# primary PR signal regardless of the orphan ahead-count. -> DELETE
$GIT -C "$REPO" checkout -q --orphan orphan-closed
echo oc > "$REPO/h"; $GIT -C "$REPO" add h; $GIT -C "$REPO" rm -q --cached f g 2>/dev/null || true
$GIT -C "$REPO" commit -qm orphan-closed-root
$GIT -C "$REPO" checkout -q main

# Synthetic PR map (tab-separated <branch>\t<state>); .closed then .open order
# so open-overrides-closed last-wins is exercised.
PR_MAP_FILE=$(mktemp)
{
    printf 'feat-merged\tMERGED\n'
    printf 'feat-merged-even\tMERGED\n'
    printf 'feat-closed\tCLOSED\n'
    printf 'feat-open\tCLOSED\n'   # closed first...
    printf 'feat-open\tOPEN\n'     # ...open later wins
    printf 'orphan-closed\tCLOSED\n'
} > "$PR_MAP_FILE"

ALL_BRANCHES=$($GIT -C "$REPO" branch | sed 's/^[*+ ]*//' | sort)
build_new_caches

# -----------------------------------------------------------------------------
# Equivalence: for every branch, OLD verdict == NEW verdict, both KEEP_NO_PR
# modes. Also assert against the hand-derived expected verdict.
# -----------------------------------------------------------------------------
# NOTE: `main` is omitted — it is PROTECTED in Phase 2 before the verdict tree
# runs, so its raw verdict (DELETE, being even+no-PR) is never reached. The
# old==new verdict-equivalence assertion still covers `main`; only the
# hand-derived protected-aware expectation is skipped for it.
EXPECTED="$(cat <<'EOF'
nopr-even DELETE KEEP
nopr-ahead KEEP KEEP
feat-merged DELETE DELETE
feat-closed DELETE DELETE
feat-open KEEP KEEP
feat-merged-even DELETE DELETE
odd.name DELETE KEEP
orphan-nopr DELETE KEEP
orphan-closed DELETE DELETE
EOF
)"

for b in $ALL_BRANCHES; do
    # main is protected in the real script; here we just confirm verdict logic
    os=$(old_status "$b"); od=$(old_nopr_delete "$b")
    ns=$(new_status "$b"); [[ -z "$ns" ]] && ns=NONE
    nd=$(new_nopr_delete "$b")

    # Status must match exactly between old scan and new join.
    assert "status($b)" "$os" "$ns"
    # No-PR deletable flag must match: old 1 <=> new 1 (covers merged AND orphan).
    assert "nopr-delete-flag($b)" "$od" "$nd"

    for keep in false true; do
        ov=$(verdict_for "$os" "$od" "$keep")
        nv=$(verdict_for "$ns" "$nd" "$keep")
        assert "verdict-equiv($b,keep=$keep)" "$ov" "$nv"
    done

    # Cross-check against hand-derived expected table.
    exp_false=$(echo "$EXPECTED" | awk -v b="$b" '$1==b{print $2}')
    exp_true=$(echo "$EXPECTED" | awk -v b="$b" '$1==b{print $3}')
    if [[ -n "$exp_false" ]]; then
        assert "expected($b,keep=false)" "$exp_false" "$(verdict_for "$ns" "$nd" false)"
        assert "expected($b,keep=true)"  "$exp_true"  "$(verdict_for "$ns" "$nd" true)"
    fi
done

# -----------------------------------------------------------------------------
# Prove the batched NOPR_DELETE set == per-branch (old ahead==0 incl. empty
# merge-base) on the WHOLE branch set — this is the byte-identical-decisions
# guarantee for the no-PR path, including orphan-history branches.
# -----------------------------------------------------------------------------
mismatch=0
for b in $ALL_BRANCHES; do
    o=$(old_nopr_delete "$b")
    n=$(grep -qxF "$b" "$NOPR_DELETE" && echo 1 || echo 0)
    [[ "$o" != "$n" ]] && { mismatch=$((mismatch+1)); echo "  MISMATCH: $b old_nopr_delete=$o nopr_set=$n"; }
done
assert "NOPR_DELETE set == per-branch old ahead==0 (all branches)" "0" "$mismatch"

# -----------------------------------------------------------------------------
# Trap-superset guard (issue #25349): the Phase 3b `--remote` EXIT trap must be
# a superset of the Phase 3 EXIT trap, otherwise re-registering it (bash traps
# replace, not append) silently de-registers cleanup for temp files created in
# Phase 3 -- specifically `${RESOLVED_STATUS_FILE}.shares` and
# `$NOPR_DELETE_SET_FILE` -- and they leak in $TMPDIR on a `--remote` run.
#
# This is a static source check (no live `gh`/remote needed): every temp file
# mentioned in the Phase 3 trap must also appear in the `--remote` trap.
# -----------------------------------------------------------------------------
SRC="$(dirname "$0")/../clean-branches.sh"
if [[ -f "$SRC" ]]; then
    # The two trap lines, by the distinguishing temp file each registers last.
    phase3_trap=$(grep -F '"${RESOLVED_STATUS_FILE}.merged" "${RESOLVED_STATUS_FILE}.shares"' "$SRC" | grep -F 'trap ' | head -1)
    remote_trap=$(grep -F '"$REMOTE_RESOLVED_FILE"' "$SRC" | grep -F 'trap ' | head -1)
    assert "phase3 trap line found" "yes" "$([[ -n "$phase3_trap" ]] && echo yes || echo no)"
    assert "remote trap line found" "yes" "$([[ -n "$remote_trap" ]] && echo yes || echo no)"
    for tok in \
        '"$PR_MAP_FILE"' '"${PR_MAP_FILE}.open"' '"${PR_MAP_FILE}.closed"' \
        '"$PROTECTED_BRANCHES_FILE"' '"$RESOLVED_STATUS_FILE"' \
        '"${RESOLVED_STATUS_FILE}.merged"' '"${RESOLVED_STATUS_FILE}.shares"' \
        '"$NOPR_DELETE_SET_FILE"'; do
        in_remote=$([[ "$remote_trap" == *"$tok"* ]] && echo yes || echo no)
        assert "remote trap cleans $tok" "yes" "$in_remote"
    done
fi

# -----------------------------------------------------------------------------
# Perf demonstration: scale up to N synthetic even-with-main branches and time
# the old per-branch ahead-count vs the single for-each-ref. Best-effort; the
# assertion only requires the batch call to be no slower than the per-branch
# loop (it is dramatically faster in practice).
# -----------------------------------------------------------------------------
N=300
i=0
while [[ $i -lt $N ]]; do $GIT -C "$REPO" branch "perf/$i" main; i=$((i+1)); done
PERF_BRANCHES=$($GIT -C "$REPO" for-each-ref --format='%(refname:short)' refs/heads/perf)

t0=$(date +%s)
for b in $PERF_BRANCHES; do old_nopr_delete "$b" >/dev/null; done
t1=$(date +%s)
$GIT -C "$REPO" for-each-ref --format='%(refname:short)' --merged main refs/heads/perf >/dev/null
t2=$(date +%s)
old_secs=$((t1 - t0)); new_secs=$((t2 - t1))
echo "  perf: per-branch ahead-count over $N branches = ${old_secs}s; single for-each-ref = ${new_secs}s"
# Sanity: the one-shot call must not be slower than the per-branch loop.
if [[ "$new_secs" -le "$old_secs" ]]; then
    echo "  ok: batch for-each-ref not slower than per-branch loop"; ((PASS++))
else
    echo "  FAIL: batch slower than per-branch loop (${new_secs}s > ${old_secs}s)"; ((FAIL++))
fi

echo ""
echo "PASS=$PASS FAIL=$FAIL"
rm -rf "$ROOT"; rm -f "$PR_MAP_FILE" "$RESOLVED" "$MERGED_SET" "$SHARES_SET" "$NOPR_DELETE"
[[ "$FAIL" -eq 0 ]]
