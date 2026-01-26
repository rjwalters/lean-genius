#!/bin/bash
# Batch merge all open PRs by attempting direct merge, then rebase+merge for conflicts
# After all merges, listings.json should be regenerated via `npx tsx scripts/annotations/build.ts`

set -euo pipefail

REPO_ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
cd "$REPO_ROOT"

TEMP_WORKTREE="$REPO_ROOT/.loom/worktrees/batch-rebase-$$"
MERGED=0
FAILED=0
SKIPPED=0
FAILED_PRS=""

cleanup() {
    echo ""
    echo "=== Cleanup ==="
    if [[ -d "$TEMP_WORKTREE" ]]; then
        (cd "$TEMP_WORKTREE" && git rebase --abort 2>/dev/null || true)
        git worktree remove "$TEMP_WORKTREE" --force 2>/dev/null || true
    fi
    git worktree prune 2>/dev/null || true
    echo "Results: merged=$MERGED, failed=$FAILED, skipped=$SKIPPED"
    if [[ -n "$FAILED_PRS" ]]; then
        echo "Failed PRs:$FAILED_PRS"
    fi
}
trap cleanup EXIT

echo "=== Batch Merging Open PRs ==="
echo "Fetching PR list..."

# Get all open PR numbers (sorted ascending so oldest first)
ALL_PRS=$(gh pr list --limit 200 --json number --jq '.[].number' | sort -n)
TOTAL=$(echo "$ALL_PRS" | wc -w | tr -d ' ')
echo "Found $TOTAL open PRs"

if [[ $TOTAL -eq 0 ]]; then
    echo "No PRs to merge"
    exit 0
fi

# Ensure main is up to date
git fetch origin main --quiet

# Create temp worktree for rebasing
echo "Creating temporary worktree..."
mkdir -p "$REPO_ROOT/.loom/worktrees"
git worktree add "$TEMP_WORKTREE" origin/main --detach 2>/dev/null

COUNT=0
for pr in $ALL_PRS; do
    ((COUNT++))
    echo -n "  [$COUNT/$TOTAL] #$pr: "

    # Phase 1: Try direct merge (works for MERGEABLE PRs)
    if gh pr merge "$pr" --squash --admin 2>/dev/null; then
        echo "merged (direct)"
        ((MERGED++))
        git fetch origin main --quiet 2>/dev/null || true
        continue
    fi

    # Phase 2: Need to rebase first
    BRANCH=$(gh pr view "$pr" --json headRefName --jq '.headRefName' 2>/dev/null || echo "")
    if [[ -z "$BRANCH" ]]; then
        echo "could not get branch, skipping"
        ((SKIPPED++))
        continue
    fi

    # Fetch the branch
    git fetch origin "$BRANCH" --quiet 2>/dev/null || {
        echo "fetch failed"
        ((FAILED++))
        FAILED_PRS="$FAILED_PRS #$pr"
        continue
    }

    # Rebase in worktree
    REBASE_OK=false
    REBASE_OUTPUT=$(
        cd "$TEMP_WORKTREE"

        # CRITICAL: Clean up any leftover rebase state from previous iteration
        git rebase --abort 2>/dev/null || true
        git reset --hard 2>/dev/null || true
        git clean -fd 2>/dev/null || true

        # Fetch latest main
        git fetch origin main --quiet 2>/dev/null || true

        # Reset to PR branch
        if ! git checkout -B "$BRANCH" "origin/$BRANCH" --quiet 2>&1; then
            echo "FAIL:checkout"
            exit 1
        fi

        # Attempt rebase on main
        if git rebase origin/main 2>&1; then
            if git push --force-with-lease origin "$BRANCH" --quiet 2>&1; then
                echo "OK:clean-rebase"
                exit 0
            else
                echo "FAIL:push-after-clean-rebase"
                exit 1
            fi
        fi

        # Rebase had conflicts - resolve them
        MAX_ROUNDS=10
        for round in $(seq 1 $MAX_ROUNDS); do
            CONFLICT_FILES=$(git diff --name-only --diff-filter=U 2>/dev/null || true)
            if [[ -z "$CONFLICT_FILES" ]]; then
                # No more conflicts - try to continue or we're done
                if git status 2>/dev/null | grep -q "rebase in progress"; then
                    GIT_EDITOR=true git rebase --continue 2>&1 || true
                    continue
                else
                    break
                fi
            fi

            ALL_RESOLVED=true
            for conflict_file in $CONFLICT_FILES; do
                # Resolve all conflicts by taking main's version (--ours during rebase = main)
                if git checkout --ours "$conflict_file" 2>/dev/null && git add "$conflict_file" 2>/dev/null; then
                    true
                else
                    echo "FAIL:resolve:$conflict_file"
                    ALL_RESOLVED=false
                fi
            done

            if [[ "$ALL_RESOLVED" != "true" ]]; then
                git rebase --abort 2>/dev/null || true
                echo "FAIL:unresolvable"
                exit 1
            fi

            # Continue rebase (may trigger more conflicts in next round)
            GIT_EDITOR=true git rebase --continue 2>&1 || {
                # Check if rebase is done
                if ! git status 2>/dev/null | grep -q "rebase in progress"; then
                    break
                fi
                # Still rebasing - continue loop for next round of conflicts
            }
        done

        # Verify rebase completed
        if git status 2>/dev/null | grep -q "rebase in progress"; then
            git rebase --abort 2>/dev/null || true
            echo "FAIL:rebase-incomplete-after-$MAX_ROUNDS-rounds"
            exit 1
        fi

        if git push --force-with-lease origin "$BRANCH" --quiet 2>&1; then
            echo "OK:resolved-rebase"
            exit 0
        else
            echo "FAIL:push-after-resolved-rebase"
            exit 1
        fi
    ) && REBASE_OK=true

    if [[ "$REBASE_OK" != "true" ]]; then
        # Extract failure reason from output
        REASON=$(echo "$REBASE_OUTPUT" | grep "^FAIL:" | tail -1 || echo "unknown")
        echo "rebase failed ($REASON)"
        ((FAILED++))
        FAILED_PRS="$FAILED_PRS #$pr"
        continue
    fi

    # Phase 3: Merge after rebase
    sleep 3
    if gh pr merge "$pr" --squash --admin 2>/dev/null; then
        echo "merged (after rebase)"
        ((MERGED++))
        git fetch origin main --quiet 2>/dev/null || true
    else
        # GitHub may need more time to recompute status
        sleep 8
        if gh pr merge "$pr" --squash --admin 2>/dev/null; then
            echo "merged (after rebase, retry)"
            ((MERGED++))
            git fetch origin main --quiet 2>/dev/null || true
        else
            echo "merge failed after rebase"
            ((FAILED++))
            FAILED_PRS="$FAILED_PRS #$pr"
        fi
    fi
done

echo ""
echo "=== Batch Merge Complete ==="
echo "  Merged: $MERGED"
echo "  Failed: $FAILED"
echo "  Skipped: $SKIPPED"
if [[ -n "$FAILED_PRS" ]]; then
    echo "  Failed PRs:$FAILED_PRS"
fi
echo ""
echo "Next step: regenerate listings.json"
echo "  npx tsx scripts/annotations/build.ts"
