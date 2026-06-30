#!/usr/bin/env bash
#
# clean-branches.sh - Comprehensive branch and worktree cleanup
#
# Cleans ALL stale local branches (not just agent-specific patterns) by checking
# GitHub PR status. Also cleans orphaned worktrees in .claude/ and .loom/.
#
# Usage: ./scripts/clean-branches.sh [options]
#
# Options:
#   --dry-run       Show what would be cleaned without making changes
#   -f, --force     Non-interactive mode (auto-confirm all prompts)
#   --keep-no-pr    Preserve branches that have no associated PR
#   --remote        Also delete merged/closed branches on origin (for CI use)
#   -h, --help      Show this help message
#
# Safety:
#   - Never deletes main/master
#   - Never deletes branches checked out in active worktrees
#   - Branches with no PR: deleted if 0 commits ahead of main, preserved if ahead
#   - --keep-no-pr overrides to preserve all branches without PRs
#   - --remote only deletes origin branches whose PR is MERGED or CLOSED
#     (OPEN-PR and no-PR remote branches are always preserved)

set -euo pipefail

# ANSI color codes
RED='\033[0;31m'
GREEN='\033[0;32m'
BLUE='\033[0;34m'
YELLOW='\033[1;33m'
CYAN='\033[0;36m'
BOLD='\033[1m'
NC='\033[0m'

error()   { echo -e "${RED}Error: $*${NC}" >&2; exit 1; }
info()    { echo -e "${BLUE}$*${NC}"; }
success() { echo -e "${GREEN}$*${NC}"; }
warning() { echo -e "${YELLOW}$*${NC}"; }
header()  { echo -e "${CYAN}$*${NC}"; }

# Find git repository root
find_repo_root() {
    local dir="$PWD"
    while [[ "$dir" != "/" ]]; do
        if [[ -d "$dir/.git" ]] || [[ -f "$dir/.git" ]]; then
            echo "$dir"
            return 0
        fi
        dir="$(dirname "$dir")"
    done
    error "Not in a git repository"
}

REPO_ROOT="$(find_repo_root)"

# Parse arguments
DRY_RUN=false
FORCE=false
KEEP_NO_PR=false
REMOTE=false

# Age threshold (in days) for reclaiming scratch worktrees under
# .loom/worktrees/* that have no merged/closed PR. A worktree older than this
# (by mtime) with a clean tree and no unpushed commits is eligible for removal.
# Overridable via the WORKTREE_MAX_AGE_DAYS environment variable.
WORKTREE_MAX_AGE_DAYS="${WORKTREE_MAX_AGE_DAYS:-30}"

for arg in "$@"; do
    case $arg in
        --dry-run)
            DRY_RUN=true
            shift
            ;;
        --force|-f)
            FORCE=true
            shift
            ;;
        --deep)
            # Accepted for compatibility with CLEAN_FLAGS but is a no-op
            # (this script always performs a full clean)
            shift
            ;;
        --keep-no-pr)
            KEEP_NO_PR=true
            shift
            ;;
        --remote)
            REMOTE=true
            shift
            ;;
        --help|-h)
            cat << 'HELPEOF'
Comprehensive Branch & Worktree Cleanup

Usage: ./scripts/clean-branches.sh [options]

Options:
  --dry-run       Show what would be cleaned without making changes
  -f, --force     Non-interactive mode (auto-confirm all prompts)
  --keep-no-pr    Preserve branches that have no associated PR
  --remote        Also delete merged/closed branches on origin (for CI use)
  -h, --help      Show this help message

Branch cleanup:
  For every local branch (except main/master and worktree-checked-out):
  - If a merged/closed PR exists: DELETE
  - If an open PR exists: PRESERVE
  - If no PR exists and branch is 0 commits ahead of main: DELETE
  - If no PR exists and branch has commits ahead: PRESERVE (or delete with prompt)
  - --keep-no-pr: always preserve branches with no PR

Remote cleanup (--remote):
  For every branch on origin (except main/master):
  - If a merged/closed PR exists: DELETE on origin
  - Otherwise (open PR or no PR): PRESERVE
  Intended for CI/scheduled runs where a fresh checkout has no local
  branches but origin has accumulated merged-PR branches.

Worktree cleanup:
  - .claude/worktrees/agent-* without a running claude process: REMOVE
  - .loom/worktrees/issue-* for closed GitHub issues: REMOVE
  - .loom/worktrees/temp-* (temporary rebase worktrees): REMOVE
  - .loom/worktrees/* (scratch: audit-*, auditor-*, mechanic-*,
    researcher-*, enricher-*, …): REMOVE when the tree is clean, has no
    unpushed commits, is not the current checkout, is not locked, has no
    active owning process, AND its branch is merged/closed/gone on origin
    OR its mtime exceeds WORKTREE_MAX_AGE_DAYS (default 30). Preserved
    otherwise.
  - git worktree prune (clean orphaned references)

Environment:
  WORKTREE_MAX_AGE_DAYS   Age threshold (days) for reclaiming stale scratch
                          worktrees with no merged/closed PR (default 30).

HELPEOF
            exit 0
            ;;
        *)
            error "Unknown option: $arg\nUse --help for usage information"
            ;;
    esac
done

# Show banner
echo ""
header "============================================================"
header "         Comprehensive Branch & Worktree Cleanup"
if [[ "$DRY_RUN" == true ]]; then
    header "                   (DRY RUN MODE)"
fi
header "============================================================"
echo ""

cd "$REPO_ROOT"

# Verify prerequisites
if ! command -v gh &> /dev/null; then
    error "GitHub CLI (gh) is required. Install with: brew install gh"
fi

if ! gh auth status &>/dev/null; then
    error "GitHub CLI not authenticated. Run: gh auth login"
fi

# =============================================================================
# PHASE 1: Build PR status map (batch fetch from GitHub)
# =============================================================================

header "Phase 1: Fetching PR status from GitHub..."
echo ""

# We need to handle pagination since gh caps at 1000 results per call.
# Fetch all closed+merged PRs (these are the ones we need for cleanup).
# Open PRs we also need to know about to preserve their branches.
PR_MAP_FILE=$(mktemp)
trap 'rm -f "$PR_MAP_FILE" "${PR_MAP_FILE}.open" "${PR_MAP_FILE}.closed"' EXIT

# Fetch all PRs in pages of 1000
# We fetch state and headRefName, building a map: branch -> state
fetch_prs() {
    local state_filter="$1"
    local output_file="$2"
    local page=1
    local total=0

    while true; do
        local count
        # Use GraphQL for efficient pagination
        local result
        result=$(gh api graphql --paginate -f query="
            query(\$endCursor: String) {
                repository(owner: \"$(gh repo view --json owner -q '.owner.login')\", name: \"$(gh repo view --json name -q '.name')\") {
                    pullRequests(first: 100, states: [$state_filter], after: \$endCursor) {
                        pageInfo { hasNextPage endCursor }
                        nodes { headRefName state }
                    }
                }
            }
        " 2>/dev/null) || { warning "GraphQL pagination failed, falling back to REST API"; return 1; }

        echo "$result" | jq -r '.data.repository.pullRequests.nodes[] | "\(.headRefName)\t\(.state)"' >> "$output_file"
        break  # --paginate handles all pages
    done
}

info "  Fetching merged/closed PRs..."
if ! fetch_prs "MERGED, CLOSED" "$PR_MAP_FILE.closed" 2>/dev/null; then
    # Fallback: use REST API with pagination
    info "  Using REST API fallback..."
    for state in closed merged; do
        page=1
        while true; do
            batch=$(gh pr list --state "$state" --limit 100 --json headRefName,state --jq '.[] | "\(.headRefName)\t\(.state)"' 2>/dev/null) || break
            [[ -z "$batch" ]] && break
            echo "$batch" >> "$PR_MAP_FILE.closed"
            count=$(echo "$batch" | wc -l | tr -d ' ')
            [[ "$count" -lt 100 ]] && break
            # gh pr list doesn't support --page, so we use a workaround
            # Actually gh pr list with --limit handles deduplication, so 100 is the max we get
            break
        done
    done
fi

closed_pr_count=$(wc -l < "$PR_MAP_FILE.closed" 2>/dev/null | tr -d ' ')
success "  Found $closed_pr_count closed/merged PR records"

info "  Fetching open PRs..."
gh pr list --state open --limit 500 --json headRefName,state --jq '.[] | "\(.headRefName)\t\(.state)"' > "$PR_MAP_FILE.open" 2>/dev/null || true
open_pr_count=$(wc -l < "$PR_MAP_FILE.open" 2>/dev/null | tr -d ' ')
success "  Found $open_pr_count open PR records"

# Combine into single map file (later entries override earlier for same branch)
cat "$PR_MAP_FILE.closed" "$PR_MAP_FILE.open" > "$PR_MAP_FILE"

# Function to look up branch PR status from the map
# Returns: MERGED, CLOSED, OPEN, or NONE
get_pr_status() {
    local branch="$1"
    # Exact, literal field match on the tab-separated <branch>\t<status> map.
    # Using awk (not grep) avoids interpreting regex metacharacters in the
    # branch name as a BRE pattern, which could false-match another branch's
    # PR status. The END{print s} form keeps the LAST matching status, so the
    # open-overrides-closed semantics (open entries appended last) are preserved.
    local status
    status=$(awk -F'\t' -v b="$branch" '$1==b {s=$2} END{print s}' "$PR_MAP_FILE")
    echo "${status:-NONE}"
}

echo ""

# =============================================================================
# PHASE 2: Identify branches checked out in worktrees (protected)
# =============================================================================

header "Phase 2: Identifying protected branches..."
echo ""

PROTECTED_BRANCHES_FILE=$(mktemp)
trap 'rm -f "$PR_MAP_FILE" "${PR_MAP_FILE}.open" "${PR_MAP_FILE}.closed" "$PROTECTED_BRANCHES_FILE"' EXIT

# main is always protected (master was retired via #13577)
echo "main" >> "$PROTECTED_BRANCHES_FILE"

# Branches checked out in worktrees are protected
git worktree list --porcelain 2>/dev/null | grep "^branch refs/heads/" | sed 's|^branch refs/heads/||' >> "$PROTECTED_BRANCHES_FILE"

# Also protect the current branch
current_branch=$(git symbolic-ref --short HEAD 2>/dev/null || echo "")
if [[ -n "$current_branch" ]]; then
    echo "$current_branch" >> "$PROTECTED_BRANCHES_FILE"
fi

protected_count=$(sort -u "$PROTECTED_BRANCHES_FILE" | wc -l | tr -d ' ')
info "  $protected_count branches protected (main, worktree-checked-out)"

is_protected() {
    local branch="$1"
    grep -qxF "$branch" "$PROTECTED_BRANCHES_FILE"
}

echo ""

# =============================================================================
# PHASE 3: Process all local branches
# =============================================================================

header "Phase 3: Processing local branches..."
echo ""

# Counters
deleted_merged=0
deleted_closed=0
deleted_no_pr_even=0
preserved_open=0
preserved_protected=0
preserved_ahead=0
preserved_no_pr=0
failed=0
total_branches=0

# Remote branch counters (--remote)
remote_deleted=0
remote_preserved=0
remote_failed=0

# Get all local branches
all_branches=$(git branch | sed 's/^[*+ ]*//' | sort)
total_local=$(echo "$all_branches" | wc -l | tr -d ' ')

info "  Processing $total_local local branches..."
echo ""

# -----------------------------------------------------------------------------
# Batch precomputation (performance: avoids O(branches) subprocess spawns)
# -----------------------------------------------------------------------------
# The per-branch loop below used to spawn, for EACH local branch:
#   - one `awk` over the whole PR_MAP_FILE (get_pr_status), and
#   - in the NONE case, `git merge-base` + `git rev-list --count`.
# On a ~3k-branch backlog that is ~100-230s of process overhead and times out
# before Phase 4. We replace both with two one-shot passes whose results are
# looked up cheaply inside the loop.
#
# bash 3.2 (macOS) has no associative arrays, so we precompute newline-delimited
# set files and a single resolved TSV, then read them back. No `declare -A`.

# (1) PR status for every local branch in ONE awk-join pass.
#     Joins the branch list against PR_MAP_FILE; last map entry per branch wins
#     (open-overrides-closed, since PR_MAP_FILE appends .open after .closed),
#     matching get_pr_status's END{print s} last-wins semantics exactly. Absent
#     branches resolve to NONE. Output: "<branch>\t<STATUS>" per branch.
RESOLVED_STATUS_FILE=$(mktemp)
NOPR_DELETE_SET_FILE="${RESOLVED_STATUS_FILE}.nopr_delete"
trap 'rm -f "$PR_MAP_FILE" "${PR_MAP_FILE}.open" "${PR_MAP_FILE}.closed" "$PROTECTED_BRANCHES_FILE" "$RESOLVED_STATUS_FILE" "${RESOLVED_STATUS_FILE}.merged" "${RESOLVED_STATUS_FILE}.shares" "$NOPR_DELETE_SET_FILE"' EXIT
printf '%s\n' "$all_branches" \
    | awk -F'\t' '
        NR==FNR { if ($1 != "") m[$1]=$2; next }
        { print $0 "\t" (($1 in m) ? m[$1] : "NONE") }
      ' "$PR_MAP_FILE" - > "$RESOLVED_STATUS_FILE"

# (2) Precompute, in O(1) git calls, the set of no-PR branches the OLD per-branch
#     ahead-count would DELETE, so the NONE fallback is byte-identical.
#
#     OLD logic (lines 408-415 of the pre-change script):
#         merge_base = git merge-base main "$branch"   # EMPTY if no common ancestor
#         ahead = (merge_base != "") ? rev-list --count merge_base..branch : 0
#         DELETE iff ahead == 0
#     So OLD DELETEs a no-PR branch IFF:
#         (a) it is reachable into main (merge-base non-empty, count 0) — i.e.
#             `--merged main`; OR
#         (b) it has NO common ancestor with main (merge-base empty) — the
#             `ahead` default of 0 makes the old code delete orphan-history
#             branches too. In this repo those are the retired-master-root
#             branches from the #13577 divergence (root ecb47b3…, disjoint from
#             main's root). Reproducing this exactly is REQUIRED: a perf refactor
#             must not change which branches get deleted, even where the old rule
#             is surprising.
#
#     Both are computable without per-branch git spawns:
#       MERGED  set = `git for-each-ref --merged main`        (case a)
#       SHARES  set = branches containing one of main's root commits. A branch
#                     shares history with main (non-empty merge-base) IFF its
#                     tip descends from a main root, i.e. it is `--contains
#                     <root>` for some root of main. Its complement is exactly
#                     the empty-merge-base (orphan) set (case b). Verified on the
#                     full 2.9k-branch backlog: contains-root partitions the
#                     branches by merge-base emptiness with zero exceptions.
#     OLD-DELETE(no-PR) = MERGED ∪ (ALL \ SHARES) = MERGED ∪ orphans.
MERGED_SET_FILE="${RESOLVED_STATUS_FILE}.merged"
SHARES_SET_FILE="${RESOLVED_STATUS_FILE}.shares"
git for-each-ref --format='%(refname:short)' --merged main refs/heads 2>/dev/null \
    | sort -u > "$MERGED_SET_FILE" || : > "$MERGED_SET_FILE"

# Branches sharing history with main = union of `--contains <root>` over every
# root commit of main (handles the multi-root case; main has a single root here).
: > "$SHARES_SET_FILE"
while IFS= read -r _root; do
    [[ -z "$_root" ]] && continue
    git for-each-ref --format='%(refname:short)' --contains "$_root" refs/heads 2>/dev/null >> "$SHARES_SET_FILE"
done < <(git rev-list --max-parents=0 main 2>/dev/null)
sort -u -o "$SHARES_SET_FILE" "$SHARES_SET_FILE"

# Old-DELETE(no-PR) set = MERGED ∪ (all local branches NOT in SHARES).
# Built once with set ops; membership tested with grep -qxF (literal, exact).
{
    cat "$MERGED_SET_FILE"
    printf '%s\n' "$all_branches" | sort -u | comm -23 - "$SHARES_SET_FILE"
} | sort -u > "$NOPR_DELETE_SET_FILE"

is_nopr_deletable() {
    # Reproduces the old `ahead == 0` (incl. empty-merge-base) DELETE decision.
    grep -qxF "$1" "$NOPR_DELETE_SET_FILE"
}

# Progress tracking
processed=0
progress_interval=20

# Iterate the resolved "<branch>\t<status>" TSV so the PR status is already
# joined (no per-branch awk). Field 1 = branch, field 2 = resolved PR status.
# The list is read from FD 3 (not stdin), so the interactive `read -r -p`
# prompts inside the loop still consume from the terminal in non-force mode.
while IFS=$'\t' read -r branch pr_status <&3; do
    [[ -z "$branch" ]] && continue
    ((processed++)) || true

    # Show progress every N branches
    if [[ $((processed % progress_interval)) -eq 0 ]]; then
        printf "  Progress: %d/%d branches processed...\r" "$processed" "$total_local"
    fi

    # Skip protected branches
    if is_protected "$branch"; then
        ((preserved_protected++)) || true
        continue
    fi

    ((total_branches++)) || true

    # PR status was resolved in the batch awk-join pass above (read from the
    # resolved TSV's second field). No per-branch awk spawn here.
    case "$pr_status" in
        MERGED)
            ((deleted_merged++)) || true
            if [[ "$DRY_RUN" == true ]]; then
                info "  [DELETE] $branch (PR merged)"
            elif [[ "$FORCE" == true ]]; then
                if git branch -D "$branch" 2>/dev/null; then
                    success "  Deleted: $branch (PR merged)"
                else
                    ((failed++)) || true
                    warning "  Failed to delete: $branch"
                fi
            else
                echo -e "  ${YELLOW}$branch${NC} (PR merged)"
                read -r -p "    Delete? [Y/n] " -n 1 CONFIRM
                echo ""
                if [[ ! $CONFIRM =~ ^[Nn]$ ]]; then
                    git branch -D "$branch" 2>/dev/null && \
                        success "  Deleted: $branch" || \
                        { ((failed++)) || true; warning "  Failed: $branch"; }
                else
                    ((deleted_merged--)) || true
                    ((preserved_no_pr++)) || true
                fi
            fi
            ;;

        CLOSED)
            ((deleted_closed++)) || true
            if [[ "$DRY_RUN" == true ]]; then
                info "  [DELETE] $branch (PR closed)"
            elif [[ "$FORCE" == true ]]; then
                if git branch -D "$branch" 2>/dev/null; then
                    success "  Deleted: $branch (PR closed)"
                else
                    ((failed++)) || true
                    warning "  Failed to delete: $branch"
                fi
            else
                echo -e "  ${YELLOW}$branch${NC} (PR closed)"
                read -r -p "    Delete? [Y/n] " -n 1 CONFIRM
                echo ""
                if [[ ! $CONFIRM =~ ^[Nn]$ ]]; then
                    git branch -D "$branch" 2>/dev/null && \
                        success "  Deleted: $branch" || \
                        { ((failed++)) || true; warning "  Failed: $branch"; }
                else
                    ((deleted_closed--)) || true
                    ((preserved_no_pr++)) || true
                fi
            fi
            ;;

        OPEN)
            ((preserved_open++)) || true
            if [[ "$DRY_RUN" == true ]]; then
                info "  [KEEP]   $branch (PR open)"
            fi
            ;;

        NONE)
            # No PR found. Check if branch has commits ahead of main.
            if [[ "$KEEP_NO_PR" == true ]]; then
                ((preserved_no_pr++)) || true
                if [[ "$DRY_RUN" == true ]]; then
                    info "  [KEEP]   $branch (no PR, --keep-no-pr)"
                fi
                continue
            fi

            # Reproduce the old `ahead == 0` DELETE decision via the precomputed
            # NOPR_DELETE set (built with a couple of one-shot git calls above)
            # instead of per-branch `git merge-base` + `git rev-list --count`.
            # The set is byte-identical to the old test: it is exactly the no-PR
            # branches the old code would delete (merged-into-main OR
            # empty-merge-base orphan).
            if is_nopr_deletable "$branch"; then
                # Branch is even with main - safe to delete
                ((deleted_no_pr_even++)) || true
                if [[ "$DRY_RUN" == true ]]; then
                    info "  [DELETE] $branch (no PR, 0 commits ahead)"
                elif [[ "$FORCE" == true ]]; then
                    if git branch -D "$branch" 2>/dev/null; then
                        success "  Deleted: $branch (no PR, even with main)"
                    else
                        ((failed++)) || true
                        warning "  Failed to delete: $branch"
                    fi
                else
                    echo -e "  ${YELLOW}$branch${NC} (no PR, 0 commits ahead of main)"
                    read -r -p "    Delete? [Y/n] " -n 1 CONFIRM
                    echo ""
                    if [[ ! $CONFIRM =~ ^[Nn]$ ]]; then
                        git branch -D "$branch" 2>/dev/null && \
                            success "  Deleted: $branch" || \
                            { ((failed++)) || true; warning "  Failed: $branch"; }
                    else
                        ((deleted_no_pr_even--)) || true
                        ((preserved_no_pr++)) || true
                    fi
                fi
            else
                # Branch has unique commits - preserve by default
                ((preserved_ahead++)) || true
                if [[ "$DRY_RUN" == true ]]; then
                    warning "  [KEEP]   $branch (no PR, commits ahead of main)"
                fi
            fi
            ;;
    esac
done 3< "$RESOLVED_STATUS_FILE"

# Clear progress line
printf "                                                          \r"

echo ""

# =============================================================================
# PHASE 3b: Process remote branches (--remote)
# =============================================================================
# On a fresh CI checkout `git branch` only lists the default branch, so the
# local-branch phase above is a no-op there. This phase deletes branches on
# origin whose PR is MERGED or CLOSED, reusing the PR map from Phase 1 and the
# same safety rules (never touch main; preserve OPEN-PR and no-PR branches).

if [[ "$REMOTE" == true ]]; then
    header "Phase 3b: Processing remote branches on origin..."
    echo ""

    # Make sure we have an up-to-date view of origin's branches.
    git fetch --prune origin &>/dev/null || warning "  git fetch failed; using cached remote refs"

    # List remote-tracking branches under origin/, stripping the prefix.
    # Skip the symbolic origin/HEAD entry.
    remote_branches=$(git for-each-ref --format='%(refname:short)' refs/remotes/origin \
        | sed 's|^origin/||' \
        | grep -v '^HEAD$' \
        | sort -u)

    remote_total=$(echo "$remote_branches" | grep -c . || true)
    info "  Processing $remote_total remote branches..."
    echo ""

    # Resolve PR status for every remote branch in ONE awk-join pass (same
    # technique as Phase 3) instead of a per-branch awk scan of PR_MAP_FILE.
    # Output: "<branch>\t<STATUS>" per branch; last map entry wins (open
    # overrides closed); absent branches resolve to NONE.
    REMOTE_RESOLVED_FILE=$(mktemp)
    trap 'rm -f "$PR_MAP_FILE" "${PR_MAP_FILE}.open" "${PR_MAP_FILE}.closed" "$PROTECTED_BRANCHES_FILE" "$RESOLVED_STATUS_FILE" "${RESOLVED_STATUS_FILE}.merged" "${RESOLVED_STATUS_FILE}.shares" "$NOPR_DELETE_SET_FILE" "$REMOTE_RESOLVED_FILE"' EXIT
    printf '%s\n' "$remote_branches" \
        | awk -F'\t' '
            NR==FNR { if ($1 != "") m[$1]=$2; next }
            { print $0 "\t" (($1 in m) ? m[$1] : "NONE") }
          ' "$PR_MAP_FILE" - > "$REMOTE_RESOLVED_FILE"

    rprocessed=0
    while IFS=$'\t' read -r branch pr_status; do
        [[ -z "$branch" ]] && continue
        ((rprocessed++)) || true

        if [[ $((rprocessed % progress_interval)) -eq 0 ]]; then
            printf "  Progress: %d/%d remote branches processed...\r" "$rprocessed" "$remote_total"
        fi

        # Never delete the protected default branch on origin.
        if [[ "$branch" == "main" || "$branch" == "master" ]]; then
            ((remote_preserved++)) || true
            continue
        fi

        case "$pr_status" in
            MERGED|CLOSED)
                if [[ "$DRY_RUN" == true ]]; then
                    info "  [DELETE] origin/$branch (PR $pr_status)"
                    ((remote_deleted++)) || true
                else
                    if git push origin --delete "$branch" &>/dev/null; then
                        success "  Deleted: origin/$branch (PR $pr_status)"
                        ((remote_deleted++)) || true
                    else
                        warning "  Failed to delete: origin/$branch"
                        ((remote_failed++)) || true
                    fi
                fi
                ;;
            *)
                # OPEN PR or NONE: preserve.
                ((remote_preserved++)) || true
                if [[ "$DRY_RUN" == true ]]; then
                    info "  [KEEP]   origin/$branch (PR ${pr_status:-NONE})"
                fi
                ;;
        esac
    done < "$REMOTE_RESOLVED_FILE"

    # Clear progress line
    printf "                                                          \r"
    echo ""
fi

# =============================================================================
# PHASE 4: Worktree cleanup
# =============================================================================

header "Phase 4: Cleaning worktrees..."
echo ""

worktrees_removed=0
worktrees_preserved=0

# --- .claude/worktrees/agent-* ---

header "  Checking .claude/worktrees/..."

if [[ -d "$REPO_ROOT/.claude/worktrees" ]]; then
    for wt_dir in "$REPO_ROOT/.claude/worktrees"/*/; do
        [[ ! -d "$wt_dir" ]] && continue
        wt_name=$(basename "$wt_dir")

        # Check if there is an active claude process for this worktree
        has_active_process=false
        if pgrep -f "claude.*${wt_dir}" &>/dev/null; then
            has_active_process=true
        fi

        if [[ "$has_active_process" == true ]]; then
            ((worktrees_preserved++)) || true
            info "    Preserving: .claude/worktrees/$wt_name (active claude process)"
        else
            ((worktrees_removed++)) || true
            if [[ "$DRY_RUN" == true ]]; then
                info "    [REMOVE] .claude/worktrees/$wt_name (no active process)"
            elif [[ "$FORCE" == true ]]; then
                git worktree remove "$wt_dir" --force 2>/dev/null && \
                    success "    Removed: .claude/worktrees/$wt_name" || \
                    { warning "    Failed to remove worktree, cleaning directory..."; rm -rf "$wt_dir"; }
            else
                echo -e "    ${YELLOW}.claude/worktrees/$wt_name${NC} (no active process)"
                read -r -p "      Remove? [Y/n] " -n 1 CONFIRM
                echo ""
                if [[ ! $CONFIRM =~ ^[Nn]$ ]]; then
                    git worktree remove "$wt_dir" --force 2>/dev/null && \
                        success "    Removed: .claude/worktrees/$wt_name" || \
                        { warning "    Failed to remove worktree, cleaning directory..."; rm -rf "$wt_dir"; }
                else
                    ((worktrees_removed--)) || true
                    ((worktrees_preserved++)) || true
                fi
            fi
        fi
    done
else
    info "    No .claude/worktrees/ directory found"
fi

echo ""

# --- .loom/worktrees/issue-* (closed issues) ---

header "  Checking .loom/worktrees/issue-*..."

for wt_dir in "$REPO_ROOT/.loom/worktrees"/issue-*/; do
    [[ ! -d "$wt_dir" ]] && continue
    wt_name=$(basename "$wt_dir")
    issue_num="${wt_name#issue-}"

    # Check if issue is closed
    issue_state=$(gh issue view "$issue_num" --json state -q '.state' 2>/dev/null || echo "UNKNOWN")

    if [[ "$issue_state" == "CLOSED" ]]; then
        ((worktrees_removed++)) || true
        if [[ "$DRY_RUN" == true ]]; then
            info "    [REMOVE] .loom/worktrees/$wt_name (issue closed)"
        elif [[ "$FORCE" == true ]]; then
            git worktree remove "$wt_dir" --force 2>/dev/null && \
                success "    Removed: .loom/worktrees/$wt_name (issue #$issue_num closed)" || \
                { warning "    Failed git worktree remove, cleaning directory..."; rm -rf "$wt_dir"; }
        else
            echo -e "    ${YELLOW}.loom/worktrees/$wt_name${NC} (issue #$issue_num closed)"
            read -r -p "      Remove? [Y/n] " -n 1 CONFIRM
            echo ""
            if [[ ! $CONFIRM =~ ^[Nn]$ ]]; then
                git worktree remove "$wt_dir" --force 2>/dev/null && \
                    success "    Removed: .loom/worktrees/$wt_name" || \
                    { warning "    Fallback: rm -rf"; rm -rf "$wt_dir"; }
            else
                ((worktrees_removed--)) || true
                ((worktrees_preserved++)) || true
            fi
        fi
    else
        ((worktrees_preserved++)) || true
        info "    Preserving: .loom/worktrees/$wt_name (issue $issue_state)"
    fi
done

echo ""

# --- .loom/worktrees/temp-* (temporary rebase worktrees) ---

header "  Checking .loom/worktrees/temp-*..."

for wt_dir in "$REPO_ROOT/.loom/worktrees"/temp-*/; do
    [[ ! -d "$wt_dir" ]] && continue
    wt_name=$(basename "$wt_dir")

    ((worktrees_removed++)) || true
    if [[ "$DRY_RUN" == true ]]; then
        info "    [REMOVE] .loom/worktrees/$wt_name (temporary)"
    elif [[ "$FORCE" == true ]]; then
        git worktree remove "$wt_dir" --force 2>/dev/null && \
            success "    Removed: .loom/worktrees/$wt_name" || \
            { warning "    Fallback: rm -rf"; rm -rf "$wt_dir"; }
    else
        echo -e "    ${YELLOW}.loom/worktrees/$wt_name${NC} (temporary)"
        read -r -p "      Remove? [Y/n] " -n 1 CONFIRM
        echo ""
        if [[ ! $CONFIRM =~ ^[Nn]$ ]]; then
            git worktree remove "$wt_dir" --force 2>/dev/null && \
                success "    Removed: .loom/worktrees/$wt_name" || \
                { warning "    Fallback: rm -rf"; rm -rf "$wt_dir"; }
        else
            ((worktrees_removed--)) || true
            ((worktrees_preserved++)) || true
        fi
    fi
done

echo ""

# --- .loom/worktrees/* (generic scratch sweep) ---
#
# The issue-* and temp-* passes above only cover two naming conventions. The
# bulk of accumulated disk lives under workflow-scratch names that match
# neither (audit-*, auditor-*, mechanic-*, researcher-*, enricher-*, …). This
# generic pass reclaims them SAFELY, mirroring the .claude/worktrees/* pass:
# a worktree is removed only when it is provably disposable.
#
# A worktree is REMOVED only when ALL of these hold:
#   - it is NOT the current checkout
#   - it is NOT locked (`git worktree list` does not flag it `locked`)
#   - no active owning process (pgrep on the worktree path)
#   - clean working tree (`git status --porcelain` empty)
#   - no commits that exist on no remote. With an upstream, `@{u}..HEAD` must
#     be empty. WITHOUT an upstream, HEAD must be reachable from some remote
#     ref (`git branch -r --contains HEAD` non-empty) — "no upstream" is NOT
#     treated as "nothing to lose", since a never-pushed branch can carry
#     local-only commits.
#   - its branch's PR is NOT OPEN (an OPEN PR is always preserved)
#   - AND it is reclaimable: its branch's PR is MERGED/CLOSED, OR its upstream
#     branch is gone on origin, OR its mtime exceeds WORKTREE_MAX_AGE_DAYS.
# Anything failing a single guard is PRESERVED. Default stays interactive;
# --force is non-interactive.
#
# Decision table for the reclaim path (after the structural guards pass):
#   PR OPEN              + stale         => PRESERVE (open-PR guard)
#   PR OPEN              + recent        => PRESERVE (open-PR guard)
#   PR MERGED/CLOSED                     => REMOVE   (reason: PR <status>)
#   no upstream + HEAD on no remote ref  => PRESERVE (unbacked local commits)
#   no upstream + HEAD on a remote ref + stale  => REMOVE (reason: stale)
#   no upstream + HEAD on a remote ref + recent => PRESERVE (unmerged, recent)
#   upstream gone on origin              => REMOVE   (reason: upstream gone)
#   upstream present + stale             => REMOVE   (reason: stale)
#   upstream present + recent            => PRESERVE (unmerged, recent)

header "  Checking .loom/worktrees/* (scratch)..."

# Resolve the current checkout's worktree path so we never remove ourselves.
current_wt_path="$(git rev-parse --show-toplevel 2>/dev/null || echo "")"

# Build the set of locked worktree paths once (porcelain marks them `locked`).
locked_wt_paths=$(git worktree list --porcelain 2>/dev/null \
    | awk '/^worktree /{p=$2} /^locked/{print p}')

is_locked_wt() {
    local path="$1"
    [[ -n "$locked_wt_paths" ]] && grep -qxF "$path" <<< "$locked_wt_paths"
}

if [[ -d "$REPO_ROOT/.loom/worktrees" ]]; then
    for wt_dir in "$REPO_ROOT/.loom/worktrees"/*/; do
        [[ ! -d "$wt_dir" ]] && continue
        wt_name=$(basename "$wt_dir")

        # Skip names handled by the dedicated passes above.
        case "$wt_name" in
            issue-*|temp-*) continue ;;
        esac

        # Normalize trailing slash for path comparisons.
        wt_path="${wt_dir%/}"
        wt_real="$(cd "$wt_path" 2>/dev/null && pwd -P || echo "$wt_path")"

        # GUARD: never remove the current checkout.
        if [[ -n "$current_wt_path" && "$wt_real" == "$(cd "$current_wt_path" 2>/dev/null && pwd -P || echo "$current_wt_path")" ]]; then
            ((worktrees_preserved++)) || true
            info "    Preserving: .loom/worktrees/$wt_name (current checkout)"
            continue
        fi

        # GUARD: never remove a locked worktree.
        if is_locked_wt "$wt_path"; then
            ((worktrees_preserved++)) || true
            info "    Preserving: .loom/worktrees/$wt_name (locked)"
            continue
        fi

        # GUARD: never remove a worktree with an active owning process.
        if pgrep -f "$wt_path" &>/dev/null; then
            ((worktrees_preserved++)) || true
            info "    Preserving: .loom/worktrees/$wt_name (active process)"
            continue
        fi

        # GUARD: never remove a worktree with a dirty working tree.
        if [[ -n "$(git -C "$wt_path" status --porcelain 2>/dev/null)" ]]; then
            ((worktrees_preserved++)) || true
            info "    Preserving: .loom/worktrees/$wt_name (uncommitted changes)"
            continue
        fi

        # GUARD: never remove a worktree carrying commits that exist on no
        # remote. Two cases must both be covered:
        #   - upstream IS configured: preserve if `@{u}..HEAD` is non-empty
        #     (real commits ahead of the tracked remote branch).
        #   - upstream is NOT configured (@{u} unresolved): "no upstream" is
        #     NOT "nothing to lose". A never-pushed branch can carry local-only
        #     exploratory commits. Preserve unless HEAD is reachable from some
        #     remote ref (`git branch -r --contains HEAD` non-empty ⇒ backed up
        #     on a remote ⇒ safe). If no remote branch contains HEAD, the
        #     commits are unbacked ⇒ preserve.
        if git -C "$wt_path" rev-parse --abbrev-ref --symbolic-full-name '@{u}' &>/dev/null; then
            unpushed=$(git -C "$wt_path" log --oneline '@{u}..HEAD' 2>/dev/null || echo "")
            if [[ -n "$unpushed" ]]; then
                ((worktrees_preserved++)) || true
                info "    Preserving: .loom/worktrees/$wt_name (unpushed commits)"
                continue
            fi
        else
            # No upstream configured: is HEAD backed up on any remote ref?
            remote_containing=$(git -C "$wt_path" branch -r --contains HEAD 2>/dev/null \
                | grep -v '\->' | sed 's/^[[:space:]]*//' | head -n 1)
            if [[ -z "$remote_containing" ]]; then
                ((worktrees_preserved++)) || true
                info "    Preserving: .loom/worktrees/$wt_name (no upstream; HEAD not on any remote)"
                continue
            fi
        fi

        # Determine reclaim eligibility. Removed only if at least one of:
        #   (a) the branch's PR is MERGED/CLOSED,
        #   (b) the upstream branch is gone on origin, or
        #   (c) the worktree mtime exceeds WORKTREE_MAX_AGE_DAYS.
        wt_branch=$(git -C "$wt_path" symbolic-ref --short HEAD 2>/dev/null || echo "")
        reclaim_reason=""

        if [[ -n "$wt_branch" ]]; then
            pr_status=$(get_pr_status "$wt_branch")
            # GUARD: an OPEN PR must ALWAYS be preserved, regardless of mtime.
            # Without this, a long-lived feature branch under active review
            # whose dir mtime drifts past WORKTREE_MAX_AGE_DAYS would fall
            # through to path (c) and be removed. Preserve before any mtime
            # check.
            if [[ "$pr_status" == "OPEN" ]]; then
                ((worktrees_preserved++)) || true
                info "    Preserving: .loom/worktrees/$wt_name (open PR)"
                continue
            fi
            if [[ "$pr_status" == "MERGED" || "$pr_status" == "CLOSED" ]]; then
                reclaim_reason="PR $pr_status"
            fi
        fi

        # (b) Upstream gone on origin: branch tracks origin but the remote ref
        # no longer exists (a fetch --prune would drop it).
        if [[ -z "$reclaim_reason" && -n "$wt_branch" ]]; then
            upstream=$(git -C "$wt_path" rev-parse --abbrev-ref --symbolic-full-name '@{u}' 2>/dev/null || echo "")
            if [[ -n "$upstream" ]] && ! git -C "$wt_path" rev-parse --verify --quiet "refs/remotes/$upstream" &>/dev/null; then
                reclaim_reason="upstream gone on origin"
            fi
        fi

        # (c) Stale by mtime.
        if [[ -z "$reclaim_reason" ]]; then
            now_epoch=$(date +%s)
            wt_mtime=$(stat -f %m "$wt_path" 2>/dev/null || stat -c %Y "$wt_path" 2>/dev/null || echo "$now_epoch")
            age_days=$(( (now_epoch - wt_mtime) / 86400 ))
            if [[ "$age_days" -gt "$WORKTREE_MAX_AGE_DAYS" ]]; then
                reclaim_reason="stale ${age_days}d > ${WORKTREE_MAX_AGE_DAYS}d"
            fi
        fi

        if [[ -z "$reclaim_reason" ]]; then
            ((worktrees_preserved++)) || true
            info "    Preserving: .loom/worktrees/$wt_name (unmerged, recent)"
            continue
        fi

        ((worktrees_removed++)) || true
        if [[ "$DRY_RUN" == true ]]; then
            info "    [REMOVE] .loom/worktrees/$wt_name ($reclaim_reason)"
        elif [[ "$FORCE" == true ]]; then
            git worktree remove "$wt_path" --force 2>/dev/null && \
                success "    Removed: .loom/worktrees/$wt_name ($reclaim_reason)" || \
                { warning "    Fallback: rm -rf"; rm -rf "$wt_path"; }
        else
            echo -e "    ${YELLOW}.loom/worktrees/$wt_name${NC} ($reclaim_reason)"
            read -r -p "      Remove? [Y/n] " -n 1 CONFIRM
            echo ""
            if [[ ! $CONFIRM =~ ^[Nn]$ ]]; then
                git worktree remove "$wt_path" --force 2>/dev/null && \
                    success "    Removed: .loom/worktrees/$wt_name" || \
                    { warning "    Fallback: rm -rf"; rm -rf "$wt_path"; }
            else
                ((worktrees_removed--)) || true
                ((worktrees_preserved++)) || true
            fi
        fi
    done
else
    info "    No .loom/worktrees/ directory found"
fi

echo ""

# --- git worktree prune ---

header "  Pruning orphaned worktree references..."
if [[ "$DRY_RUN" == true ]]; then
    git worktree prune --dry-run --verbose 2>&1 || true
else
    git worktree prune --verbose 2>&1 || true
fi

echo ""

# =============================================================================
# PHASE 5: Prune remote tracking refs
# =============================================================================

header "Phase 5: Pruning remote tracking refs..."
echo ""

if [[ "$DRY_RUN" == true ]]; then
    info "  Would run: git fetch --prune"
else
    git fetch --prune 2>&1 | head -20 || true
    success "  Remote tracking refs pruned"
fi

echo ""

# =============================================================================
# SUMMARY
# =============================================================================

total_deleted=$((deleted_merged + deleted_closed + deleted_no_pr_even))
total_preserved=$((preserved_open + preserved_protected + preserved_ahead + preserved_no_pr))

header "============================================================"
header "                       SUMMARY"
header "============================================================"
echo ""

if [[ "$DRY_RUN" == true ]]; then
    echo -e "  ${BOLD}Mode:${NC} DRY RUN (no changes made)"
else
    echo -e "  ${BOLD}Mode:${NC} $(if [[ "$FORCE" == true ]]; then echo "Force (non-interactive)"; else echo "Interactive"; fi)"
fi
echo ""

echo -e "  ${BOLD}Branches:${NC}"
echo -e "    ${GREEN}Deleted (PR merged):${NC}      $deleted_merged"
echo -e "    ${GREEN}Deleted (PR closed):${NC}      $deleted_closed"
echo -e "    ${GREEN}Deleted (no PR, even):${NC}    $deleted_no_pr_even"
echo -e "    ${BLUE}Preserved (PR open):${NC}      $preserved_open"
echo -e "    ${BLUE}Preserved (protected):${NC}    $preserved_protected"
echo -e "    ${YELLOW}Preserved (ahead, no PR):${NC} $preserved_ahead"
echo -e "    ${BLUE}Preserved (other):${NC}        $preserved_no_pr"
if [[ $failed -gt 0 ]]; then
    echo -e "    ${RED}Failed:${NC}                   $failed"
fi
echo -e "    ${BOLD}Total deleted:${NC}            $total_deleted / $((total_branches + preserved_protected)) branches"
echo ""

if [[ "$REMOTE" == true ]]; then
    echo -e "  ${BOLD}Remote branches (origin):${NC}"
    echo -e "    ${GREEN}Deleted (PR merged/closed):${NC} $remote_deleted"
    echo -e "    ${BLUE}Preserved:${NC}                  $remote_preserved"
    if [[ $remote_failed -gt 0 ]]; then
        echo -e "    ${RED}Failed:${NC}                     $remote_failed"
    fi
    echo ""
fi

echo -e "  ${BOLD}Worktrees:${NC}"
echo -e "    ${GREEN}Removed:${NC}    $worktrees_removed"
echo -e "    ${BLUE}Preserved:${NC}  $worktrees_preserved"
echo ""

if [[ "$DRY_RUN" == true ]]; then
    info "  To execute: ./scripts/clean-branches.sh --force"
else
    success "  Cleanup complete!"
fi

echo ""
