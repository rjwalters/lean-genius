#!/usr/bin/env bash
#
# clean-enhancers.sh - Clean up stale enhancement agent artifacts
#
# Usage: ./scripts/erdos/clean-enhancers.sh [options]
#
# Options:
#   --dry-run    Show what would be cleaned without making changes
#   --deep       Deep clean (includes worktrees with uncommitted work)
#   -f, --force  Non-interactive mode (auto-confirm all prompts)
#   -h, --help   Show this help message
#
# Cleans:
#   - Stale claims (expired TTL)
#   - Orphaned worktrees (erdos-{N} and enhancer-{N})
#   - Merged/closed branches (feature/erdos-{N}-enhance)
#   - Stop signals (.loom/signals/stop-*)
#   - Agent logs (.loom/logs/erdos-enhancer-*.log)

set -euo pipefail

# ANSI color codes
RED='\033[0;31m'
GREEN='\033[0;32m'
BLUE='\033[0;34m'
YELLOW='\033[1;33m'
CYAN='\033[0;36m'
NC='\033[0m'

error() {
  echo -e "${RED}Error: $*${NC}" >&2
  exit 1
}

info() {
  echo -e "${BLUE}$*${NC}"
}

success() {
  echo -e "${GREEN}$*${NC}"
}

warning() {
  echo -e "${YELLOW}$*${NC}"
}

header() {
  echo -e "${CYAN}$*${NC}"
}

# Find git repository root
find_repo_root() {
    local dir="$PWD"
    while [[ "$dir" != "/" ]]; do
        if [[ -d "$dir/.git" ]]; then
            echo "$dir"
            return 0
        fi
        dir="$(dirname "$dir")"
    done
    echo "Error: Not in a git repository" >&2
    return 1
}

REPO_ROOT="$(find_repo_root)"
CLAIMS_DIR="$REPO_ROOT/research/stub-claims"
WORKTREES_DIR="$REPO_ROOT/.loom/worktrees"
SIGNALS_DIR="$REPO_ROOT/.loom/signals"
LOGS_DIR="$REPO_ROOT/.loom/logs"

# Parse arguments
DRY_RUN=false
DEEP_CLEAN=false
FORCE=false

for arg in "$@"; do
  case $arg in
    --dry-run)
      DRY_RUN=true
      shift
      ;;
    --deep)
      DEEP_CLEAN=true
      shift
      ;;
    --force|-f)
      FORCE=true
      shift
      ;;
    --help|-h)
      cat << 'EOF'
Enhancement Agent Cleanup - Clean up stale enhancement artifacts

Usage: ./scripts/erdos/clean-enhancers.sh [options]

Options:
  --dry-run    Show what would be cleaned without making changes
  --deep       Deep clean (includes worktrees with uncommitted work)
  -f, --force  Non-interactive mode (auto-confirm all prompts)
  -h, --help   Show this help message

Standard cleanup:
  - Stale claims (expired TTL in research/stub-claims/)
  - Orphaned lock directories
  - Stop signals (.loom/signals/stop-*)

Deep cleanup (--deep):
  - All of the above, plus:
  - Worktrees for merged PRs (erdos-{N}, enhancer-{N})
  - Local branches for closed issues (feature/erdos-{N}-enhance)
  - Old agent logs (.loom/logs/erdos-enhancer-*.log)

EOF
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
if [[ "$DEEP_CLEAN" == true ]]; then
  header "         Enhancement Agent Deep Cleanup"
else
  header "         Enhancement Agent Cleanup"
fi
if [[ "$DRY_RUN" == true ]]; then
  header "                  (DRY RUN MODE)"
fi
header "============================================================"
echo ""

cd "$REPO_ROOT"

# Check if claim is expired
is_claim_expired() {
    local claim_file="$1"
    if [[ ! -f "$claim_file" ]]; then
        return 0  # No claim file = "expired"
    fi

    local expires_at
    expires_at=$(jq -r '.expires_at' "$claim_file" 2>/dev/null || echo "1970-01-01T00:00:00Z")

    local now_epoch expires_epoch
    now_epoch=$(date -u +%s)

    if [[ "$(uname)" == "Darwin" ]]; then
        # Strip Z suffix and parse as UTC - macOS date -j doesn't respect Z timezone suffix
        local clean_ts="${expires_at%Z}"
        expires_epoch=$(TZ=UTC date -j -f "%Y-%m-%dT%H:%M:%S" "$clean_ts" +%s 2>/dev/null || echo 0)
    else
        expires_epoch=$(date -d "$expires_at" +%s 2>/dev/null || echo 0)
    fi

    [[ $now_epoch -gt $expires_epoch ]]
}

# =============================================================================
# CLEANUP: Stale Claims
# =============================================================================

header "Cleaning Stale Claims"
echo ""

stale_claims=0
active_claims=0

if [[ -d "$CLAIMS_DIR" ]]; then
    for lock_dir in "$CLAIMS_DIR"/*.lock; do
        [[ ! -d "$lock_dir" ]] && continue

        erdos_num=$(basename "$lock_dir" .lock | sed 's/erdos-//')
        claim_file="$CLAIMS_DIR/erdos-$erdos_num.json"

        if is_claim_expired "$claim_file"; then
            ((stale_claims++))
            if [[ "$DRY_RUN" == true ]]; then
                info "Would clean stale claim: erdos-$erdos_num"
            else
                rm -rf "$lock_dir"
                rm -f "$claim_file"
                success "Cleaned stale claim: erdos-$erdos_num"
            fi
        else
            ((active_claims++))
            info "Active claim: erdos-$erdos_num (preserving)"
        fi
    done
fi

if [[ $stale_claims -eq 0 ]]; then
    success "No stale claims found"
else
    echo ""
    info "Stale claims: $stale_claims, Active claims: $active_claims"
fi

echo ""

# =============================================================================
# CLEANUP: Stop Signals
# =============================================================================

header "Cleaning Stop Signals"
echo ""

signal_count=0

if [[ -d "$SIGNALS_DIR" ]]; then
    for signal_file in "$SIGNALS_DIR"/stop-*; do
        [[ ! -e "$signal_file" ]] && continue

        # Only clean enhancer-related signals
        signal_name=$(basename "$signal_file")
        if [[ "$signal_name" == "stop-all" || "$signal_name" == stop-enhancer-* ]]; then
            ((signal_count++))
            if [[ "$DRY_RUN" == true ]]; then
                info "Would remove signal: $signal_name"
            else
                rm -f "$signal_file"
                success "Removed signal: $signal_name"
            fi
        fi
    done
fi

if [[ $signal_count -eq 0 ]]; then
    success "No stop signals found"
fi

echo ""

# =============================================================================
# DEEP CLEANUP: Worktrees and Branches
# =============================================================================

if [[ "$DEEP_CLEAN" == true ]]; then
    header "Deep Cleaning Worktrees"
    echo ""

    worktree_count=0

    if [[ -d "$WORKTREES_DIR" ]]; then
        # Clean erdos-{N} worktrees for merged/closed PRs
        for worktree_dir in "$WORKTREES_DIR"/erdos-*; do
            [[ ! -d "$worktree_dir" ]] && continue

            erdos_num=$(basename "$worktree_dir" | sed 's/erdos-//')
            branch_name="feature/erdos-$erdos_num-enhance"

            # Check if PR exists and is merged/closed
            pr_state="unknown"
            if command -v gh &> /dev/null; then
                pr_state=$(gh pr list --head "$branch_name" --state all --json state --jq '.[0].state // "none"' 2>/dev/null || echo "unknown")
            fi

            should_clean=false
            if [[ "$pr_state" == "MERGED" || "$pr_state" == "CLOSED" ]]; then
                should_clean=true
                reason="PR $pr_state"
            elif [[ "$pr_state" == "none" ]]; then
                # No PR exists - check if branch has been deleted from remote
                if ! git ls-remote --heads origin "$branch_name" 2>/dev/null | grep -q "$branch_name"; then
                    should_clean=true
                    reason="branch deleted"
                fi
            fi

            if [[ "$should_clean" == true ]]; then
                ((worktree_count++))
                if [[ "$DRY_RUN" == true ]]; then
                    info "Would remove worktree: erdos-$erdos_num ($reason)"
                elif [[ "$FORCE" == true ]]; then
                    git worktree remove "$worktree_dir" --force 2>/dev/null && \
                        success "Removed worktree: erdos-$erdos_num ($reason)" || \
                        warning "Failed to remove: erdos-$erdos_num"
                else
                    echo -e "  ${YELLOW}erdos-$erdos_num${NC} ($reason)"
                    read -r -p "  Remove this worktree? [y/N] " -n 1 CONFIRM
                    echo ""
                    if [[ $CONFIRM =~ ^[Yy]$ ]]; then
                        git worktree remove "$worktree_dir" --force 2>/dev/null && \
                            success "Removed worktree: erdos-$erdos_num" || \
                            warning "Failed to remove: erdos-$erdos_num"
                    else
                        info "Skipping: erdos-$erdos_num"
                    fi
                fi
            else
                info "Preserving worktree: erdos-$erdos_num (active work)"
            fi
        done

        # Clean enhancer-{N} worktrees
        for worktree_dir in "$WORKTREES_DIR"/enhancer-*; do
            [[ ! -d "$worktree_dir" ]] && continue

            enhancer_num=$(basename "$worktree_dir" | sed 's/enhancer-//')

            # Check if enhancer has any active claims
            has_active_work=false
            for claim_file in "$CLAIMS_DIR"/*.json; do
                [[ ! -f "$claim_file" ]] && continue
                agent_id=$(jq -r '.agent_id' "$claim_file" 2>/dev/null || echo "")
                if [[ "$agent_id" == "enhancer-$enhancer_num" ]] && ! is_claim_expired "$claim_file"; then
                    has_active_work=true
                    break
                fi
            done

            if [[ "$has_active_work" == false ]]; then
                ((worktree_count++))
                if [[ "$DRY_RUN" == true ]]; then
                    info "Would remove worktree: enhancer-$enhancer_num (no active claims)"
                elif [[ "$FORCE" == true ]]; then
                    git worktree remove "$worktree_dir" --force 2>/dev/null && \
                        success "Removed worktree: enhancer-$enhancer_num" || \
                        warning "Failed to remove: enhancer-$enhancer_num"
                else
                    echo -e "  ${YELLOW}enhancer-$enhancer_num${NC} (no active claims)"
                    read -r -p "  Remove this worktree? [y/N] " -n 1 CONFIRM
                    echo ""
                    if [[ $CONFIRM =~ ^[Yy]$ ]]; then
                        git worktree remove "$worktree_dir" --force 2>/dev/null && \
                            success "Removed worktree: enhancer-$enhancer_num" || \
                            warning "Failed to remove: enhancer-$enhancer_num"
                    else
                        info "Skipping: enhancer-$enhancer_num"
                    fi
                fi
            else
                info "Preserving worktree: enhancer-$enhancer_num (active claims)"
            fi
        done
    fi

    if [[ $worktree_count -eq 0 ]]; then
        success "No stale worktrees found"
    fi

    # Prune orphaned worktree references
    echo ""
    info "Pruning orphaned worktree references..."
    if [[ "$DRY_RUN" == true ]]; then
        git worktree prune --dry-run --verbose 2>&1 || true
    else
        git worktree prune --verbose 2>&1 || true
    fi

    echo ""
    header "Deep Cleaning Branches"
    echo ""

    branch_count=0

    # Find feature/erdos-*-enhance branches
    branches=$(git branch | grep "feature/erdos-.*-enhance" | sed 's/^[*+ ]*//' || true)

    if [[ -n "$branches" ]]; then
        for branch in $branches; do
            erdos_num=$(echo "$branch" | sed 's/feature\/erdos-//' | sed 's/-enhance//')

            # Check if PR is merged/closed
            pr_state="unknown"
            if command -v gh &> /dev/null; then
                pr_state=$(gh pr list --head "$branch" --state all --json state --jq '.[0].state // "none"' 2>/dev/null || echo "unknown")
            fi

            if [[ "$pr_state" == "MERGED" ]]; then
                ((branch_count++))
                if [[ "$DRY_RUN" == true ]]; then
                    info "Would delete branch: $branch (PR merged)"
                else
                    git branch -D "$branch" 2>/dev/null && \
                        success "Deleted branch: $branch (PR merged)" || \
                        warning "Failed to delete: $branch"
                fi
            elif [[ "$pr_state" == "CLOSED" ]]; then
                ((branch_count++))
                if [[ "$DRY_RUN" == true ]]; then
                    info "Would delete branch: $branch (PR closed)"
                else
                    git branch -D "$branch" 2>/dev/null && \
                        success "Deleted branch: $branch (PR closed)" || \
                        warning "Failed to delete: $branch"
                fi
            else
                info "Preserving branch: $branch (PR $pr_state)"
            fi
        done
    fi

    # Also clean enhancer-{N} branches
    enhancer_branches=$(git branch | grep "feature/enhancer-" | sed 's/^[*+ ]*//' || true)

    if [[ -n "$enhancer_branches" ]]; then
        for branch in $enhancer_branches; do
            enhancer_num=$(echo "$branch" | sed 's/feature\/enhancer-//')

            # Check if any worktree uses this branch
            worktree_exists=false
            if [[ -d "$WORKTREES_DIR/enhancer-$enhancer_num" ]]; then
                worktree_exists=true
            fi

            if [[ "$worktree_exists" == false ]]; then
                ((branch_count++))
                if [[ "$DRY_RUN" == true ]]; then
                    info "Would delete branch: $branch (no worktree)"
                else
                    git branch -D "$branch" 2>/dev/null && \
                        success "Deleted branch: $branch (no worktree)" || \
                        warning "Failed to delete: $branch"
                fi
            fi
        done
    fi

    if [[ $branch_count -eq 0 ]]; then
        success "No stale branches found"
    fi

    echo ""
    header "Deep Cleaning Logs"
    echo ""

    log_count=0
    log_size="0"

    if [[ -d "$LOGS_DIR" ]]; then
        # Count and measure logs
        for log_file in "$LOGS_DIR"/erdos-enhancer-*.log "$LOGS_DIR"/erdos-enhancer-*-prompt.md "$LOGS_DIR"/erdos-enhancer-*-prompt.txt; do
            [[ ! -f "$log_file" ]] && continue
            ((log_count++))
        done

        if [[ $log_count -gt 0 ]]; then
            log_size=$(du -sh "$LOGS_DIR"/erdos-enhancer-* 2>/dev/null | tail -1 | cut -f1 || echo "unknown")

            if [[ "$DRY_RUN" == true ]]; then
                info "Would remove $log_count enhancer log files ($log_size)"
            elif [[ "$FORCE" == true ]]; then
                rm -f "$LOGS_DIR"/erdos-enhancer-*.log "$LOGS_DIR"/erdos-enhancer-*-prompt.md "$LOGS_DIR"/erdos-enhancer-*-prompt.txt
                success "Removed $log_count enhancer log files ($log_size)"
            else
                echo -e "  Found ${YELLOW}$log_count${NC} log files ($log_size)"
                read -r -p "  Remove all enhancer logs? [y/N] " -n 1 CONFIRM
                echo ""
                if [[ $CONFIRM =~ ^[Yy]$ ]]; then
                    rm -f "$LOGS_DIR"/erdos-enhancer-*.log "$LOGS_DIR"/erdos-enhancer-*-prompt.md "$LOGS_DIR"/erdos-enhancer-*-prompt.txt
                    success "Removed $log_count enhancer log files"
                else
                    info "Skipping log cleanup"
                fi
            fi
        else
            success "No enhancer logs found"
        fi
    else
        success "No logs directory found"
    fi

    echo ""
fi

# =============================================================================
# SUMMARY
# =============================================================================

echo ""
header "============================================================"
echo ""

if [[ "$DRY_RUN" == true ]]; then
    success "Dry run complete - no changes made"
    echo ""
    info "To actually clean, run: ./scripts/erdos/clean-enhancers.sh"
    if [[ "$DEEP_CLEAN" == true ]]; then
        echo "                        ./scripts/erdos/clean-enhancers.sh --deep"
    fi
else
    success "Enhancement agent cleanup complete!"
fi

echo ""
