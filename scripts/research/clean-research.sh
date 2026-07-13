#!/usr/bin/env bash
#
# clean-research.sh - Clean up stale research agent artifacts
#
# Usage: ./scripts/research/clean-research.sh [options]
#
# Options:
#   --dry-run    Show what would be cleaned without making changes
#   --deep       Deep clean (includes worktrees with uncommitted work)
#   -f, --force  Non-interactive mode (auto-confirm all prompts)
#   -h, --help   Show this help message
#
# Cleans:
#   - Stale claims (expired TTL)
#   - Orphaned worktrees (researcher-{N})
#   - Merged/closed branches (feature/researcher-{N})
#   - Stop signals (.loom/signals/stop-researcher-*)
#   - Agent logs (.loom/logs/researcher-*.log)

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
        if [[ -d "$dir/.git" ]] || [[ -f "$dir/.git" ]]; then
            echo "$dir"
            return 0
        fi
        dir="$(dirname "$dir")"
    done
    echo "Error: Not in a git repository" >&2
    return 1
}

REPO_ROOT="$(find_repo_root)"
CLAIMS_DIR="$REPO_ROOT/research/claims"
WORKTREES_DIR="$REPO_ROOT/.loom/worktrees"
SIGNALS_DIR="$REPO_ROOT/.loom/signals"
LOGS_DIR="$REPO_ROOT/.loom/logs"

# Shared worktree reclaim helper (remove_own_worktree, guards 1-5). The deep
# worktree cleanup below routes every removal through these structural guards so
# a dirty tree, unpushed commits, a live owning process, or a locked/current
# worktree is never force-removed — even when the claim tracker shows no active
# claim (issue #35256). Mirrors parallel-research.sh's reclaim_worktrees().
# shellcheck source=../lib/worktree-cleanup.sh
source "$REPO_ROOT/scripts/lib/worktree-cleanup.sh"

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
Research Agent Cleanup - Clean up stale research artifacts

Usage: ./scripts/research/clean-research.sh [options]

Options:
  --dry-run    Show what would be cleaned without making changes
  --deep       Deep clean (includes worktrees with uncommitted work)
  -f, --force  Non-interactive mode (auto-confirm all prompts)
  -h, --help   Show this help message

Standard cleanup:
  - Stale claims (expired TTL in research/claims/)
  - Orphaned lock directories
  - Stop signals (.loom/signals/stop-researcher-*)

Deep cleanup (--deep):
  - All of the above, plus:
  - Worktrees for inactive researchers (researcher-{N})
  - Local branches without worktrees (feature/researcher-{N})
  - Old agent logs (.loom/logs/researcher-*.log)

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
  header "           Research Agent Deep Cleanup"
else
  header "           Research Agent Cleanup"
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

        problem_id=$(basename "$lock_dir" .lock)
        claim_file="$CLAIMS_DIR/${problem_id}.json"

        if is_claim_expired "$claim_file"; then
            ((++stale_claims))
            if [[ "$DRY_RUN" == true ]]; then
                info "Would clean stale claim: $problem_id"
            else
                rm -rf "$lock_dir"
                rm -f "$claim_file"
                success "Cleaned stale claim: $problem_id"
            fi
        else
            ((++active_claims))
            agent_id=$(jq -r '.agent_id' "$claim_file" 2>/dev/null || echo "unknown")
            info "Active claim: $problem_id by $agent_id (preserving)"
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
    for signal_file in "$SIGNALS_DIR"/stop-researcher-*; do
        [[ ! -e "$signal_file" ]] && continue

        signal_name=$(basename "$signal_file")
        ((++signal_count))
        if [[ "$DRY_RUN" == true ]]; then
            info "Would remove signal: $signal_name"
        else
            rm -f "$signal_file"
            success "Removed signal: $signal_name"
        fi
    done
fi

if [[ $signal_count -eq 0 ]]; then
    success "No researcher stop signals found"
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
        # Clean researcher-{N} worktrees.
        #
        # The removal decision is gated by the structural guards 1-5 in
        # `remove_own_worktree` (via `would_remove_own_worktree` for the
        # predicate), NOT by claim-tracker state. Claim state is racy — a
        # concurrently-wiped or TTL-expired claim can make an actively-used
        # worktree look idle — so trusting it alone can force-remove a worktree
        # with a live session or uncommitted work (issue #35256). The guards
        # (dirty tree, unpushed commits, live process, locked, current checkout)
        # are a superset of anything claim correctness could tell us. The claim
        # scan below is retained for diagnostic messaging ONLY.
        for worktree_dir in "$WORKTREES_DIR"/researcher-*; do
            [[ ! -d "$worktree_dir" ]] && continue

            researcher_id=$(basename "$worktree_dir")

            # Diagnostic only: note if a live claim references this researcher.
            claim_note=""
            for claim_file in "$CLAIMS_DIR"/*.json; do
                [[ ! -f "$claim_file" ]] && continue
                agent_id=$(jq -r '.agent_id' "$claim_file" 2>/dev/null || echo "")
                if [[ "$agent_id" == "$researcher_id" ]] && ! is_claim_expired "$claim_file"; then
                    claim_note=" (active claim by $agent_id)"
                    break
                fi
            done

            # Structural guard decision (read-only; matches what a real
            # remove_own_worktree call would do). The predicate returns non-zero
            # for any "preserve" outcome; `|| true` keeps that from tripping the
            # script's `set -e` — the decision is carried by the echoed word.
            decision="$(would_remove_own_worktree "$worktree_dir")" || true

            if [[ "$decision" != "remove" ]]; then
                # A guard preserves this worktree regardless of claim state.
                info "Preserving worktree: $researcher_id (guard: $decision)"
                continue
            fi

            # All guards pass: this worktree is idle, clean, and fully backed up.
            ((++worktree_count))
            if [[ "$DRY_RUN" == true ]]; then
                info "Would remove worktree: $researcher_id${claim_note}"
            elif [[ "$FORCE" == true ]]; then
                remove_own_worktree "$worktree_dir"
                if [[ ! -d "$worktree_dir" ]]; then
                    success "Removed worktree: $researcher_id"
                else
                    warning "Preserved (guard triggered): $researcher_id"
                fi
            else
                echo -e "  ${YELLOW}$researcher_id${NC}${claim_note}"
                read -r -p "  Remove this worktree? [y/N] " -n 1 CONFIRM
                echo ""
                if [[ $CONFIRM =~ ^[Yy]$ ]]; then
                    remove_own_worktree "$worktree_dir"
                    if [[ ! -d "$worktree_dir" ]]; then
                        success "Removed worktree: $researcher_id"
                    else
                        warning "Preserved (guard triggered): $researcher_id"
                    fi
                else
                    info "Skipping: $researcher_id"
                fi
            fi
        done
    fi

    if [[ $worktree_count -eq 0 ]]; then
        success "No stale researcher worktrees found"
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

    # Find feature/researcher-* branches
    branches=$(git branch | grep "feature/researcher-" | sed 's/^[*+ ]*//' || true)

    if [[ -n "$branches" ]]; then
        for branch in $branches; do
            researcher_num=$(echo "$branch" | sed 's/feature\/researcher-//')

            # Check if any worktree uses this branch
            worktree_exists=false
            if [[ -d "$WORKTREES_DIR/researcher-$researcher_num" ]]; then
                worktree_exists=true
            fi

            if [[ "$worktree_exists" == false ]]; then
                ((++branch_count))
                if [[ "$DRY_RUN" == true ]]; then
                    info "Would delete branch: $branch (no worktree)"
                else
                    git branch -D "$branch" 2>/dev/null && \
                        success "Deleted branch: $branch (no worktree)" || \
                        warning "Failed to delete: $branch"
                fi
            else
                info "Preserving branch: $branch (worktree exists)"
            fi
        done
    fi

    if [[ $branch_count -eq 0 ]]; then
        success "No stale researcher branches found"
    fi

    echo ""
    header "Deep Cleaning Logs"
    echo ""

    log_count=0
    log_size="0"

    if [[ -d "$LOGS_DIR" ]]; then
        # Count and measure logs
        for log_file in "$LOGS_DIR"/researcher-*.log "$LOGS_DIR"/researcher-*-prompt.md "$LOGS_DIR"/researcher-*-prompt.txt; do
            [[ ! -f "$log_file" ]] && continue
            ((++log_count))
        done

        if [[ $log_count -gt 0 ]]; then
            log_size=$(du -sh "$LOGS_DIR"/researcher-* 2>/dev/null | tail -1 | cut -f1 || echo "unknown")

            if [[ "$DRY_RUN" == true ]]; then
                info "Would remove $log_count researcher log files ($log_size)"
            elif [[ "$FORCE" == true ]]; then
                rm -f "$LOGS_DIR"/researcher-*.log "$LOGS_DIR"/researcher-*-prompt.md "$LOGS_DIR"/researcher-*-prompt.txt
                success "Removed $log_count researcher log files ($log_size)"
            else
                echo -e "  Found ${YELLOW}$log_count${NC} log files ($log_size)"
                read -r -p "  Remove all researcher logs? [y/N] " -n 1 CONFIRM
                echo ""
                if [[ $CONFIRM =~ ^[Yy]$ ]]; then
                    rm -f "$LOGS_DIR"/researcher-*.log "$LOGS_DIR"/researcher-*-prompt.md "$LOGS_DIR"/researcher-*-prompt.txt
                    success "Removed $log_count researcher log files"
                else
                    info "Skipping log cleanup"
                fi
            fi
        else
            success "No researcher logs found"
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
    info "To actually clean, run: ./scripts/research/clean-research.sh"
    if [[ "$DEEP_CLEAN" == true ]]; then
        echo "                        ./scripts/research/clean-research.sh --deep"
    fi
else
    success "Research agent cleanup complete!"
fi

echo ""
