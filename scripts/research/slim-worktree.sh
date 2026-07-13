#!/bin/bash
#
# slim-worktree.sh - slim a git worktree for disk space the SAFE way
#
# NEVER delete tracked files from disk to reclaim space. Git sees raw disk
# deletions as pending changes, and a later stage-all commit (`git add -A`)
# will faithfully stage them as deletions — this is exactly how commit
# dc9fdffa30 (2026-07-11, issue #38398) mass-deleted 9,927 files from main.
#
# This helper uses `git sparse-checkout` in cone mode instead: files outside
# the kept directories are removed from DISK but marked skip-worktree in the
# index, so git does NOT see them as deleted and no commit can stage their
# deletion.
#
# Usage:
#   slim-worktree.sh [--worktree PATH] DIR [DIR ...]   Keep only DIRs (+ root files)
#   slim-worktree.sh [--worktree PATH] --restore       Undo: restore the full checkout
#   slim-worktree.sh [--worktree PATH] --status        Show sparse-checkout state
#
# Examples:
#   # Slim a researcher worktree down to the Lean project + one problem dir:
#   scripts/research/slim-worktree.sh --worktree .loom/worktrees/researcher-3 \
#       proofs research/problems/erdos-771
#
#   # Undo (from inside the worktree):
#   scripts/research/slim-worktree.sh --restore

set -euo pipefail

RED='\033[0;31m'
GREEN='\033[0;32m'
BLUE='\033[0;34m'
YELLOW='\033[1;33m'
NC='\033[0m'

print_error() { echo -e "${RED}✗ $1${NC}"; }
print_success() { echo -e "${GREEN}✓ $1${NC}"; }
print_info() { echo -e "${BLUE}ℹ $1${NC}"; }
print_warning() { echo -e "${YELLOW}⚠ $1${NC}"; }

WORKTREE="$PWD"
ACTION="set"
DIRS=()

while [[ $# -gt 0 ]]; do
    case "$1" in
        --worktree)
            if [[ -z "${2:-}" ]]; then
                print_error "--worktree requires a path"
                exit 2
            fi
            WORKTREE="$2"
            shift 2
            ;;
        --restore)
            ACTION="restore"
            shift
            ;;
        --status)
            ACTION="status"
            shift
            ;;
        --help|-h)
            sed -n '2,26p' "$0" | sed 's/^# \{0,1\}//'
            exit 0
            ;;
        -*)
            print_error "Unknown option: $1 (see --help)"
            exit 2
            ;;
        *)
            DIRS+=("$1")
            shift
            ;;
    esac
done

if ! git -C "$WORKTREE" rev-parse --git-dir >/dev/null 2>&1; then
    print_error "Not a git worktree: $WORKTREE"
    exit 2
fi

case "$ACTION" in
    status)
        if [[ "$(git -C "$WORKTREE" config --get core.sparseCheckout 2>/dev/null || echo false)" == "true" ]]; then
            print_info "sparse-checkout is ENABLED in $WORKTREE; kept directories:"
            git -C "$WORKTREE" sparse-checkout list | sed 's/^/    /'
        else
            print_info "sparse-checkout is DISABLED in $WORKTREE (full checkout)"
        fi
        ;;
    restore)
        print_info "Restoring full checkout in $WORKTREE..."
        git -C "$WORKTREE" sparse-checkout disable
        print_success "Full checkout restored"
        ;;
    set)
        if [[ ${#DIRS[@]} -eq 0 ]]; then
            print_error "No directories given. Usage: slim-worktree.sh [--worktree PATH] DIR [DIR ...]"
            print_error "(or --restore / --status; see --help)"
            exit 2
        fi

        # Warn about pre-existing deletions: sparse-checkout cannot repair a
        # worktree that ALREADY has raw disk deletions pending — those must be
        # restored first or they remain stageable.
        pre_missing=$(git -C "$WORKTREE" status --porcelain 2>/dev/null | grep -c '^ D\|^D ' || true)
        if [[ "${pre_missing:-0}" -gt 0 ]]; then
            print_warning "$pre_missing tracked file(s) already deleted on disk in $WORKTREE."
            print_warning "Restore them BEFORE slimming: git -C $WORKTREE checkout -- ."
        fi

        print_info "Slimming $WORKTREE to: ${DIRS[*]} (cone mode)..."
        git -C "$WORKTREE" sparse-checkout set --cone "${DIRS[@]}"

        # Prove safety: sparse-checkout must not have introduced any
        # git-visible deletions (skip-worktree bits protect slimmed paths).
        post_missing=$(git -C "$WORKTREE" status --porcelain 2>/dev/null | grep -c '^ D\|^D ' || true)
        if [[ "${post_missing:-0}" -gt "${pre_missing:-0}" ]]; then
            print_error "sparse-checkout left $post_missing pending deletion(s) — investigate before committing!"
            exit 1
        fi
        print_success "Slimmed safely: git sees ${post_missing:-0} pending deletion(s) (skip-worktree protects the rest)"
        print_info "Undo anytime with: $0 --worktree $WORKTREE --restore"
        ;;
esac
