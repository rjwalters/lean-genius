#!/bin/bash
#
# sync-and-deploy.sh - Merge PRs, sync data, build, and deploy the website
#
# Usage:
#   ./sync-and-deploy.sh              Run full pipeline
#   ./sync-and-deploy.sh --merge      Only merge PRs
#   ./sync-and-deploy.sh --sync       Only sync data files
#   ./sync-and-deploy.sh --build      Only build
#   ./sync-and-deploy.sh --deploy     Only deploy (assumes already built)
#   ./sync-and-deploy.sh --dry-run    Show what would be done
#
# Environment:
#   SKIP_MERGE=1    Skip PR merging
#   SKIP_SYNC=1     Skip data syncing
#   SKIP_BUILD=1    Skip building
#   SKIP_DEPLOY=1   Skip deployment

set -euo pipefail

# Find repo root
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
cd "$REPO_ROOT"

# Colors
RED='\033[0;31m'
GREEN='\033[0;32m'
BLUE='\033[0;34m'
YELLOW='\033[1;33m'
NC='\033[0m'

print_error() { echo -e "${RED}✗ $1${NC}"; }
print_success() { echo -e "${GREEN}✓ $1${NC}"; }
print_info() { echo -e "${BLUE}ℹ $1${NC}"; }
print_warning() { echo -e "${YELLOW}⚠ $1${NC}"; }
print_header() { echo -e "\n${BLUE}=== $1 ===${NC}"; }

DRY_RUN=false
ONLY_MERGE=false
ONLY_SYNC=false
ONLY_BUILD=false
ONLY_DEPLOY=false

# Parse arguments
while [[ $# -gt 0 ]]; do
    case $1 in
        --dry-run) DRY_RUN=true; shift ;;
        --merge) ONLY_MERGE=true; shift ;;
        --sync) ONLY_SYNC=true; shift ;;
        --build) ONLY_BUILD=true; shift ;;
        --deploy) ONLY_DEPLOY=true; shift ;;
        --help|-h)
            echo "Usage: $0 [OPTIONS]"
            echo ""
            echo "Options:"
            echo "  --merge      Only merge PRs"
            echo "  --sync       Only sync data files"
            echo "  --build      Only build website"
            echo "  --deploy     Only deploy (assumes built)"
            echo "  --dry-run    Show what would be done"
            echo "  --help       Show this help"
            exit 0
            ;;
        *) print_error "Unknown option: $1"; exit 1 ;;
    esac
done

# Determine what to run
run_merge=true
run_sync=true
run_build=true
run_deploy=true

if $ONLY_MERGE; then run_sync=false; run_build=false; run_deploy=false; fi
if $ONLY_SYNC; then run_merge=false; run_build=false; run_deploy=false; fi
if $ONLY_BUILD; then run_merge=false; run_sync=false; run_deploy=false; fi
if $ONLY_DEPLOY; then run_merge=false; run_sync=false; run_build=false; fi

[[ "${SKIP_MERGE:-}" == "1" ]] && run_merge=false
[[ "${SKIP_SYNC:-}" == "1" ]] && run_sync=false
[[ "${SKIP_BUILD:-}" == "1" ]] && run_build=false
[[ "${SKIP_DEPLOY:-}" == "1" ]] && run_deploy=false

# ============================================================================
# Step 1: Merge PRs
# ============================================================================
merge_prs() {
    print_header "Merging Pull Requests"

    # Update main first
    print_info "Updating main branch..."
    git fetch origin main
    git checkout main 2>/dev/null || true
    git stash 2>/dev/null || true
    git reset --hard origin/main

    local merged=0
    local failed=0
    local total=$(gh pr list --json number | jq 'length')

    print_info "Found $total open PRs"

    if [[ $total -eq 0 ]]; then
        print_success "No PRs to merge"
        return 0
    fi

    # Try to merge each PR
    for pr in $(gh pr list --limit 100 --json number,mergeable --jq '.[] | select(.mergeable == "MERGEABLE") | .number'); do
        if $DRY_RUN; then
            echo "  Would merge PR #$pr"
            ((merged++))
        else
            echo -n "  #$pr: "
            if gh pr merge "$pr" --squash 2>/dev/null; then
                echo "merged"
                ((merged++))
            else
                echo "failed"
                ((failed++))
            fi
        fi
    done

    # Handle UNKNOWN status PRs (wait and retry)
    sleep 3
    for pr in $(gh pr list --limit 100 --json number,mergeable --jq '.[] | select(.mergeable == "UNKNOWN") | .number'); do
        local status=$(gh pr view "$pr" --json mergeable --jq '.mergeable' 2>/dev/null || echo "UNKNOWN")
        if [[ "$status" == "MERGEABLE" ]]; then
            if $DRY_RUN; then
                echo "  Would merge PR #$pr (after status refresh)"
                ((merged++))
            else
                echo -n "  #$pr: "
                if gh pr merge "$pr" --squash 2>/dev/null; then
                    echo "merged"
                    ((merged++))
                else
                    echo "skipped"
                fi
            fi
        fi
    done

    # Try to rebase conflicting PRs
    for pr in $(gh pr list --limit 50 --json number,mergeable --jq '.[] | select(.mergeable == "CONFLICTING") | .number'); do
        local branch=$(gh pr view "$pr" --json headRefName --jq '.headRefName')
        print_info "Attempting rebase for PR #$pr ($branch)..."

        if $DRY_RUN; then
            echo "  Would attempt rebase for PR #$pr"
            continue
        fi

        # Find worktree for this branch
        local worktree_name=$(echo "$branch" | sed 's/feature\///' | sed 's/-enhance//')
        local worktree_path="$REPO_ROOT/.loom/worktrees/$worktree_name"

        if [[ -d "$worktree_path" ]]; then
            (
                cd "$worktree_path"
                git stash 2>/dev/null || true
                git fetch origin main
                if git rebase origin/main 2>/dev/null; then
                    # Rebase succeeded
                    git push --force-with-lease origin "$branch" 2>/dev/null || true
                else
                    # Try accepting theirs for common conflict files
                    git checkout --theirs research/candidate-pool.json 2>/dev/null || true
                    git checkout --theirs src/data/proofs/listings.json 2>/dev/null || true
                    git checkout --theirs research/stub-claims/completed.json 2>/dev/null || true
                    git checkout --theirs src/data/research/research-listings.json 2>/dev/null || true
                    git add -A
                    GIT_EDITOR=true git rebase --continue 2>/dev/null || git rebase --abort 2>/dev/null || true
                    git push --force-with-lease origin "$branch" 2>/dev/null || true
                fi
            )

            # Try merging again after rebase
            sleep 2
            echo -n "  #$pr (after rebase): "
            if gh pr merge "$pr" --squash 2>/dev/null; then
                echo "merged"
                ((merged++))
            else
                echo "still conflicting"
                ((failed++))
            fi
        fi
    done

    print_success "Merged $merged PRs ($failed failed/skipped)"

    # Update main again after merges
    git fetch origin main
    git reset --hard origin/main
}

# ============================================================================
# Step 2: Sync Data Files
# ============================================================================
sync_data() {
    print_header "Syncing Data Files"

    if $DRY_RUN; then
        echo "  Would sync research-listings.json"
        echo "  Would sync stub completion stats"
        return 0
    fi

    # Sync research listings
    print_info "Syncing research-listings.json..."
    python3 << 'PYTHON'
import json
from pathlib import Path
from datetime import datetime

listings_file = Path("src/data/research/research-listings.json")
problems_dir = Path("src/data/research/problems")
pool_file = Path("research/candidate-pool.json")

if not listings_file.exists():
    print("  No research-listings.json found")
    exit(0)

with open(listings_file) as f:
    listings = json.load(f)

# Load pool for status
pool_status = {}
if pool_file.exists():
    with open(pool_file) as f:
        pool = json.load(f)
    pool_status = {c["id"]: c.get("status", "pending") for c in pool["candidates"]}

listing_slugs = {item["slug"] for item in listings}
added = 0
updated = 0

# Process each problem file
for problem_file in problems_dir.glob("*.json"):
    slug = problem_file.stem

    with open(problem_file) as f:
        problem = json.load(f)

    knowledge = problem.get("knowledge", {})
    insights = len(knowledge.get("insights", []))
    built = len(knowledge.get("builtItems", []))

    if insights == 0 and built == 0:
        continue

    attempt_count = max(1, (insights + built) // 3)

    if slug not in listing_slugs:
        # Add new entry
        status = pool_status.get(slug, "pending")
        phase = "ACT" if status == "completed" else "SURVEY"
        list_status = "complete" if status == "completed" else "active"

        title = problem.get("title", problem.get("name", slug))
        description = problem.get("statement", problem.get("description", ""))[:200]

        new_entry = {
            "slug": slug,
            "title": title,
            "description": description,
            "phase": phase,
            "status": list_status,
            "tier": "B",
            "path": "full",
            "tags": problem.get("tags", ["research"]),
            "started": datetime.now().isoformat(),
            "lastUpdate": datetime.now().isoformat(),
            "attemptCount": attempt_count,
            "approachCount": 0,
            "significance": 5,
            "tractability": 5
        }
        listings.append(new_entry)
        added += 1
    else:
        # Update existing entry
        idx = next(i for i, item in enumerate(listings) if item["slug"] == slug)
        if attempt_count > listings[idx].get("attemptCount", 0):
            listings[idx]["attemptCount"] = attempt_count
            listings[idx]["lastUpdate"] = datetime.now().isoformat()
            updated += 1

with open(listings_file, "w") as f:
    json.dump(listings, f, indent=2)

total_attempts = sum(item.get("attemptCount", 0) for item in listings)
print(f"  Added {added}, updated {updated} listings")
print(f"  Total iterations: {total_attempts}")
PYTHON

    # Check for changes
    if git diff --quiet src/data/research/research-listings.json 2>/dev/null; then
        print_info "No changes to research-listings.json"
    else
        print_success "Updated research-listings.json"
    fi
}

# ============================================================================
# Step 3: Build
# ============================================================================
build_website() {
    print_header "Building Website"

    if $DRY_RUN; then
        echo "  Would run: pnpm build"
        return 0
    fi

    print_info "Running pnpm build..."
    if pnpm build 2>&1 | tail -5; then
        print_success "Build completed"
    else
        print_error "Build failed"
        return 1
    fi
}

# ============================================================================
# Step 4: Deploy
# ============================================================================
deploy_website() {
    print_header "Deploying to Cloudflare"

    if $DRY_RUN; then
        echo "  Would run: pnpm run deploy"
        return 0
    fi

    print_info "Running pnpm run deploy..."
    if pnpm run deploy 2>&1 | tail -10; then
        print_success "Deployment completed"
    else
        print_error "Deployment failed"
        return 1
    fi
}

# ============================================================================
# Step 5: Commit Sync Changes
# ============================================================================
commit_changes() {
    print_header "Committing Sync Changes"

    if $DRY_RUN; then
        echo "  Would commit any data sync changes"
        return 0
    fi

    # Check for changes
    if git diff --quiet && git diff --staged --quiet; then
        print_info "No changes to commit"
        return 0
    fi

    git add src/data/research/research-listings.json 2>/dev/null || true
    git add research/candidate-pool.json 2>/dev/null || true

    if ! git diff --staged --quiet; then
        git commit -m "$(cat <<'EOF'
chore: sync research listings and data

Automated sync of research iteration counts and problem listings.

Co-Authored-By: Claude <noreply@anthropic.com>
EOF
)"
        git push origin main
        print_success "Changes committed and pushed"
    else
        print_info "No staged changes to commit"
    fi
}

# ============================================================================
# Main
# ============================================================================
main() {
    print_header "Deploy Pipeline"
    echo "  Merge PRs: $run_merge"
    echo "  Sync Data: $run_sync"
    echo "  Build:     $run_build"
    echo "  Deploy:    $run_deploy"
    echo "  Dry Run:   $DRY_RUN"

    $run_merge && merge_prs
    $run_sync && sync_data
    $run_build && build_website
    $run_deploy && deploy_website
    $run_sync && commit_changes

    print_header "Complete"
    print_success "Deploy pipeline finished"
}

main
