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

        # Find worktree by checking which one has this branch
        local worktree_path=""
        while IFS= read -r line; do
            local wt_path=$(echo "$line" | cut -d' ' -f1)
            local wt_branch=$(echo "$line" | grep -o '\[.*\]' | tr -d '[]')
            if [[ "$wt_branch" == "$branch" ]]; then
                worktree_path="$wt_path"
                break
            fi
        done < <(git worktree list)

        # If no worktree found, create a temporary one
        local temp_worktree=false
        if [[ -z "$worktree_path" ]]; then
            worktree_path="$REPO_ROOT/.loom/worktrees/temp-rebase-$$"
            print_info "Creating temporary worktree for rebase..."
            git fetch origin "$branch"
            git worktree add "$worktree_path" "origin/$branch" --detach 2>/dev/null || {
                print_warning "Could not create worktree for #$pr"
                ((failed++))
                continue
            }
            (cd "$worktree_path" && git checkout -B "$branch" "origin/$branch")
            temp_worktree=true
        fi

        (
            cd "$worktree_path"
            git stash 2>/dev/null || true
            git fetch origin main
            git fetch origin "$branch"
            git reset --hard "origin/$branch" 2>/dev/null || true

            if git rebase origin/main 2>/dev/null; then
                # Rebase succeeded cleanly
                git push --force-with-lease origin "$branch" 2>/dev/null || true
            else
                # Handle conflicts intelligently
                resolve_conflicts() {
                    local resolved=true
                    for conflict_file in $(git diff --name-only --diff-filter=U); do
                        case "$conflict_file" in
                            research/candidate-pool.json)
                                # JSON-aware merge: union candidates by id
                                print_info "  Merging candidate-pool.json with JSON-aware union..."
                                # Extract ours and theirs versions
                                git show :2:"$conflict_file" > /tmp/pool-ours.json 2>/dev/null || true
                                git show :3:"$conflict_file" > /tmp/pool-theirs.json 2>/dev/null || true
                                if [[ -s /tmp/pool-ours.json && -s /tmp/pool-theirs.json ]]; then
                                    node -e "
const fs = require('fs');
const ours = JSON.parse(fs.readFileSync('/tmp/pool-ours.json', 'utf8'));
const theirs = JSON.parse(fs.readFileSync('/tmp/pool-theirs.json', 'utf8'));
const merged = {};
[...(ours.candidates || []), ...(theirs.candidates || [])].forEach(c => {
    if (!merged[c.id] || (merged[c.id].attemptCount || 0) < (c.attemptCount || 0)) {
        merged[c.id] = c;
    }
});
ours.candidates = Object.values(merged).sort((a, b) => a.id.localeCompare(b.id));
ours.last_updated = new Date().toISOString();
fs.writeFileSync('$conflict_file', JSON.stringify(ours, null, 2) + '\n');
" && git add "$conflict_file"
                                else
                                    # Fallback: take ours
                                    git checkout --ours "$conflict_file" 2>/dev/null && git add "$conflict_file"
                                fi
                                rm -f /tmp/pool-ours.json /tmp/pool-theirs.json
                                ;;
                            src/data/proofs/listings.json|src/data/research/research-listings.json)
                                # These derived files should no longer be in PRs (gitignored).
                                # If somehow present in an old PR, remove from index - they are regenerated by pnpm build.
                                git rm --cached "$conflict_file" 2>/dev/null || git checkout --ours "$conflict_file" 2>/dev/null
                                git add "$conflict_file" 2>/dev/null || true
                                ;;
                            research/stub-claims/completed.json)
                                # For stub-claims, take ours (main wins)
                                git checkout --ours "$conflict_file" 2>/dev/null && git add "$conflict_file"
                                ;;
                            *.lean)
                                # Lean files need careful handling - don't auto-resolve
                                print_warning "  Lean file conflict: $conflict_file (needs manual review)"
                                resolved=false
                                ;;
                            *)
                                # Other files - try ours first
                                git checkout --ours "$conflict_file" 2>/dev/null && git add "$conflict_file" || resolved=false
                                ;;
                        esac
                    done
                    $resolved
                }

                if resolve_conflicts; then
                    # Check for nested conflict markers (bad previous merge)
                    if grep -rq "^<<<<<<<.*\n.*^<<<<<<" . 2>/dev/null; then
                        print_warning "  Nested conflict markers detected, aborting"
                        git rebase --abort 2>/dev/null || true
                    else
                        GIT_EDITOR=true git rebase --continue 2>/dev/null || {
                            # If continue fails, try once more after resolving any new conflicts
                            resolve_conflicts && GIT_EDITOR=true git rebase --continue 2>/dev/null || git rebase --abort 2>/dev/null || true
                        }
                        git push --force-with-lease origin "$branch" 2>/dev/null || true
                    fi
                else
                    print_warning "  Could not auto-resolve all conflicts"
                    git rebase --abort 2>/dev/null || true
                fi
            fi
        )

        # Clean up temporary worktree
        if $temp_worktree; then
            git worktree remove "$worktree_path" --force 2>/dev/null || true
        fi

        # Try merging again after rebase
        sleep 3
        local new_status=$(gh pr view "$pr" --json mergeable --jq '.mergeable' 2>/dev/null || echo "UNKNOWN")
        echo -n "  #$pr (after rebase): "
        if [[ "$new_status" == "MERGEABLE" ]] && gh pr merge "$pr" --squash 2>/dev/null; then
            echo "merged"
            ((merged++))
        else
            echo "still conflicting ($new_status)"
            ((failed++))
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
# Quality Trend Analysis
# ============================================================================

# Compare current quality audit snapshot to the previous one and log trends.
# Non-blocking: deploy always succeeds regardless of regression.
compare_quality_trends() {
    local audit_dir="$1"
    local current_file="$2"

    # Find previous snapshot (second most recent file)
    local prev_file
    prev_file=$(ls -t "$audit_dir"/*.json 2>/dev/null | sed -n '2p')

    if [[ -z "$prev_file" ]]; then
        print_info "Quality trend: No previous audit for comparison (first run)"
        return 0
    fi

    # Extract total counts
    local prev_total curr_total
    prev_total=$(jq '.summary.totalIssues' "$prev_file" 2>/dev/null) || prev_total=""
    curr_total=$(jq '.summary.totalIssues' "$current_file" 2>/dev/null) || curr_total=""

    # Bail out if either value is not a valid number
    if ! [[ "$prev_total" =~ ^[0-9]+$ ]] || ! [[ "$curr_total" =~ ^[0-9]+$ ]]; then
        print_warning "Quality trend: Could not parse audit snapshots for comparison"
        return 0
    fi

    local delta=$((curr_total - prev_total))

    if [[ $delta -eq 0 ]]; then
        print_info "Quality trend: Stable at $curr_total issues"
    elif [[ $delta -gt 0 ]]; then
        print_warning "Quality regression: $prev_total → $curr_total (+$delta issues)"
    else
        # delta is negative, use absolute value for display
        local abs_delta=$(( -delta ))
        print_success "Quality improvement: $prev_total → $curr_total (-$abs_delta issues)"
    fi

    # Per-type breakdown: show changes for each issue type
    local prev_types curr_types
    prev_types=$(jq -r '.summary.issuesByType // {}' "$prev_file" 2>/dev/null) || prev_types="{}"
    curr_types=$(jq -r '.summary.issuesByType // {}' "$current_file" 2>/dev/null) || curr_types="{}"

    if [[ "$prev_types" != "{}" ]] && [[ "$curr_types" != "{}" ]]; then
        local type_changes
        type_changes=$(jq -n \
            --argjson prev "$prev_types" \
            --argjson curr "$curr_types" \
            '[$curr | to_entries[] | {key, prev: ($prev[.key] // 0), curr: .value} | select(.curr - .prev | . > 0 or . < 0)] |
             sort_by(-.curr + .prev) |
             .[] | "  \(.key): \(.prev) -> \(.curr) (\(if .curr > .prev then "+\(.curr - .prev)" else "\(.curr - .prev)" end))"' 2>/dev/null)

        if [[ -n "$type_changes" ]]; then
            print_info "Issue type changes:"
            echo "$type_changes"
        fi
    fi

    return 0
}

# Prune old quality history snapshots, keeping the most recent N files.
prune_quality_history() {
    local audit_dir="$1"
    local keep_count="${QUALITY_HISTORY_KEEP:-30}"

    local file_count
    file_count=$(ls -1 "$audit_dir"/*.json 2>/dev/null | wc -l | tr -d ' ')

    if [[ "$file_count" -gt "$keep_count" ]]; then
        local to_delete=$((file_count - keep_count))
        print_info "Pruning $to_delete old quality snapshot(s) (keeping last $keep_count)..."
        ls -t "$audit_dir"/*.json | tail -n "$to_delete" | xargs rm -f
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

    # Run quality audit and log results
    print_info "Running quality audit..."
    local audit_dir="$REPO_ROOT/research/quality-history"
    mkdir -p "$audit_dir"
    local audit_file="$audit_dir/$(date -u +%Y%m%d-%H%M%S).json"
    if npx tsx "$REPO_ROOT/scripts/erdos/quality-audit.ts" --json > "$audit_file" 2>/dev/null; then
        local total_issues
        total_issues=$(jq '.summary.totalIssues' "$audit_file" 2>/dev/null || echo "?")
        print_info "Quality audit: $total_issues issues logged to $audit_file"

        # Compare to previous snapshot for trend analysis
        compare_quality_trends "$audit_dir" "$audit_file"

        # Prune old snapshots to prevent unbounded growth
        prune_quality_history "$audit_dir"
    else
        print_warning "Quality audit failed (non-blocking)"
        rm -f "$audit_file"
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

    # Note: research-listings.json is gitignored (derived artifact, regenerated by pnpm build)
    # Only commit candidate-pool.json which is runtime state
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
