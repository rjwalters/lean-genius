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
cd "$REPO_ROOT"

# Pin gh to the correct repo — this repo has a mathlib-fork remote that gh
# defaults to over origin, causing all pr commands to target the wrong repo.
export GH_REPO="rjwalters/lean-genius"

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
# Step 0: Label unlabeled erdos/research PRs
# ============================================================================
label_unlabeled_prs() {
    print_header "Labeling Unlabeled Erdos/Research PRs"

    # Find open PRs with erdos-enhancement, research, or aristotle-integration labels
    # that have no loom: labels at all (safety net for old worktrees or gh errors)
    local labeled=0
    for pr in $(gh pr list --state open --limit 100 --json number,labels \
        --jq '.[] |
            select(.labels | map(.name) | any(. == "erdos-enhancement" or . == "research" or . == "aristotle-integration")) |
            select(.labels | map(.name) | any(startswith("loom:")) | not) |
            .number'); do
        if $DRY_RUN; then
            echo "  Would label PR #$pr with loom:review-requested"
        else
            echo -n "  #$pr: "
            if gh pr edit "$pr" --add-label "loom:review-requested" 2>/dev/null; then
                echo "labeled"
            else
                echo "failed to label"
            fi
        fi
        ((labeled++)) || true
    done

    if [[ $labeled -eq 0 ]]; then
        print_info "No unlabeled erdos/research PRs found"
    else
        print_success "Labeled $labeled PR(s) with loom:review-requested"
    fi
}

# ============================================================================
# Step 1: Merge PRs
# ============================================================================
merge_prs() {
    print_header "Merging Pull Requests"

    # Update main first
    print_info "Updating main branch..."
    git fetch origin main
    # Stash before checkout — dirty files block branch switch
    git stash 2>/dev/null || true
    git checkout main 2>/dev/null || git checkout -b main origin/main 2>/dev/null || true
    git reset --hard origin/main

    local merged=0
    local failed=0

    # Skip PRs with loom:review-requested — those are opted into Loom Judge review
    local jq_filter='[.[] | select(.labels | map(.name) | any(. == "loom:review-requested") | not)]'
    local all_prs=$(gh pr list --limit 100 --json number,mergeable,labels)
    local eligible_prs=$(echo "$all_prs" | jq "$jq_filter")
    local total=$(echo "$eligible_prs" | jq 'length')
    local skipped=$(echo "$all_prs" | jq "length - ($total)")

    print_info "Found $total eligible PRs ($skipped skipped — loom:review-requested)"

    if [[ $total -eq 0 ]]; then
        print_success "No PRs to merge"
        return 0
    fi

    # Try to merge each PR
    for pr in $(echo "$eligible_prs" | jq -r '.[] | select(.mergeable == "MERGEABLE") | .number'); do
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
    for pr in $(echo "$eligible_prs" | jq -r '.[] | select(.mergeable == "UNKNOWN") | .number'); do
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
    for pr in $(echo "$eligible_prs" | jq -r '.[] | select(.mergeable == "CONFLICTING") | .number'); do
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
            # --no-track: don't write upstream-tracking config to .git/config,
            # which is shared across all worktrees and serialized via a single
            # lockfile. With ~60 worktrees doing concurrent rebases this lock
            # is the dominant failure mode ("could not lock config file").
            (cd "$worktree_path" && git checkout --no-track -B "$branch" "origin/$branch")
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
                git -c push.autoSetupRemote=false push --force-with-lease origin "$branch" 2>/dev/null || true
            else
                # Handle conflicts intelligently
                resolve_conflicts() {
                    local resolved=true
                    for conflict_file in $(git diff --name-only --diff-filter=U); do
                        case "$conflict_file" in
                            .lean/state/candidate-pool.json)
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
                            .lean/state/stub-claims/completed.json)
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
                        git -c push.autoSetupRemote=false push --force-with-lease origin "$branch" 2>/dev/null || true
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
pool_file = Path(".lean/state/candidate-pool.json")

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

# Remove entries missing required 'slug' field
listings = [item for item in listings if "slug" in item]
listing_slugs = {item["slug"] for item in listings}
added = 0
updated = 0

# Process each problem file
for problem_file in problems_dir.glob("*.json"):
    slug = problem_file.stem

    try:
        with open(problem_file) as f:
            problem = json.load(f)
    except (json.JSONDecodeError, ValueError):
        print(f"  WARN: skipping invalid JSON: {problem_file.name}")
        continue

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
    # Capture full log so failures aren't masked by `| tail -5` (which forces
    # the pipe's exit status to tail's, always 0). Cap node heap at 8 GB so
    # OOMs surface as deterministic exits rather than thrashing the host, and
    # bound the whole chain at 20 minutes so a hung step can't accumulate
    # zombie pnpm/vite processes across cycles.
    local build_log
    build_log=$(mktemp)
    local build_status=0
    NODE_OPTIONS="${NODE_OPTIONS:-} --max-old-space-size=8192" \
        timeout --kill-after=30 20m pnpm build > "$build_log" 2>&1 \
        || build_status=$?
    tail -20 "$build_log"
    case $build_status in
        0)
            print_success "Build completed"
            rm -f "$build_log"
            ;;
        124|137)
            print_error "Build timed out after 20m (status $build_status); see full log at $build_log"
            return 1
            ;;
        *)
            print_error "Build failed (exit $build_status); see full log at $build_log"
            return 1
            ;;
    esac

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

# Prune old Cloudflare Pages deployments, keeping only the latest DEPLOY_KEEP (default 10).
# Runs after each successful deploy to prevent unbounded deployment accumulation.
prune_old_deployments() {
    local keep="${DEPLOY_KEEP:-10}"
    local project="lean-genius"

    if [[ -z "${CLOUDFLARE_API_TOKEN:-}" || -z "${CLOUDFLARE_ACCOUNT_ID:-}" ]]; then
        print_warning "Skipping deployment pruning (no API token)"
        return 0
    fi

    local api="https://api.cloudflare.com/client/v4/accounts/${CLOUDFLARE_ACCOUNT_ID}/pages/projects/${project}/deployments"
    local total
    total=$(curl -sf -H "Authorization: Bearer $CLOUDFLARE_API_TOKEN" "${api}?per_page=1" | jq '.result_info.total_count // 0')

    if [[ "$total" -le "$keep" ]]; then
        print_info "Deployments: $total (within limit of $keep)"
        return 0
    fi

    print_info "Pruning deployments: $total total, keeping latest $keep..."
    local pruned=0

    # Fetch page 1 (newest first), delete everything after the first $keep entries.
    # Repeat until nothing left to delete (deletions shift items forward).
    while true; do
        local ids
        ids=$(curl -sf -H "Authorization: Bearer $CLOUDFLARE_API_TOKEN" \
            "${api}?per_page=25&page=1" | jq -r ".result[$keep:][].id // empty" 2>/dev/null)

        [[ -z "$ids" ]] && break

        for id in $ids; do
            curl -sf -X DELETE -H "Authorization: Bearer $CLOUDFLARE_API_TOKEN" \
                "${api}/${id}?force=true" > /dev/null 2>&1 && ((pruned++)) || true
        done
    done

    print_success "Pruned $pruned old deployment(s)"
}

deploy_website() {
    print_header "Deploying to Cloudflare"

    # Load .env to get CLOUDFLARE_ACCOUNT_ID and CLOUDFLARE_API_TOKEN
    # These override wrangler's OAuth login, ensuring deploys always go
    # to the correct account regardless of who is logged in.
    if [[ -f "$REPO_ROOT/.env" ]]; then
        set -a
        source "$REPO_ROOT/.env"
        set +a
    fi

    # Verify we have the account pinned
    if [[ -z "${CLOUDFLARE_ACCOUNT_ID:-}" ]]; then
        print_error "CLOUDFLARE_ACCOUNT_ID not set. Add it to .env to prevent wrong-account deploys."
        print_info "Expected: 251e6e8626d921603fdc3f0d75576bc6 (Personal Account)"
        return 1
    fi

    if $DRY_RUN; then
        echo "  Would run: wrangler pages deploy dist (with ASCII-safe commit message)"
        echo "  Account: $CLOUDFLARE_ACCOUNT_ID"
        return 0
    fi

    # Use ASCII-safe commit message to avoid Cloudflare API rejecting Unicode math symbols
    local commit_hash
    commit_hash=$(git rev-parse --short HEAD 2>/dev/null || echo "unknown")
    local safe_commit_msg
    safe_commit_msg=$(git log -1 --format="%s" 2>/dev/null | LC_ALL=C tr -cd '[:print:]' | cut -c1-100 || echo "deploy $commit_hash")

    print_info "Running wrangler pages deploy (commit: $commit_hash)..."
    # UV_THREADPOOL_SIZE=32 prevents DNS resolution failures (ENOTFOUND) during
    # parallel bulk uploads on macOS with Node 25 + wrangler 4.x
    if UV_THREADPOOL_SIZE=32 wrangler pages deploy dist --project-name=lean-genius --branch=main --commit-dirty=true --commit-hash="$commit_hash" --commit-message="$safe_commit_msg" 2>&1 | tail -10; then
        print_success "Deployment completed"

        # Prune old deployments, keeping only the latest N
        prune_old_deployments

        # Create completion signal for daemon stats tracking
        local completions_dir="$REPO_ROOT/.loom/signals/completions"
        mkdir -p "$completions_dir"
        touch "$completions_dir/deployment-$(date +%s)"
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

    # Commit state files that change during sync (registry graduations, pool status)
    git add .lean/state/candidate-pool.json 2>/dev/null || true
    git add research/registry.json 2>/dev/null || true

    if ! git diff --staged --quiet; then
        # Branch protection blocks direct pushes to main — use a PR
        local sync_branch="chore/sync-data-$(date +%Y%m%d-%H%M%S)"
        git checkout -b "$sync_branch" 2>/dev/null
        git commit -m "$(cat <<'EOF'
chore: sync research listings and data

Automated sync of research iteration counts and problem listings.

Co-Authored-By: Claude <noreply@anthropic.com>
EOF
)"
        if git push -u origin "$sync_branch" 2>/dev/null; then
            if gh pr create --title "chore: sync research data" --body "Automated data sync." 2>/dev/null; then
                local pr_number
                pr_number=$(gh pr list --head "$sync_branch" --json number --jq '.[0].number' 2>/dev/null)
                if [[ -n "$pr_number" ]]; then
                    sleep 2
                    gh pr merge "$pr_number" --squash 2>/dev/null && print_success "Sync PR #$pr_number merged" || print_warning "Sync PR #$pr_number created but not yet mergeable"
                fi
            fi
        else
            print_warning "Could not push sync branch"
        fi
        # Return to main
        git checkout main 2>/dev/null || true
        git reset --hard origin/main 2>/dev/null || true
        git branch -D "$sync_branch" 2>/dev/null || true
    else
        print_info "No staged changes to commit"
    fi

    # Clean up build artifacts left in working tree (regenerated by pnpm build).
    # Files like src/data/research/problems/*.json and research-listings.json are
    # derived from registry + markdown sources and must not stay dirty on main.
    if ! git diff --quiet 2>/dev/null; then
        print_info "Cleaning up build artifacts from working tree..."
        git checkout -- .
        print_success "Working tree cleaned"
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
