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
#   SKIP_MERGE=1            Skip PR merging
#   SKIP_SYNC=1             Skip data syncing
#   SKIP_BUILD=1            Skip building
#   SKIP_DEPLOY=1           Skip deployment
#   SKIP_SYNC_BRANCH=1      Skip per-cycle fast-forward sync of the current
#                           branch to origin/main. By default the pipeline
#                           fetches origin/main and fast-forwards the current
#                           branch before the merge phase so the deployer's
#                           long-lived worktree (feature/deployer) does not
#                           drift behind main across daemon cycles (see #21042).
#                           Set to 1 for ad-hoc manual runs that need to deploy
#                           a specific local state.
#   BUILD_TIMEOUT=20m       Hard cap for `pnpm build` (timeout(1) duration syntax).
#                           Default 20m. As of 2026-05-27 at HEAD a4f83c7b055 a
#                           clean build measures ~35s wall-clock total
#                           (annotations 3s, research:build 1s, research:enrich
#                           3s, tsc 9s, vite 18s) -- ~34x headroom. Re-profile
#                           with scripts/deploy/profile-build.sh before bumping.
#   BUILD_NODE_OPTIONS=...  Extra Node options for the build. Defaults to
#                           "--max-old-space-size=8192" so vite does not OOM on
#                           the current bundle.
#   DEPLOY_GATE_MAX_DELETIONS=100
#                           Diff-stat merge gate (issue #38398, dc9fdffa30
#                           incident): skip auto-merging any PR whose
#                           GitHub-reported deleted LINES exceed this; the PR
#                           is flagged with a comment for operator review.
#   DEPLOY_GATE_MAX_CHANGED_FILES=500
#                           Same gate, limit on the PR's changedFiles count.
#   SKIP_NOOP_BUILD_DETECTION=1
#                           Disable Strategy F (issue #22149): skipping the
#                           whole `pnpm build` invocation when no app-relevant
#                           paths changed since the last successful deploy.
#                           Set this if the heuristic ever produces a stale
#                           dist/ (would re-deploy stale artifacts).
#   DISABLE_BUILD_CACHE=1   Disable Strategy B (issue #22149): per-script
#                           input-hash skip-gates in annotations:build,
#                           research:build, and research:enrich. Set this for
#                           a forced full rebuild without removing the cache
#                           directory.

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

# Canonical completion-signal directory resolver (shared with the lean daemon
# so deployment signals land where the daemon reads them -- #41047).
# shellcheck source=../lib/completions-dir.sh
source "$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)/../lib/completions-dir.sh"

# Resolved worktree base (LOOM_WORKTREE_ROOT env var / .loom/config.json
# worktree.root override; default $REPO_ROOT/.loom/worktrees).
# shellcheck source=../lib/worktree-root.sh
source "$REPO_ROOT/scripts/lib/worktree-root.sh"
WORKTREES_BASE="$(loom_worktree_root "$REPO_ROOT")"
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
run_sync_branch=true
run_merge=true
run_sync=true
run_build=true
run_deploy=true

if $ONLY_MERGE; then run_sync_branch=false; run_sync=false; run_build=false; run_deploy=false; fi
if $ONLY_SYNC; then run_sync_branch=false; run_merge=false; run_build=false; run_deploy=false; fi
if $ONLY_BUILD; then run_sync_branch=false; run_merge=false; run_sync=false; run_deploy=false; fi
if $ONLY_DEPLOY; then run_sync_branch=false; run_merge=false; run_sync=false; run_build=false; fi

[[ "${SKIP_SYNC_BRANCH:-}" == "1" ]] && run_sync_branch=false
[[ "${SKIP_MERGE:-}" == "1" ]] && run_merge=false
[[ "${SKIP_SYNC:-}" == "1" ]] && run_sync=false
[[ "${SKIP_BUILD:-}" == "1" ]] && run_build=false
[[ "${SKIP_DEPLOY:-}" == "1" ]] && run_deploy=false

# The deployer's long-lived worktree lives on this branch, never on `main`
# (launch-agent.sh BRANCH_NAME must match).
DEPLOYER_BRANCH="${DEPLOYER_BRANCH:-feature/deployer}"

# True when this checkout is the deployer's long-lived worktree (a linked
# worktree whose directory is named "deployer").
in_deployer_worktree() {
    [[ "$(basename "$(pwd -P)")" == "deployer" ]] &&
        [[ "$(git rev-parse --git-dir 2>/dev/null)" != "$(git rev-parse --git-common-dir 2>/dev/null)" ]]
}

# Bring the working tree to origin/main WITHOUT stealing the `main` ref from
# another worktree. On 2026-07-11 the old `git checkout main` here ran inside
# the deployer worktree, moved it off feature/deployer, and squatted on `main`
# for two days — blocking every other checkout of main, after which the
# orphaned feature/deployer branch was swept by clean-branches.sh. It also had
# a latent footgun: when `checkout main` failed (main held elsewhere), the
# follow-up `reset --hard origin/main` nuked whatever branch was checked out.
sync_tree_to_main() {
    local cur
    cur=$(git rev-parse --abbrev-ref HEAD 2>/dev/null || echo "HEAD")
    if in_deployer_worktree; then
        if [[ "$cur" != "$DEPLOYER_BRANCH" ]]; then
            print_warning "Deployer worktree is on '$cur' — self-healing to $DEPLOYER_BRANCH"
        fi
        git checkout -B "$DEPLOYER_BRANCH" origin/main
    elif [[ "$cur" == "main" || "$cur" == "$DEPLOYER_BRANCH" ]]; then
        git reset --hard origin/main
    elif git checkout main 2>/dev/null; then
        git reset --hard origin/main
    else
        print_warning "'main' is checked out in another worktree — using detached origin/main instead"
        git checkout --detach origin/main
    fi
}

# ============================================================================
# Step 0a: Sync current branch to origin/main (fast-forward only)
# ============================================================================
#
# The deployer runs in a long-lived worktree on `feature/deployer` and loops
# via `claude-wrapper.sh --daemon`. setup_or_refresh_worktree in
# launch-agent.sh only syncs at LAUNCH, so without this per-cycle step the
# local branch drifts behind main and the build runs against stale code.
# See #21042 for the incident that motivated this.
#
# We use fast-forward only because the deployer must never carry local
# commits that aren't already in main. Any divergence (local commits,
# fetch failure, true conflict) is surfaced as a warning and the cycle
# continues with the existing checkout — better stale-but-running than
# auto-rebasing or hard-resetting work we didn't expect to see.
sync_branch() {
    print_header "Syncing Branch to origin/main"

    local current_branch
    current_branch=$(git rev-parse --abbrev-ref HEAD 2>/dev/null || echo "HEAD")

    if [[ "$current_branch" == "HEAD" ]]; then
        print_warning "Detached HEAD — skipping branch sync"
        return 0
    fi

    if [[ "$current_branch" == "main" ]]; then
        if in_deployer_worktree; then
            # Drifted state (see sync_tree_to_main): the deployer worktree
            # must never occupy the `main` ref. Heal it now, before merge.
            print_warning "Deployer worktree has 'main' checked out — self-healing to $DEPLOYER_BRANCH"
            git fetch origin main --quiet || print_warning "git fetch origin main failed"
            git checkout -B "$DEPLOYER_BRANCH" origin/main
            return 0
        fi
        # merge_prs already handles main directly via reset --hard; nothing
        # to do here. We still fetch so subsequent steps see fresh refs.
        print_info "On main — fetching only (merge step will reset to origin/main)"
        git fetch origin main --quiet || print_warning "git fetch origin main failed"
        return 0
    fi

    if $DRY_RUN; then
        echo "  Would fast-forward $current_branch to origin/main"
        return 0
    fi

    print_info "Fast-forwarding $current_branch to origin/main..."
    if ! git fetch origin main --quiet; then
        print_warning "git fetch origin main failed — continuing with existing refs"
        return 0
    fi

    # Fast-forward only. Any failure (not-ff, local commits, lock contention,
    # conflict) leaves the working tree untouched and surfaces as a warning.
    # We deliberately do NOT auto-rebase, reset --hard, or anything destructive
    # — that's a human-judgement call.
    if ! git merge --ff-only origin/main 2>/dev/null; then
        print_warning "$current_branch is not fast-forwardable to origin/main"
        print_warning "  (local commits or divergence — investigate before next cycle)"
        print_warning "  Continuing with current checkout; build may run against stale code."
    else
        local head_short
        head_short=$(git rev-parse --short HEAD 2>/dev/null || echo "unknown")
        print_success "$current_branch fast-forwarded to $head_short"
    fi
}

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

# ----------------------------------------------------------------------------
# Destructive-merge guard
# ----------------------------------------------------------------------------
# A PR branch built on an ancient/divergent base — or one whose remote tip was
# corrupted by a bad rebase+force-push earlier in this very pipeline — can carry
# a near-empty tree. Merging it deletes most of the repository: on 2026-06-23,
# PR #27891 merged such a branch and wiped 20,866 files from main. GitHub's
# additions/deletions are computed against the PR's own (ancient) merge-base, so
# they look harmless; the only reliable tell is the branch TIP's top-level entry
# count vs main's. Refuse to merge a branch missing a large fraction of the tree.
pr_branch_safe() {
    local pr="$1"
    local branch
    branch=$(gh pr view "$pr" --json headRefName --jq '.headRefName' 2>/dev/null) || return 0
    [[ -z "$branch" ]] && return 0
    git fetch -q origin "$branch" 2>/dev/null || return 0  # can't verify → don't block
    local main_n branch_n
    main_n=$(git ls-tree origin/main --name-only 2>/dev/null | wc -l | tr -d ' ')
    branch_n=$(git ls-tree FETCH_HEAD --name-only 2>/dev/null | wc -l | tr -d ' ')
    # If counts are unreadable, do not block (fail open on inspection errors).
    [[ -z "$main_n" || -z "$branch_n" || "$main_n" -eq 0 ]] && return 0
    # Refuse if the branch tip has fewer than 75% of main's top-level entries.
    if (( branch_n * 4 < main_n * 3 )); then
        print_warning "  #$pr: branch '$branch' tip has $branch_n top-level entries vs main's $main_n — corrupted/ancient base; REFUSING to merge (would delete files)"
        return 1
    fi
    return 0
}

# ----------------------------------------------------------------------------
# Diff-stat merge gate (issue #38398 — the dc9fdffa30 mass deletion)
# ----------------------------------------------------------------------------
# On 2026-07-11 a single-file research PR (#37576) silently carried 9,927 file
# deletions (a disk-slimmed worktree without sparse-checkout + `git add -A`)
# through this auto-merge path: research PRs are outside the loom judge
# lifecycle and nothing anywhere checked the diff stat, so +103/-1,201,128
# merged on mergeability alone. This gate refuses to AUTO-merge any PR whose
# reported deletions (lines, per GitHub) exceed DEPLOY_GATE_MAX_DELETIONS
# (default 100) or whose changedFiles exceed DEPLOY_GATE_MAX_CHANGED_FILES
# (default 500). Gated PRs are skipped and flagged with an idempotent PR
# comment for operator review — the deploy script must never silently label
# or close a PR. Intentional large PRs: an operator merges manually or raises
# the limits via env for one cycle.
#
# Complementary to pr_branch_safe above: pr_branch_safe catches corrupted/
# ancient branch TIPS (which GitHub's stats miss); this gate catches honest
# diff stats that are simply too destructive/wide to merge unreviewed.
DEPLOY_GATE_MAX_DELETIONS="${DEPLOY_GATE_MAX_DELETIONS:-100}"
DEPLOY_GATE_MAX_CHANGED_FILES="${DEPLOY_GATE_MAX_CHANGED_FILES:-500}"
DEPLOY_GATE_MARKER="<!-- deploy-diffstat-gate:38398 -->"

post_diffstat_gate_comment() {
    local pr="$1" additions="$2" deletions="$3" changed="$4"

    if $DRY_RUN; then
        echo "  Would post diff-stat gate comment on #$pr"
        return 0
    fi

    # Idempotent: post at most once per PR (marker survives edits/rebases).
    if gh pr view "$pr" --json comments --jq '.comments[].body' 2>/dev/null \
        | grep -qF "$DEPLOY_GATE_MARKER"; then
        return 0
    fi

    # Body goes via a temp file: a heredoc inside "$(...)" breaks under the
    # host's bash 3.2 parser, and --body-file also sidesteps quoting issues.
    local body_file
    body_file=$(mktemp)
    cat > "$body_file" <<EOF
$DEPLOY_GATE_MARKER
**Deployer diff-stat gate: auto-merge skipped.**

This PR reports **+$additions / -$deletions lines across $changed files**, exceeding the deployer auto-merge limits (deletions > $DEPLOY_GATE_MAX_DELETIONS or changedFiles > $DEPLOY_GATE_MAX_CHANGED_FILES).

Context: on 2026-07-11, a single-file research PR silently carried **9,927 file deletions** (a disk-slimmed worktree plus \`git add -A\`) through the auto-merge path and wiped most of the repository (commit dc9fdffa30 — see issue #38398). The deployer therefore no longer auto-merges deletion-heavy or very wide PRs.

- **If this diff is intentional**: an operator can merge manually (\`gh pr merge $pr --squash\`) or raise the limits for one cycle via \`DEPLOY_GATE_MAX_DELETIONS\` / \`DEPLOY_GATE_MAX_CHANGED_FILES\`.
- **If it is not**: check the branch for phantom deletions: \`git diff --name-status --diff-filter=D origin/main...HEAD\`.
EOF
    gh pr comment "$pr" --body-file "$body_file" >/dev/null 2>&1 \
        || print_warning "  Could not post gate comment on #$pr"
    rm -f "$body_file"
}

# Returns 0 when the PR's diff stat is within auto-merge limits; 1 when the
# gate trips (skip the merge). Fails OPEN on inspection errors — the tree-level
# pr_branch_safe and assert_main_intact guards still stand behind it.
pr_diffstat_safe() {
    local pr="$1"
    local stats additions deletions changed
    stats=$(gh pr view "$pr" --json additions,deletions,changedFiles 2>/dev/null) || return 0
    additions=$(echo "$stats" | jq -r '.additions // 0' 2>/dev/null) || return 0
    deletions=$(echo "$stats" | jq -r '.deletions // 0' 2>/dev/null) || return 0
    changed=$(echo "$stats" | jq -r '.changedFiles // 0' 2>/dev/null) || return 0
    [[ "$deletions" =~ ^[0-9]+$ && "$changed" =~ ^[0-9]+$ ]] || return 0

    if (( deletions > DEPLOY_GATE_MAX_DELETIONS || changed > DEPLOY_GATE_MAX_CHANGED_FILES )); then
        print_warning "  #$pr: DIFF-STAT GATE — +$additions/-$deletions across $changed files exceeds auto-merge limits (deletions <= $DEPLOY_GATE_MAX_DELETIONS, changedFiles <= $DEPLOY_GATE_MAX_CHANGED_FILES); skipping, operator review required (dc9fdffa30 guard, #38398)"
        post_diffstat_gate_comment "$pr" "$additions" "$deletions" "$changed"
        return 1
    fi
    return 0
}

# Assert origin/main still holds a full tree. Call after the merge loop; if main
# has collapsed, something merged a destructive branch — abort before deploying.
assert_main_intact() {
    git fetch -q origin main 2>/dev/null || return 0
    local n
    n=$(git ls-tree origin/main --name-only 2>/dev/null | wc -l | tr -d ' ')
    [[ -z "$n" || "$n" -eq 0 ]] && return 0
    if (( n < 30 )); then
        print_error "origin/main has only $n top-level entries — a destructive merge corrupted main. ABORTING deploy. Recover by reverting the offending merge commit."
        exit 1
    fi
    print_success "main integrity OK ($n top-level entries)"
}

# ============================================================================
# Step 1: Merge PRs
# ============================================================================
merge_prs() {
    print_header "Merging Pull Requests"

    # Update main first. Retry once and never abort on the benign
    # "unable to update local ref" race: when a prior merge in this same loop
    # just advanced origin/main, a concurrent fetch can fail to lock the
    # remote-tracking ref even though the data is fetched into FETCH_HEAD and
    # the ref ends up current. Under `set -e` an unguarded fetch would kill the
    # whole merge step after merging only ~1 PR (see issue: deploy fetch race).
    print_info "Updating main branch..."
    git fetch origin main --quiet || git fetch origin main --quiet || true
    # Stash before checkout — dirty files block branch switch
    git stash 2>/dev/null || true
    sync_tree_to_main

    local merged=0
    local failed=0

    # Skip drafts (researcher "build pending" PRs) and PRs with loom:review-requested
    # (those are opted into Loom Judge review).
    local jq_filter='[.[] | select(.isDraft | not) | select(.labels | map(.name) | any(. == "loom:review-requested") | not)]'
    local all_prs=$(gh pr list --limit 100 --json number,mergeable,labels,isDraft)
    local eligible_prs=$(echo "$all_prs" | jq "$jq_filter")
    local total=$(echo "$eligible_prs" | jq 'length')
    local drafts=$(echo "$all_prs" | jq '[.[] | select(.isDraft)] | length')
    local review_requested=$(echo "$all_prs" | jq '[.[] | select(.isDraft | not) | select(.labels | map(.name) | any(. == "loom:review-requested"))] | length')

    print_info "Found $total eligible PRs ($drafts drafts skipped, $review_requested loom:review-requested skipped)"

    if [[ $total -eq 0 ]]; then
        print_success "No PRs to merge"
        return 0
    fi

    # Try to merge each PR
    for pr in $(echo "$eligible_prs" | jq -r '.[] | select(.mergeable == "MERGEABLE") | .number'); do
        if $DRY_RUN; then
            if ! pr_diffstat_safe "$pr"; then
                echo "  Would skip PR #$pr (diff-stat gate)"
            else
                echo "  Would merge PR #$pr"
                ((++merged))
            fi
        else
            echo -n "  #$pr: "
            if ! pr_branch_safe "$pr"; then
                echo "skipped (unsafe tree)"
                ((++failed))
            elif ! pr_diffstat_safe "$pr"; then
                echo "skipped (diff-stat gate — operator review required)"
                ((++failed))
            elif gh pr merge "$pr" --squash 2>/dev/null; then
                echo "merged"
                ((++merged))
            else
                echo "failed"
                ((++failed))
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
                ((++merged))
            else
                echo -n "  #$pr: "
                if ! pr_branch_safe "$pr"; then
                    echo "skipped (unsafe tree)"
                elif ! pr_diffstat_safe "$pr"; then
                    echo "skipped (diff-stat gate — operator review required)"
                elif gh pr merge "$pr" --squash 2>/dev/null; then
                    echo "merged"
                    ((++merged))
                else
                    echo "skipped"
                fi
            fi
        fi
    done

    # Try to rebase conflicting PRs
    for pr in $(echo "$eligible_prs" | jq -r '.[] | select(.mergeable == "CONFLICTING") | .number'); do
        local branch=$(gh pr view "$pr" --json headRefName --jq '.headRefName')

        # Reap superseded PRs before wasting a rebase on them (fix A).
        # A CONFLICTING research PR whose new proof file already exists on main is
        # an add/add duplicate of an already-formalized result — the loser of a
        # same-problem race between two agents. No rebase can ever land it; close
        # it so the backlog drains instead of accumulating dead duplicates.
        if [[ -x "$REPO_ROOT/scripts/research/check-superseded.sh" ]]; then
            # Fetch the PR head into an explicit ref rather than relying on
            # FETCH_HEAD (issue #34555): a swallowed fetch failure would otherwise
            # leave FETCH_HEAD pointing at a *previous* branch, so the check would
            # silently compare the wrong tree. Only run the reap check when this
            # fetch actually succeeds; on failure, fall through to the rebase path.
            local reap_ref="refs/tmp/reap-check-$pr"
            if git fetch origin "$branch:$reap_ref" --force --quiet 2>/dev/null; then
                local sup_verdict
                sup_verdict=$("$REPO_ROOT/scripts/research/check-superseded.sh" \
                    --ref "$reap_ref" --base origin/main --quiet 2>/dev/null | tail -1 || echo "")
                git update-ref -d "$reap_ref" 2>/dev/null || true
                if [[ "$sup_verdict" == "SUPERSEDED" ]]; then
                    if $DRY_RUN; then
                        echo "  Would close #$pr as superseded (proof file already on main)"
                    else
                        print_warning "Closing #$pr as superseded — proof file already on main (add/add duplicate)"
                        gh pr close "$pr" --delete-branch --comment "Closing as **superseded** — automated race-condition cleanup by the deployer.

Every new proof file this PR adds already exists on \`main\` (landed via a competing PR that won the merge race). This branch is an unmergeable add/add duplicate of an already-formalized result, so no rebase can land it.

This branch has been deleted. If you believe this version carries unique content \`main\` lacks, re-push the branch and open a fresh PR rebased onto \`main\`. See the pre-submission guard (\`scripts/research/check-superseded.sh\`) that now prevents most of these." 2>/dev/null \
                            && print_success "Closed superseded #$pr" || print_warning "Could not close #$pr"
                    fi
                    continue
                fi
            else
                print_warning "  Could not fetch $branch for reap check on #$pr; proceeding to rebase"
            fi
        fi

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
            worktree_path="$WORKTREES_BASE/temp-rebase-$$"
            print_info "Creating temporary worktree for rebase..."
            mkdir -p "$WORKTREES_BASE"
            git fetch origin "$branch"
            git worktree add "$worktree_path" "origin/$branch" --detach 2>/dev/null || {
                print_warning "Could not create worktree for #$pr"
                ((++failed))
                continue
            }
            # --no-track: don't write upstream-tracking config to .git/config,
            # which is shared across all worktrees and serialized via a single
            # lockfile. With ~60 worktrees doing concurrent rebases this lock
            # is the dominant failure mode ("could not lock config file").
            #
            # The checkout fails fatally ("branch is already used by worktree")
            # when this branch is checked out in an active agent worktree that
            # our find-worktree scan missed (e.g. a race, or a detached state at
            # scan time). Under `set -e` that would crash the whole merge loop
            # before build/deploy, so guard it: clean up the temp worktree, mark
            # the PR failed, and continue with the rest.
            if ! (cd "$worktree_path" && git checkout --no-track -B "$branch" "origin/$branch") 2>/dev/null; then
                print_warning "Branch $branch is checked out elsewhere; skipping rebase for #$pr"
                git worktree remove "$worktree_path" --force 2>/dev/null || true
                ((++failed))
                continue
            fi
            temp_worktree=true
        fi

        (
            cd "$worktree_path"
            git stash 2>/dev/null || true
            # Tolerate the benign "unable to update local ref" race (a prior
            # merge in this loop just moved origin/main); FETCH_HEAD is still
            # populated and the ref ends up current, so don't let set -e abort.
            git fetch origin main --quiet || git fetch origin main --quiet || true
            git fetch origin "$branch" --quiet || true
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
                            proofs/Proofs.lean)
                                # Auto-generated module index (pure `import Proofs.X`
                                # lines, regenerated by generate-proofs-imports.sh).
                                # Every research/enrichment PR appends to it, so it
                                # conflicts whenever a sibling lands first. Union-merge
                                # the import lines — safe because it carries no proof
                                # math. This is what unblocks the research backlog.
                                print_info "  Union-merging proofs/Proofs.lean (auto-generated import index)..."
                                git show :2:"$conflict_file" > /tmp/proofs-ours.lean 2>/dev/null || true
                                git show :3:"$conflict_file" > /tmp/proofs-theirs.lean 2>/dev/null || true
                                {
                                    printf -- '-- Auto-generated file - do not edit manually\n'
                                    printf -- '-- Run: ./.lean/scripts/generate-proofs-imports.sh\n\n'
                                    cat /tmp/proofs-ours.lean /tmp/proofs-theirs.lean 2>/dev/null \
                                        | grep -E '^import Proofs\.' | sort -u
                                } > "$conflict_file"
                                rm -f /tmp/proofs-ours.lean /tmp/proofs-theirs.lean
                                git add "$conflict_file"
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
        if [[ "$new_status" == "MERGEABLE" ]] && pr_branch_safe "$pr" && pr_diffstat_safe "$pr" && gh pr merge "$pr" --squash 2>/dev/null; then
            echo "merged"
            ((++merged))
        else
            echo "still conflicting ($new_status)"
            ((++failed))
        fi
    done

    print_success "Merged $merged PRs ($failed failed/skipped)"

    # Update main again after merges (tolerate the ref-lock race, see above)
    git fetch origin main --quiet || git fetch origin main --quiet || true
    git reset --hard origin/main

    # Safety net: confirm the merges did not collapse main's tree.
    assert_main_intact
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
    if not isinstance(knowledge, dict):
        knowledge = {}

    # Some problem files store insights/builtItems as a literal count (int)
    # rather than a list of entries. Tolerate both shapes.
    def _count(v):
        if isinstance(v, (list, str, dict)):
            return len(v)
        if isinstance(v, bool):
            return 0
        if isinstance(v, (int, float)):
            return int(v)
        return 0

    insights = _count(knowledge.get("insights", []))
    built = _count(knowledge.get("builtItems", []))

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

    # Strategy F (issue #22149): skip the entire `pnpm build` invocation when
    # no app-relevant paths have changed since the last successful deploy.
    # The deployer cycle commonly merges only docs/issue-comment/research-state
    # tweaks — in those cycles dist/ is byte-for-byte the same as last cycle's
    # output. Wrangler's content-hash uploader will already short-circuit on
    # unchanged blobs, but it still re-uploads the manifest and burns ~3min on
    # `pnpm build`. Skipping the build entirely turns the no-op cycle into a
    # ~10s deploy.
    #
    # The set of "app-relevant" paths must include everything the bundle is
    # derived from: src/, public/, the Lean proofs, the data scripts, and
    # build-tool config. Adding a path here is safe (we just do an extra build
    # if it changes); omitting a path is unsafe (we'd ship stale dist/).
    SKIP_BUILD_AS_NO_OP=false
    if [[ "${SKIP_NOOP_BUILD_DETECTION:-}" != "1" ]] && [[ -d "$REPO_ROOT/dist" ]]; then
        local last_deployed_commit
        last_deployed_commit=$(cat "$REPO_ROOT/.build-cache/last-deployed-commit" 2>/dev/null || echo "")
        local current_head
        current_head=$(git rev-parse HEAD 2>/dev/null || echo "")
        if [[ -n "$last_deployed_commit" ]] \
           && [[ -n "$current_head" ]] \
           && [[ "$last_deployed_commit" != "$current_head" ]] \
           && git cat-file -e "${last_deployed_commit}^{commit}" 2>/dev/null; then
            if git diff --quiet "$last_deployed_commit" "$current_head" -- \
                 src/ public/ proofs/Proofs/ \
                 scripts/annotations/ scripts/research/ scripts/lib/ \
                 package.json pnpm-lock.yaml tsconfig.json tsconfig.app.json tsconfig.node.json \
                 vite.config.ts 2>/dev/null; then
                print_info "No app-relevant changes since ${last_deployed_commit:0:8} — skipping pnpm build, reusing dist/"
                SKIP_BUILD_AS_NO_OP=true
            fi
        fi
    fi

    if $SKIP_BUILD_AS_NO_OP; then
        print_success "Build skipped (no-op cycle); existing dist/ will be redeployed"
        return 0
    fi

    # Cap node heap at 8 GB so OOMs surface as deterministic exits rather than
    # thrashing the host, and bound the whole chain at BUILD_TIMEOUT so a hung
    # step can't accumulate zombie pnpm/vite processes across cycles. The cap
    # is configurable via env (BUILD_TIMEOUT, BUILD_NODE_OPTIONS) so future
    # adjustments don't require code changes. A profiler is available at
    # scripts/deploy/profile-build.sh -- re-run before tightening or loosening
    # the default.
    local build_timeout="${BUILD_TIMEOUT:-20m}"
    local build_node_options="${BUILD_NODE_OPTIONS:---max-old-space-size=8192}"
    print_info "Running pnpm build (cap ${build_timeout}, NODE_OPTIONS=${build_node_options})..."
    # Capture full log so failures aren't masked by `| tail -5` (which forces
    # the pipe's exit status to tail's, always 0).
    local build_log
    build_log=$(mktemp)
    local build_status=0
    NODE_OPTIONS="${NODE_OPTIONS:-} ${build_node_options}" \
        timeout --kill-after=30 "$build_timeout" pnpm build > "$build_log" 2>&1 \
        || build_status=$?
    tail -20 "$build_log"
    case $build_status in
        0)
            print_success "Build completed"
            rm -f "$build_log"
            ;;
        124|137)
            print_error "Build timed out after ${build_timeout} (status $build_status); see full log at $build_log"
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
        print_info "Expected: the Personal Account (see scripts/deploy/check-account.sh)"
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

        # Strategy F (issue #22149): record the full commit hash of this
        # successful deploy so the next cycle can compare HEAD against it and
        # skip pnpm build when no app-relevant paths changed. Only updated
        # AFTER a successful wrangler upload — failed deploys leave the prior
        # value intact so we re-attempt the build next cycle.
        mkdir -p "$REPO_ROOT/.build-cache"
        git rev-parse HEAD > "$REPO_ROOT/.build-cache/last-deployed-commit" 2>/dev/null || true

        # Prune old deployments, keeping only the latest N
        prune_old_deployments

        # Create completion signal for daemon stats tracking. Resolve the
        # canonical (main-checkout) completions dir so the daemon actually sees
        # it -- writing to this worktree's .loom/ would be invisible (#41047).
        local completions_dir
        completions_dir="$(resolve_completions_dir)"
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
        # Return to the pipeline branch (never steal `main` from another worktree)
        sync_tree_to_main
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
    echo "  Sync Branch: $run_sync_branch"
    echo "  Merge PRs:   $run_merge"
    echo "  Sync Data:   $run_sync"
    echo "  Build:       $run_build"
    echo "  Deploy:      $run_deploy"
    echo "  Dry Run:     $DRY_RUN"

    # The primary checkout is shared by every concurrently-running agent:
    # cycles run here dirty the tree others read, and past cycles left it
    # stuck on chore/sync-data branches when `checkout main` failed. The
    # deployer agent must run from its worktree (.loom/worktrees/deployer).
    if [[ "$(git rev-parse --git-dir 2>/dev/null)" == "$(git rev-parse --git-common-dir 2>/dev/null)" ]]; then
        print_warning "Running in the PRIMARY checkout, not a worktree."
        print_warning "  Deployer agents: cd to your worktree (.loom/worktrees/deployer) first."
        print_warning "  Ad-hoc/manual runs: this is allowed but concurrent agents share this tree."
    fi

    $run_sync_branch && sync_branch
    $run_merge && merge_prs
    $run_sync && sync_data
    $run_build && build_website
    $run_deploy && deploy_website
    $run_sync && commit_changes

    print_header "Complete"
    print_success "Deploy pipeline finished"
}

main
