#!/bin/bash
#
# ingest-issue-problems.sh - Bridge GitHub research issues into the candidate pool
#
# Scans open GitHub issues carrying a dedicated trigger label
# (default: research:queued) and turns each not-yet-ingested issue into a
# candidate-pool entry that `claim-problem.sh claim-random` will serve like any
# other problem. This is an ADDITIONAL problem source for the Seeker — it does
# NOT replace the gallery-derived sourcing.
#
# The research SQLite database (research/db/knowledge.db) is the single source
# of truth: sync_pool.py regenerates .lean/state/candidate-pool.json from it
# every Seeker cycle. So we INSERT the synthesized problem into the DB (and
# write the site JSON), then regenerate the pool — otherwise the next
# sync_pool.py run would drop an issue-sourced candidate that lived only in the
# pool JSON.
#
# Idempotency (never ingest the same issue twice) is enforced three ways:
#   1. The scan can skip issues that already carry the "pooled" marker label.
#   2. A problem whose site JSON already records `sourceIssue: <n>` is skipped.
#   3. A slug that already exists in the DB is skipped.
# On successful ingest the issue is marked with the pooled label + a one-line
# comment linking the pool slug.
#
# Usage:
#   ./ingest-issue-problems.sh                 Ingest all newly-labeled issues
#   ./ingest-issue-problems.sh --dry-run       Preview only; mutate nothing
#   ./ingest-issue-problems.sh --repo O/R      Override target repo
#   ./ingest-issue-problems.sh --label NAME    Override trigger label
#   ./ingest-issue-problems.sh --help          Show this help
#
# Environment:
#   INGEST_REPO           Target repo (default: rjwalters/lean-genius)
#   INGEST_TRIGGER_LABEL  Trigger label to scan for (default: research:queued)
#   INGEST_POOLED_LABEL   Marker label applied on ingest (default: research:pooled)
#
# Exit status is 0 whenever the scan completes (including "nothing to do").

set -euo pipefail

# --- Configuration ----------------------------------------------------------

REPO="${INGEST_REPO:-rjwalters/lean-genius}"
TRIGGER_LABEL="${INGEST_TRIGGER_LABEL:-research:queued}"
POOLED_LABEL="${INGEST_POOLED_LABEL:-research:pooled}"
DRY_RUN=false

while [[ $# -gt 0 ]]; do
    case "$1" in
        --dry-run|-n) DRY_RUN=true; shift ;;
        --repo) REPO="$2"; shift 2 ;;
        --label) TRIGGER_LABEL="$2"; shift 2 ;;
        --help|-h)
            sed -n '2,40p' "$0" | sed 's/^# \{0,1\}//'
            exit 0
            ;;
        *) echo "Unknown option: $1" >&2; exit 1 ;;
    esac
done

# --- Repo root resolution ---------------------------------------------------
#
# Claims, the DB, and the gitignored candidate pool are SHARED coordination
# state. When this runs from a linked worktree, an upward ".git" search resolves
# to the worktree (where .lean/state/candidate-pool.json does not exist), so we
# must resolve to the MAIN worktree root via the common git dir — exactly as
# claim-problem.sh does — so every agent shares one pool and one DB.
find_repo_root() {
    local common_dir
    if common_dir="$(git rev-parse --git-common-dir 2>/dev/null)" \
        && common_dir="$(cd "$common_dir" 2>/dev/null && pwd)"; then
        dirname "$common_dir"
        return 0
    fi
    local dir="$PWD"
    while [[ "$dir" != "/" ]]; do
        if [[ -d "$dir/.git" ]] || [[ -f "$dir/.git" ]]; then
            echo "$dir"; return 0
        fi
        dir="$(dirname "$dir")"
    done
    echo "Error: Not in a git repository" >&2
    return 1
}

REPO_ROOT="$(find_repo_root)"
DB_PATH="$REPO_ROOT/research/db/knowledge.db"
PROBLEMS_JSON_DIR="$REPO_ROOT/src/data/research/problems"
SYNC_POOL="$REPO_ROOT/research/db/sync_pool.py"

# Colors
RED='\033[0;31m'; GREEN='\033[0;32m'; BLUE='\033[0;34m'; YELLOW='\033[1;33m'; NC='\033[0m'
info()  { echo -e "${BLUE}i $1${NC}"; }
ok()    { echo -e "${GREEN}+ $1${NC}"; }
warn()  { echo -e "${YELLOW}! $1${NC}"; }
err()   { echo -e "${RED}x $1${NC}" >&2; }

# --- Dependency check -------------------------------------------------------
check_deps() {
    local missing=()
    command -v gh >/dev/null 2>&1 || missing+=("gh")
    command -v jq >/dev/null 2>&1 || missing+=("jq")
    command -v python3 >/dev/null 2>&1 || missing+=("python3")
    if [[ ${#missing[@]} -gt 0 ]]; then
        err "Missing dependencies: ${missing[*]}"
        exit 1
    fi
}

# --- Helpers ----------------------------------------------------------------

# slugify <number> <title> -> "issue-<n>-<sanitized-title>"
# Embedding the issue number guarantees a unique, provenance-bearing slug.
slugify() {
    local number="$1" title="$2" base
    base="$(printf '%s' "$title" \
        | tr '[:upper:]' '[:lower:]' \
        | tr -c 'a-z0-9' '-' \
        | tr -s '-' \
        | sed 's/^-//; s/-$//' \
        | cut -c1-50 \
        | sed 's/-$//')"
    if [[ -z "$base" ]]; then
        echo "issue-${number}"
    else
        echo "issue-${number}-${base}"
    fi
}

# db_has_slug <slug>  -> exit 0 if the slug is already a row in the DB
db_has_slug() {
    local slug="$1"
    [[ -f "$DB_PATH" ]] || return 1
    python3 - "$DB_PATH" "$slug" 2>/dev/null <<'PY'
import sqlite3, sys
db, slug = sys.argv[1], sys.argv[2]
try:
    c = sqlite3.connect(db)
    row = c.execute("SELECT 1 FROM problems WHERE slug = ?", (slug,)).fetchone()
    c.close()
    sys.exit(0 if row else 1)
except Exception:
    sys.exit(1)
PY
}

# already_ingested <number> <slug>  -> 0 if we've seen this issue before
already_ingested() {
    local number="$1" slug="$2"
    # (2) site JSON already records this sourceIssue
    if grep -rlq "\"sourceIssue\": *${number}\b" "$PROBLEMS_JSON_DIR" 2>/dev/null; then
        return 0
    fi
    # (3) slug already present in the DB
    if db_has_slug "$slug"; then
        return 0
    fi
    return 1
}

# db_insert <slug> <title> <statement_plain>
db_insert() {
    local slug="$1" title="$2" statement="$3"
    python3 - "$DB_PATH" "$slug" "$title" "$statement" <<'PY'
import sqlite3, sys, json, datetime
db, slug, title, statement = sys.argv[1], sys.argv[2], sys.argv[3], sys.argv[4]
now = datetime.datetime.now(datetime.timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ")
tags = json.dumps(["issue-sourced"])
c = sqlite3.connect(db)
# Issue-sourced problems are explicit human requests: tier B, mid significance,
# mid tractability, status available. ON CONFLICT DO NOTHING keeps this
# idempotent even if the slug slipped past the earlier dedup checks.
c.execute(
    """
    INSERT INTO problems
        (slug, title, status, tier, significance, tractability,
         statement_plain, tags, started_at, last_updated)
    VALUES (?, ?, 'available', 'B', 5, 5, ?, ?, ?, ?)
    ON CONFLICT(slug) DO NOTHING
    """,
    (slug, title, statement, tags, now, now),
)
c.commit()
c.close()
PY
}

# write_problem_json <slug> <number> <title> <url> <statement_plain>
write_problem_json() {
    local slug="$1" number="$2" title="$3" url="$4" statement="$5"
    local now
    now="$(date -u +"%Y-%m-%dT%H:%M:%SZ")"
    local out="$PROBLEMS_JSON_DIR/${slug}.json"
    mkdir -p "$PROBLEMS_JSON_DIR"
    jq -n \
        --arg slug "$slug" \
        --arg title "$title" \
        --arg statement "$statement" \
        --arg url "$url" \
        --arg now "$now" \
        --argjson number "$number" \
        '{
            slug: $slug,
            title: $title,
            phase: "OBSERVE",
            status: "available",
            tier: "B",
            path: "full",
            sourceIssue: $number,
            problemStatement: { formal: "", plain: $statement, whyMatters: [] },
            knownResults: { proven: [], open: [], goal: "" },
            currentState: {
                phase: "OBSERVE",
                since: $now,
                iteration: 1,
                focus: "Initial problem understanding. Read the source issue and gather context.",
                blockers: [],
                nextAction: "Read the source GitHub issue thoroughly and acquire full context.",
                attemptCounts: { total: 0, currentApproach: 0, approachesTried: 0 }
            },
            knowledge: {
                progressSummary: "",
                builtItems: [],
                insights: [],
                mathlibGaps: [],
                nextSteps: [],
                markdown: ("# Knowledge Base: " + $slug + "\n\nSourced from GitHub issue #" + ($number|tostring) + " (" + $url + ").\n\n---\n\n## Problem Understanding\n\n[Initial observations about the problem will be recorded here]\n\n---\n\n## Insights\n\n[Insights from research attempts will be accumulated here]\n\n---\n\n## Dead Ends\n\n[Approaches known not to work will be documented here]\n")
            },
            tags: ["issue-sourced"],
            relatedProofs: [],
            references: { papers: [], urls: [$url], mathlib: [] },
            started: $now,
            lastUpdate: $now,
            significance: 5,
            tractability: 5
        }' > "$out"
    echo "$out"
}

# --- Ingest one issue -------------------------------------------------------
ingest_one() {
    local number="$1" title="$2" url="$3" body="$4" has_pooled="$5"
    local slug statement
    slug="$(slugify "$number" "$title")"

    # (1) marker label already present -> definitely ingested.
    if [[ "$has_pooled" == "true" ]]; then
        info "#$number already carries '$POOLED_LABEL' — skipping ($slug)"
        return 0
    fi

    if already_ingested "$number" "$slug"; then
        info "#$number already ingested ($slug) — skipping"
        return 0
    fi

    # Plain-language statement: prefer the issue body, fall back to the title.
    # Trim to a reasonable length for the pool "notes" summary.
    statement="$(printf '%s' "$body" | tr '\r' ' ' | tr '\n' ' ' | sed 's/  */ /g; s/^ //; s/ $//' | cut -c1-500)"
    [[ -z "$statement" ]] && statement="$title"

    if [[ "$DRY_RUN" == "true" ]]; then
        warn "[dry-run] would ingest #$number as '$slug'"
        echo "           title: $title"
        echo "           statement: ${statement:0:100}..."
        echo "           would: DB insert, write $PROBLEMS_JSON_DIR/${slug}.json, sync pool, label '$POOLED_LABEL' + comment"
        return 0
    fi

    if [[ ! -f "$DB_PATH" ]]; then
        err "DB not found at $DB_PATH — run 'python3 research/db/migrate.py' first. Skipping #$number."
        return 0
    fi

    db_insert "$slug" "$title" "$statement"
    local json_path
    json_path="$(write_problem_json "$slug" "$number" "$title" "$url" "$statement")"
    ok "Ingested #$number -> $slug"
    info "  DB row + $json_path"

    # Regenerate the consumed pool from the DB (source of truth).
    if python3 "$SYNC_POOL" >/dev/null 2>&1; then
        info "  Regenerated candidate pool"
    else
        warn "  sync_pool.py failed — pool not refreshed (candidate is in the DB and will appear on the next Seeker refresh)"
    fi

    # Mark the issue so we never ingest it twice, and leave a breadcrumb.
    if gh issue edit "$number" --repo "$REPO" --add-label "$POOLED_LABEL" >/dev/null 2>&1; then
        info "  Labeled #$number '$POOLED_LABEL'"
    else
        warn "  Could not add '$POOLED_LABEL' to #$number (label missing? run: gh label sync)"
    fi
    if gh issue comment "$number" --repo "$REPO" \
        --body "Ingested into the researcher candidate pool as \`$slug\` (status: available). A Researcher can now claim it via \`claim-problem.sh claim-random\`." \
        >/dev/null 2>&1; then
        info "  Commented on #$number"
    else
        warn "  Could not comment on #$number"
    fi
}

# --- Main -------------------------------------------------------------------
main() {
    check_deps

    info "Scanning $REPO for open issues labeled '$TRIGGER_LABEL'..."
    local issues_json count
    if ! issues_json="$(gh issue list --repo "$REPO" --state open --label "$TRIGGER_LABEL" \
            --limit 200 --json number,title,body,url,labels 2>/dev/null)"; then
        err "gh issue list failed (auth? label '$TRIGGER_LABEL' missing?)"
        exit 0
    fi
    count="$(jq 'length' <<<"$issues_json")"
    if [[ "$count" -eq 0 ]]; then
        ok "No open issues labeled '$TRIGGER_LABEL' — nothing to ingest."
        return 0
    fi
    info "Found $count issue(s) labeled '$TRIGGER_LABEL'."

    local i number title url body has_pooled
    for ((i = 0; i < count; i++)); do
        number="$(jq -r ".[$i].number" <<<"$issues_json")"
        title="$(jq -r ".[$i].title" <<<"$issues_json")"
        url="$(jq -r ".[$i].url" <<<"$issues_json")"
        body="$(jq -r ".[$i].body // \"\"" <<<"$issues_json")"
        has_pooled="$(jq -r ".[$i].labels | map(.name) | index(\"$POOLED_LABEL\") != null" <<<"$issues_json")"
        ingest_one "$number" "$title" "$url" "$body" "$has_pooled"
    done

    ok "Issue intake complete."
}

main
