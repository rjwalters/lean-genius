#!/usr/bin/env bash
#
# Aristotle: prune zombie jobs from research/aristotle-jobs.json
#
# Moves all entries with status == "zombie" out of aristotle-jobs.json into a
# forensics archive at research/aristotle-jobs-archive-zombies.json.
#
# Idempotent: re-running when there are zero zombies leaves the jobs file
# untouched (only updates the archive file if new zombies were found).
#
# Uses jq for all JSON manipulation and atomic temp+mv writes.
#
# Usage:
#   ./scripts/aristotle/prune-zombies.sh [--jobs PATH] [--archive PATH] [--quiet]
#
# Exit codes:
#   0 = success (including no-op when 0 zombies)
#   1 = error (file missing, jq missing, write failed, etc.)
#

set -euo pipefail

JOBS_FILE="research/aristotle-jobs.json"
ARCHIVE_FILE="research/aristotle-jobs-archive-zombies.json"
QUIET=false

while [[ $# -gt 0 ]]; do
    case "$1" in
        --jobs)
            JOBS_FILE="$2"; shift 2;;
        --archive)
            ARCHIVE_FILE="$2"; shift 2;;
        --quiet|-q)
            QUIET=true; shift;;
        -h|--help)
            sed -n '2,18p' "$0" | sed 's/^# \{0,1\}//'
            exit 0;;
        *)
            echo "Unknown argument: $1" >&2
            exit 1;;
    esac
done

log() {
    if ! $QUIET; then
        echo "$@"
    fi
}

if ! command -v jq >/dev/null 2>&1; then
    echo "ERROR: jq is required but not installed." >&2
    exit 1
fi

if [[ ! -f "$JOBS_FILE" ]]; then
    echo "ERROR: jobs file not found: $JOBS_FILE" >&2
    exit 1
fi

# Count zombies before
ZOMBIE_COUNT=$(jq '[.jobs[] | select(.status == "zombie")] | length' "$JOBS_FILE")
TOTAL_BEFORE=$(jq '.jobs | length' "$JOBS_FILE")

log "Aristotle prune-zombies:"
log "  Jobs file:    $JOBS_FILE"
log "  Archive file: $ARCHIVE_FILE"
log "  Total jobs (before): $TOTAL_BEFORE"
log "  Zombies found:       $ZOMBIE_COUNT"

if [[ "$ZOMBIE_COUNT" -eq 0 ]]; then
    log "  No zombies to prune; jobs file left unchanged."
    # Still ensure archive file is valid (or create empty one for first run consistency).
    if [[ ! -f "$ARCHIVE_FILE" ]]; then
        log "  Archive file does not exist; leaving as-is (no zombies to record)."
    fi
    exit 0
fi

# Build pruned jobs file (non-zombie entries only)
PRUNED_TMP="$(mktemp "${JOBS_FILE}.tmp.XXXXXX")"
trap 'rm -f "$PRUNED_TMP" "$ARCHIVE_TMP" 2>/dev/null || true' EXIT

jq '.jobs |= map(select(.status != "zombie"))' "$JOBS_FILE" > "$PRUNED_TMP"

# Build archive entry: timestamp + zombies pulled from jobs file.
# Archive schema: { description, runs: [ { archived_at, source, jobs: [...] } ] }
# This makes the file append-safe across multiple prune runs.

ZOMBIES_JSON="$(jq '[.jobs[] | select(.status == "zombie")]' "$JOBS_FILE")"
NOW="$(date -u +%Y-%m-%dT%H:%M:%SZ)"

ARCHIVE_TMP="$(mktemp "${ARCHIVE_FILE}.tmp.XXXXXX")"

if [[ -f "$ARCHIVE_FILE" ]]; then
    # Append a new run to the existing archive.
    jq \
        --argjson new_jobs "$ZOMBIES_JSON" \
        --arg now "$NOW" \
        --arg source "$JOBS_FILE" \
        '
        # Normalize legacy shape if archive was previously a bare array.
        (if type == "array" then {description: "Archived Aristotle zombie jobs (forensics only; do not re-submit).", runs: [{archived_at: "legacy", source: "unknown", jobs: .}]} else . end)
        | .description = (.description // "Archived Aristotle zombie jobs (forensics only; do not re-submit).")
        | .runs = ((.runs // []) + [{archived_at: $now, source: $source, jobs: $new_jobs}])
        | .total = ([.runs[].jobs | length] | add)
        ' "$ARCHIVE_FILE" > "$ARCHIVE_TMP"
else
    jq -n \
        --argjson new_jobs "$ZOMBIES_JSON" \
        --arg now "$NOW" \
        --arg source "$JOBS_FILE" \
        '
        {
            description: "Archived Aristotle zombie jobs (forensics only; do not re-submit).",
            runs: [{archived_at: $now, source: $source, jobs: $new_jobs}],
            total: ($new_jobs | length)
        }
        ' > "$ARCHIVE_TMP"
fi

# Atomic moves (move archive first; if jobs move fails we have at least preserved a copy).
mv "$ARCHIVE_TMP" "$ARCHIVE_FILE"
mv "$PRUNED_TMP" "$JOBS_FILE"

# Verify
POST_ZOMBIES=$(jq '[.jobs[] | select(.status == "zombie")] | length' "$JOBS_FILE")
POST_TOTAL=$(jq '.jobs | length' "$JOBS_FILE")
ARCHIVE_TOTAL=$(jq '[.runs[].jobs | length] | add' "$ARCHIVE_FILE")

log "  Pruned ${ZOMBIE_COUNT} zombie entries."
log "  Jobs file now:   ${POST_TOTAL} entries (${POST_ZOMBIES} zombies remaining)"
log "  Archive total:   ${ARCHIVE_TOTAL} entries"

if [[ "$POST_ZOMBIES" -ne 0 ]]; then
    echo "ERROR: post-prune zombie count is $POST_ZOMBIES (expected 0)" >&2
    exit 1
fi
