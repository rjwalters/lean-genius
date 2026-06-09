#!/bin/bash
#
# write-run-artifact.sh - Persist an Aristotle attempt's outputs as a research
# artifact under research/aristotle-runs/<slug>/<timestamp>/.
#
# This is the storage half of the "memory layer for the OODA loop" defined in
# issue #22628. The Aristotle wrapper calls this script after each attempt
# (success OR failure) on a Tier-3 target, so prior attempts remain inspectable
# by future runs and by the Researcher agent.
#
# Usage:
#   write-run-artifact.sh \
#       --slug <slug>             # e.g., fermat-defect-one
#       --tier <0|1|2|3>           # tier from find-candidates.sh
#       --status <success|failure|partial|skipped>
#       --transcript <path>        # full Aristotle output (will be copied)
#       [--final-state <path>]     # optional: proof state when the run ended
#       [--summary <text>]         # optional: one-paragraph human summary
#       [--config-json <path>]     # optional: extra config to merge into config.json
#
# Artifact directory layout:
#   research/aristotle-runs/<slug>/<YYYY-MM-DDTHH-MMZ>/
#     config.json          # tier, timeout, Aristotle version, slug, status
#     transcript.log       # full Aristotle output
#     final-state.lean     # proof state when the run ended (optional)
#     summary.md           # one-paragraph human-readable summary
#
# Notes:
#   - This is a thin storage helper. It does NOT submit anything to Aristotle.
#   - It is safe to call repeatedly; each invocation creates a new timestamp dir.
#   - The output of this script is the absolute path of the created artifact dir
#     (printed on stdout). Callers can pipe this into downstream tooling.
#
# Exit codes:
#   0 — artifact written successfully
#   1 — usage error (missing required flags)
#   2 — transcript not readable
#

set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
PROJECT_ROOT="$(cd "$SCRIPT_DIR/../.." && pwd)"
ARISTOTLE_RUNS_DIR="$PROJECT_ROOT/research/aristotle-runs"

SLUG=""
TIER=""
STATUS=""
TRANSCRIPT=""
FINAL_STATE=""
SUMMARY=""
CONFIG_JSON=""

usage() {
    sed -n '2,40p' "$0" | sed 's/^# \{0,1\}//'
    exit 1
}

while [[ $# -gt 0 ]]; do
    case "$1" in
        --slug) SLUG="$2"; shift 2 ;;
        --tier) TIER="$2"; shift 2 ;;
        --status) STATUS="$2"; shift 2 ;;
        --transcript) TRANSCRIPT="$2"; shift 2 ;;
        --final-state) FINAL_STATE="$2"; shift 2 ;;
        --summary) SUMMARY="$2"; shift 2 ;;
        --config-json) CONFIG_JSON="$2"; shift 2 ;;
        -h|--help) usage ;;
        *) echo "Unknown option: $1" >&2; usage ;;
    esac
done

[[ -z "$SLUG" ]] && { echo "ERROR: --slug is required" >&2; usage; }
[[ -z "$TIER" ]] && { echo "ERROR: --tier is required" >&2; usage; }
[[ -z "$STATUS" ]] && { echo "ERROR: --status is required" >&2; usage; }
[[ -z "$TRANSCRIPT" ]] && { echo "ERROR: --transcript is required" >&2; usage; }
[[ -r "$TRANSCRIPT" ]] || { echo "ERROR: transcript not readable: $TRANSCRIPT" >&2; exit 2; }

TIMESTAMP=$(date -u +'%Y-%m-%dT%H-%MZ')
ARTIFACT_DIR="$ARISTOTLE_RUNS_DIR/$SLUG/$TIMESTAMP"
mkdir -p "$ARTIFACT_DIR"

# Write config.json
ARISTOTLE_VERSION="${ARISTOTLE_VERSION:-unknown}"
TIMEOUT_HINT="${ARISTOTLE_TIMEOUT:-unset}"
cat > "$ARTIFACT_DIR/config.json" <<EOF
{
  "slug": "$SLUG",
  "tier": $TIER,
  "status": "$STATUS",
  "timestamp": "$(date -u +'%Y-%m-%dT%H:%M:%SZ')",
  "aristotleVersion": "$ARISTOTLE_VERSION",
  "timeoutHint": "$TIMEOUT_HINT"
}
EOF

# Merge in optional extra config (best-effort; falls back to bare config.json)
if [[ -n "$CONFIG_JSON" && -r "$CONFIG_JSON" ]]; then
    if command -v jq >/dev/null 2>&1; then
        jq -s '.[0] * .[1]' "$ARTIFACT_DIR/config.json" "$CONFIG_JSON" \
            > "$ARTIFACT_DIR/config.json.tmp" \
            && mv "$ARTIFACT_DIR/config.json.tmp" "$ARTIFACT_DIR/config.json"
    fi
fi

# Copy transcript (best-effort gzip if file is large)
cp "$TRANSCRIPT" "$ARTIFACT_DIR/transcript.log"

# Copy final-state if provided
if [[ -n "$FINAL_STATE" && -r "$FINAL_STATE" ]]; then
    cp "$FINAL_STATE" "$ARTIFACT_DIR/final-state.lean"
fi

# Write summary.md
SUMMARY_TEXT="${SUMMARY:-No summary provided. (Set --summary to record what was tried, what stuck, and what to try next.)}"
cat > "$ARTIFACT_DIR/summary.md" <<EOF
# Aristotle attempt — $SLUG — $TIMESTAMP

- **Slug**: $SLUG
- **Tier**: $TIER
- **Status**: $STATUS
- **Aristotle version**: $ARISTOTLE_VERSION

## Summary

$SUMMARY_TEXT

## Artifacts

- \`config.json\` — run configuration (tier, status, Aristotle version)
- \`transcript.log\` — full Aristotle output (stdout/stderr)
$(if [[ -f "$ARTIFACT_DIR/final-state.lean" ]]; then echo "- \`final-state.lean\` — proof state when the run ended"; fi)

EOF

# If the slug has a research/problems/<slug>/ directory, drop a stub claim file.
# This is the Aristotle <-> Researcher coupling described in #22628 section 5.
PROBLEM_DIR="$PROJECT_ROOT/research/problems/$SLUG"
if [[ -d "$PROBLEM_DIR" ]]; then
    CLAIMS_DIR="$PROBLEM_DIR/claims"
    mkdir -p "$CLAIMS_DIR"
    CLAIM_FILE="$CLAIMS_DIR/$(date -u +'%Y-%m-%d')-aristotle-${STATUS}-${TIMESTAMP}.md"
    cat > "$CLAIM_FILE" <<EOF
# Claim — Aristotle attempt $TIMESTAMP

- **Vector attempted**: \`aristotle-mcts\` (automated)
- **Date**: $(date -u +'%Y-%m-%d')
- **Status**: $STATUS

## What was tried

Aristotle MCTS proof search on Tier-3 target \`$SLUG\`.

## What happened

$STATUS — see \`research/aristotle-runs/$SLUG/$TIMESTAMP/\` for full transcript and config.

## What this suggests for next iteration

(Auto-generated stub; the Researcher agent should curate this when it picks up the slug next.)
EOF
fi

echo "$ARTIFACT_DIR"
