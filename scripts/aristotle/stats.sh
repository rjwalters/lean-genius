#!/usr/bin/env bash
#
# Aristotle: real-success-rate stats from research/aristotle-jobs.json
#
# Excludes archived zombies (those live in research/aristotle-jobs-archive-zombies.json
# after running prune-zombies.sh).
#
# Usage:
#   ./scripts/aristotle/stats.sh              # Human-readable table
#   ./scripts/aristotle/stats.sh --oneline    # Single-line summary
#   ./scripts/aristotle/stats.sh --json       # Raw JSON
#
# Definitions:
#   total          = count of all .jobs[] (zombies should already be pruned)
#   active         = jobs with status == "submitted" (in-flight)
#   real_wins      = jobs with status == "integrated" AND theorems_proved > 0
#   noops          = jobs with status == "integrated" AND (theorems_proved == 0 or null)
#   theorems_total = sum of .theorems_proved across all integrated jobs
#   failed         = jobs with status == "failed"
#   ghost          = jobs with status == "ghost_completed"
#   build_failed   = jobs with status == "build_failed"
#   blocked        = jobs with status == "blocked"
#   terminal       = active + real_wins + noops + failed + ghost + build_failed + blocked
#                    + completed + resolved_manually
#   success_rate   = real_wins / (terminal - active)   (only computed when denom > 0)
#

set -euo pipefail

JOBS_FILE="research/aristotle-jobs.json"
MODE="table"

while [[ $# -gt 0 ]]; do
    case "$1" in
        --oneline) MODE="oneline"; shift;;
        --json)    MODE="json"; shift;;
        --table)   MODE="table"; shift;;
        --jobs)    JOBS_FILE="$2"; shift 2;;
        -h|--help)
            sed -n '2,28p' "$0" | sed 's/^# \{0,1\}//'
            exit 0;;
        *)
            echo "Unknown argument: $1" >&2
            exit 1;;
    esac
done

if ! command -v jq >/dev/null 2>&1; then
    echo "ERROR: jq is required but not installed." >&2
    exit 1
fi

if [[ ! -f "$JOBS_FILE" ]]; then
    echo "ERROR: jobs file not found: $JOBS_FILE" >&2
    exit 1
fi

# Compute all numbers in one jq pass for atomicity.
STATS_JSON=$(jq '
    .jobs as $j
    | {
        total:           ($j | length),
        active:          [$j[] | select(.status == "submitted")] | length,
        integrated:      [$j[] | select(.status == "integrated")] | length,
        real_wins:       [$j[] | select(.status == "integrated" and ((.theorems_proved // 0) > 0))] | length,
        noops:           [$j[] | select(.status == "integrated" and ((.theorems_proved // 0) == 0))] | length,
        theorems_total:  ([$j[] | select(.status == "integrated") | (.theorems_proved // 0)] | add // 0),
        failed:          [$j[] | select(.status == "failed")] | length,
        ghost:           [$j[] | select(.status == "ghost_completed")] | length,
        build_failed:    [$j[] | select(.status == "build_failed")] | length,
        blocked:         [$j[] | select(.status == "blocked")] | length,
        completed:       [$j[] | select(.status == "completed")] | length,
        resolved:        [$j[] | select(.status == "resolved_manually")] | length,
        zombies:         [$j[] | select(.status == "zombie")] | length,
        null_status:     [$j[] | select(.status == null)] | length
      }
    | . + {
        terminal: (.real_wins + .noops + .failed + .ghost + .build_failed + .blocked + .completed + .resolved),
        success_denom: (.real_wins + .noops + .failed + .ghost + .build_failed + .blocked + .completed + .resolved)
      }
    | . + {
        success_rate: (if .success_denom > 0 then (.real_wins / .success_denom) else 0 end)
      }
' "$JOBS_FILE")

case "$MODE" in
    json)
        echo "$STATS_JSON"
        exit 0
        ;;
    oneline)
        # Single-line format expected by launch.sh status.
        # Example: "real_wins=31 theorems=64 success_rate=18.7% (of 166 terminal)"
        printf '%s\n' "$(
            echo "$STATS_JSON" | jq -r '
                "real_wins=\(.real_wins) theorems=\(.theorems_total) success_rate=\((.success_rate * 1000 | round) / 10)% (of \(.success_denom) terminal)"
            '
        )"
        exit 0
        ;;
    table)
        echo "$STATS_JSON" | jq -r '
            "Aristotle stats (excluding archived zombies)",
            "─────────────────────────────────────────────",
            "Total jobs ever:           \(.total)",
            "  Active (submitted):      \(.active)",
            "  Real wins (proved > 0):  \(.real_wins)",
            "  No-ops (proved == 0):    \(.noops)",
            "  Completed (no theorems): \(.completed)",
            "  Resolved manually:       \(.resolved)",
            "",
            "Total theorems proved:     \(.theorems_total)",
            "",
            "Failure breakdown:",
            "  failed:                  \(.failed)",
            "  ghost_completed:         \(.ghost)",
            "  build_failed:            \(.build_failed)",
            "  blocked:                 \(.blocked)",
            "",
            "Terminal jobs (excludes active): \(.success_denom)",
            "Success rate (real_wins/terminal): \((.success_rate * 1000 | round) / 10)%",
            (if (.zombies // 0) > 0 then "\nWARNING: \(.zombies) zombie entries still in jobs file; run prune-zombies.sh" else empty end),
            (if (.null_status // 0) > 0 then "Note: \(.null_status) entries have null status" else empty end)
        '
        ;;
esac
