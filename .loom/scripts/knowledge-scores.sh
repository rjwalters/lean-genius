#!/bin/bash
# List problems by knowledge accumulation (lowest first)
# Usage: ./knowledge-scores.sh [--status STATUS] [--revisit]

STATUS_FILTER=""
REVISIT_MODE=false

while [[ $# -gt 0 ]]; do
  case $1 in
    --status)
      STATUS_FILTER="$2"
      shift 2
      ;;
    --revisit)
      REVISIT_MODE=true
      shift
      ;;
    *)
      shift
      ;;
  esac
done

echo "=== Problems by Knowledge Score ==="
echo "Score | Status      | Problem ID"
echo "------|-------------|------------"

for file in src/data/research/problems/*.json; do
  id=$(basename "$file" .json)

  # Get pool status
  pool_status=$(jq -r --arg id "$id" '.candidates[] | select(.id == $id) | .status // "unknown"' research/candidate-pool.json 2>/dev/null)

  # Skip if status filter provided and doesn't match
  if [ -n "$STATUS_FILTER" ] && [ "$pool_status" != "$STATUS_FILTER" ]; then
    continue
  fi

  # In revisit mode, only show surveyed/in-progress/skipped
  if [ "$REVISIT_MODE" = true ]; then
    case "$pool_status" in
      surveyed|in-progress|skipped) ;;
      *) continue ;;
    esac
  fi

  score=$(jq '[.knowledge.insights, .knowledge.builtItems, .knowledge.mathlibGaps, .knowledge.nextSteps] | map(length) | add' "$file" 2>/dev/null || echo 0)
  printf "%5s | %-11s | %s\n" "$score" "$pool_status" "$id"
done | sort -t'|' -k1 -n
