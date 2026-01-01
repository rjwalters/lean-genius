#!/bin/bash
# List problems by knowledge accumulation (lowest first)
# Usage: ./knowledge-scores.sh [--status STATUS]

STATUS_FILTER="$1"

echo "=== Problems by Knowledge Score ==="
echo "Score | Problem ID"
echo "------|------------"

for file in src/data/research/problems/*.json; do
  id=$(basename "$file" .json)

  # Skip if status filter provided and doesn't match
  if [ -n "$STATUS_FILTER" ]; then
    pool_status=$(jq -r --arg id "$id" '.candidates[] | select(.id == $id) | .status // "unknown"' research/candidate-pool.json 2>/dev/null)
    if [ "$pool_status" != "$STATUS_FILTER" ]; then
      continue
    fi
  fi

  score=$(jq '[.knowledge.insights, .knowledge.builtItems, .knowledge.mathlibGaps, .knowledge.nextSteps] | map(length) | add' "$file" 2>/dev/null || echo 0)
  printf "%5s | %s\n" "$score" "$id"
done | sort -t'|' -k1 -n
