#!/usr/bin/env bash
# validate-data.sh - Check research data quality
# Usage: ./scripts/research/validate-data.sh [--strict]
# Exit code 0 = pass, 1 = fail (only in --strict mode)

set -euo pipefail

STRICT=false
[[ "${1:-}" == "--strict" ]] && STRICT=true

PROBLEMS_DIR="src/data/research/problems"
issues=0

# Check for navigation junk in formal statements
junk_count=$(python3 -c "
import json, glob
count = sum(1 for f in glob.glob('${PROBLEMS_DIR}/erdos-*.json')
            if 'Forum' in json.load(open(f)).get('problemStatement',{}).get('formal',''))
print(count)
")

if [[ "$junk_count" -gt 0 ]]; then
    echo "FAIL: $junk_count problems have navigation junk in formal statements"
    ((issues++))
else
    echo "PASS: No navigation junk in formal statements"
fi

# Check for placeholder text
placeholder_count=$(python3 -c "
import json, glob
count = sum(1 for f in glob.glob('${PROBLEMS_DIR}/erdos-*.json')
            if json.load(open(f)).get('problemStatement',{}).get('formal','') == '(LaTeX not available)')
print(count)
")

if [[ "$placeholder_count" -gt 0 ]]; then
    echo "WARN: $placeholder_count problems have '(LaTeX not available)' placeholder"
else
    echo "PASS: No placeholder formal statements"
fi

# Check for HTML entities in plain text
html_count=$(python3 -c "
import json, glob
count = sum(1 for f in glob.glob('${PROBLEMS_DIR}/erdos-*.json')
            if '&lt;' in json.load(open(f)).get('problemStatement',{}).get('plain','')
            or '&#x' in json.load(open(f)).get('problemStatement',{}).get('plain',''))
print(count)
")

if [[ "$html_count" -gt 0 ]]; then
    echo "WARN: $html_count problems have HTML entities in plain text"
else
    echo "PASS: No HTML entities in plain text"
fi

# Summary
echo ""
echo "=== Summary ==="
echo "Navigation junk: $junk_count (FAIL if > 0)"
echo "Placeholders: $placeholder_count (WARN)"
echo "HTML entities: $html_count (WARN)"

if [[ "$issues" -gt 0 ]] && $STRICT; then
    echo ""
    echo "STRICT MODE: $issues failures detected"
    exit 1
fi

exit 0
