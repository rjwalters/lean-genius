#!/usr/bin/env bash
#
# update-stats.sh - Create completion signal files for daemon stats tracking
#
# Agents call this script after completing significant work. The daemon
# polls for these signal files and aggregates them into session_stats.
#
# Usage:
#   ./scripts/lean/update-stats.sh <stat_name> [identifier]
#
# Signal types:
#   stub-enhanced <erdos-number>    Erdős stub was enhanced
#   proof-submitted <problem-id>    Proof submitted to Aristotle
#   proof-integrated <problem-id>   Aristotle proof integrated
#   research-completed <problem-id> Research problem completed
#   problem-selected [identifier]   New problem selected by seeker
#   deployment [identifier]         Deployment completed
#
# Examples:
#   ./scripts/lean/update-stats.sh stub-enhanced 42
#   ./scripts/lean/update-stats.sh proof-submitted erdos-728
#   ./scripts/lean/update-stats.sh research-completed bounded-prime-gaps
#   ./scripts/lean/update-stats.sh problem-selected
#   ./scripts/lean/update-stats.sh deployment
#

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
COMPLETIONS_DIR="$REPO_ROOT/.loom/signals/completions"

usage() {
    cat <<EOF
Usage: $0 <stat_name> [identifier]

Create a completion signal file for daemon stats tracking.

Signal types:
  stub-enhanced <erdos-number>     Erdős stub was enhanced
  proof-submitted <problem-id>     Proof submitted to Aristotle
  proof-integrated <problem-id>    Aristotle proof integrated
  research-completed <problem-id>  Research problem completed
  problem-selected [identifier]    New problem selected by seeker
  deployment [identifier]          Deployment completed

Examples:
  $0 stub-enhanced 42
  $0 proof-submitted erdos-728
  $0 research-completed bounded-prime-gaps
  $0 problem-selected
  $0 deployment
EOF
}

# Validate signal type
validate_signal_type() {
    local signal_type="$1"
    case "$signal_type" in
        stub-enhanced|proof-submitted|proof-integrated|research-completed|problem-selected|deployment)
            return 0
            ;;
        *)
            echo "Error: Unknown signal type '$signal_type'" >&2
            echo "Valid types: stub-enhanced, proof-submitted, proof-integrated, research-completed, problem-selected, deployment" >&2
            return 1
            ;;
    esac
}

# Main
if [[ $# -lt 1 ]] || [[ "${1:-}" == "--help" ]] || [[ "${1:-}" == "-h" ]]; then
    usage
    exit 1
fi

signal_type="$1"
identifier="${2:-}"

validate_signal_type "$signal_type"

# Build signal filename
mkdir -p "$COMPLETIONS_DIR"
timestamp=$(date +%s)

if [[ -n "$identifier" ]]; then
    signal_file="$COMPLETIONS_DIR/${signal_type}-${identifier}-${timestamp}"
else
    signal_file="$COMPLETIONS_DIR/${signal_type}-${timestamp}"
fi

touch "$signal_file"
echo "Signal created: $(basename "$signal_file")"
