#!/bin/bash
#
# llm-map-file.sh - Use Claude to map a recovered Aristotle solution to its local proof file
#
# Usage:
#   ./llm-map-file.sh <recovered-file.lean>       # Map a single file
#   ./llm-map-file.sh --batch                      # Process all files in aristotle-results/new/
#   ./llm-map-file.sh --clear-cache                # Clear the mapping cache
#
# Output:
#   Prints a single filename (e.g., "DerangementsOQ02.lean") or "UNMAPPED"
#
# Requires: claude CLI tool
#

set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
PROJECT_ROOT="$(cd "$SCRIPT_DIR/../.." && pwd)"
PROOFS_DIR="$PROJECT_ROOT/proofs/Proofs"
CACHE_FILE="$PROJECT_ROOT/aristotle-results/llm-mapping-cache.json"
RESULTS_DIR="$PROJECT_ROOT/aristotle-results/new"

# Colors (only for --batch mode stderr output)
RED='\033[0;31m'
GREEN='\033[0;32m'
YELLOW='\033[1;33m'
CYAN='\033[0;36m'
NC='\033[0m'

# Cache expiry for UNMAPPED entries (7 days in seconds)
UNMAPPED_EXPIRY=$((7 * 24 * 60 * 60))

BATCH_MODE=false

# Initialize cache file if it doesn't exist
init_cache() {
    if [[ ! -f "$CACHE_FILE" ]]; then
        mkdir -p "$(dirname "$CACHE_FILE")"
        echo '{"version": 1, "mappings": {}}' > "$CACHE_FILE"
    fi
}

# Check cache for a file mapping
# Returns the cached target or empty string
check_cache() {
    local basename="$1"

    if [[ ! -f "$CACHE_FILE" ]]; then
        return
    fi

    local cached
    cached=$(jq -r --arg f "$basename" '.mappings[$f].target // empty' "$CACHE_FILE" 2>/dev/null) || true

    if [[ -z "$cached" ]]; then
        return
    fi

    # Check if UNMAPPED entries have expired
    if [[ "$cached" == "UNMAPPED" ]]; then
        local timestamp
        timestamp=$(jq -r --arg f "$basename" '.mappings[$f].timestamp // empty' "$CACHE_FILE" 2>/dev/null) || true
        if [[ -n "$timestamp" ]]; then
            local cached_epoch
            cached_epoch=$(date -j -f "%Y-%m-%dT%H:%M:%SZ" "$timestamp" "+%s" 2>/dev/null || date -d "$timestamp" "+%s" 2>/dev/null || echo 0)
            local now_epoch
            now_epoch=$(date "+%s")
            if (( now_epoch - cached_epoch > UNMAPPED_EXPIRY )); then
                # Expired, remove from cache
                local tmp
                tmp=$(mktemp)
                jq --arg f "$basename" 'del(.mappings[$f])' "$CACHE_FILE" > "$tmp" && mv "$tmp" "$CACHE_FILE"
                return
            fi
        fi
    fi

    echo "$cached"
}

# Write a mapping to the cache
write_cache() {
    local basename="$1"
    local target="$2"
    local reason="${3:-}"

    init_cache

    local now
    now=$(date -u +"%Y-%m-%dT%H:%M:%SZ")

    local tmp
    tmp=$(mktemp)
    jq --arg f "$basename" --arg t "$target" --arg ts "$now" --arg r "$reason" '
        .mappings[$f] = {
            target: $t,
            timestamp: $ts,
            reason: $r
        }
    ' "$CACHE_FILE" > "$tmp" && mv "$tmp" "$CACHE_FILE"
}

# Generate a compact proof file listing for the prompt
# Groups files by prefix to reduce token count (~39KB full -> ~8KB compact)
generate_file_listing() {
    ls "$PROOFS_DIR"/*.lean 2>/dev/null | xargs -I{} basename {} .lean | sort
}

# Map a single file using Claude
map_file() {
    local input_file="$1"
    local basename
    basename=$(basename "$input_file")

    # Check cache first
    local cached
    cached=$(check_cache "$basename")
    if [[ -n "$cached" ]]; then
        echo "$cached"
        return 0
    fi

    # Check that claude CLI is available
    if ! command -v claude &>/dev/null; then
        echo "UNMAPPED"
        return 1
    fi

    # Extract first 50 lines of the file for context (keep prompt compact)
    local file_excerpt
    file_excerpt=$(head -50 "$input_file" 2>/dev/null) || true

    if [[ -z "$file_excerpt" ]]; then
        write_cache "$basename" "UNMAPPED" "Empty file"
        echo "UNMAPPED"
        return 0
    fi

    # Generate proof file listing
    local file_listing
    file_listing=$(generate_file_listing)

    # Build the prompt in a temp file (too large for shell argument)
    local prompt_file
    prompt_file=$(mktemp "${TMPDIR:-/tmp}/aristotle-prompt-XXXXXX")
    cat > "$prompt_file" <<PROMPT_EOF
Match this recovered Lean 4 proof file to one of the filenames below.

NAMING CONVENTIONS:
- XOQ01.lean, XOQ02.lean = Open questions about theorem X (variant numbers)
- XAristotle.lean = Companion file submitted to Aristotle for proof search
- ErdosNNNProblem.lean = Erdos problem #NNN
- Names use PascalCase: AngleTrisection, BezoutIdentity, CentralLimitTheorem, etc.

AVAILABLE FILES (without .lean extension):
${file_listing}

RECOVERED FILE CONTENT (first 50 lines):
${file_excerpt}

Respond with ONLY the matching name (e.g., DerangementsOQ02) or UNMAPPED. No explanation.
PROMPT_EOF

    # Call Claude with TTY-safe pattern, piping prompt from file
    local tmpfile
    tmpfile=$(mktemp "${TMPDIR:-/tmp}/aristotle-llm-XXXXXX")

    timeout 120 claude -p "$(cat "$prompt_file")" --model sonnet --max-turns 1 < /dev/null > "$tmpfile" 2>/dev/null || {
        rm -f "$tmpfile" "$prompt_file"
        write_cache "$basename" "UNMAPPED" "Claude CLI call failed"
        echo "UNMAPPED"
        return 0
    }
    rm -f "$prompt_file"

    local result
    result=$(cat "$tmpfile" | tr -d '[:space:]' | sed 's/^`//;s/`$//')
    rm -f "$tmpfile"

    # Validate: must end in .lean and exist in proofs/Proofs/
    if [[ -z "$result" || "$result" == "UNMAPPED" ]]; then
        write_cache "$basename" "UNMAPPED" "Claude returned UNMAPPED"
        echo "UNMAPPED"
        return 0
    fi

    # Strip any path prefix if Claude included one
    result=$(basename "$result")

    # Ensure .lean extension
    if [[ "$result" != *.lean ]]; then
        result="${result}.lean"
    fi

    if [[ -f "$PROOFS_DIR/$result" ]]; then
        write_cache "$basename" "$result" "LLM matched"
        echo "$result"
    else
        write_cache "$basename" "UNMAPPED" "LLM suggested $result but file does not exist"
        echo "UNMAPPED"
    fi
}

# Batch mode: process all files in aristotle-results/new/
batch_mode() {
    init_cache

    local files
    files=$(ls "$RESULTS_DIR"/recovered-*.lean 2>/dev/null)

    if [[ -z "$files" ]]; then
        echo -e "${YELLOW}No recovered files to process${NC}" >&2
        return 0
    fi

    local total mapped unmapped cached_hits
    total=$(echo "$files" | wc -l | tr -d ' ')
    mapped=0
    unmapped=0
    cached_hits=0

    echo -e "${CYAN}Processing $total recovered files...${NC}" >&2

    while IFS= read -r f; do
        [[ -z "$f" ]] && continue
        local bn
        bn=$(basename "$f")

        local result
        result=$(map_file "$f")

        if [[ "$result" == "UNMAPPED" ]]; then
            ((++unmapped))
            echo -e "  ${YELLOW}UNMAPPED${NC}: $bn" >&2
        else
            ((++mapped))
            echo -e "  ${GREEN}MAPPED${NC}: $bn -> $result" >&2
        fi
    done <<< "$files"

    echo "" >&2
    echo -e "${GREEN}Mapped: $mapped${NC}" >&2
    echo -e "${YELLOW}Unmapped: $unmapped${NC}" >&2
}

# Main
main() {
    case "${1:-}" in
        --batch)
            BATCH_MODE=true
            batch_mode
            ;;
        --clear-cache)
            rm -f "$CACHE_FILE"
            echo "Cache cleared"
            ;;
        -h|--help)
            echo "Usage: $0 <recovered-file.lean> | --batch | --clear-cache"
            exit 0
            ;;
        "")
            echo "Usage: $0 <recovered-file.lean> | --batch | --clear-cache" >&2
            exit 1
            ;;
        *)
            if [[ ! -f "$1" ]]; then
                echo "File not found: $1" >&2
                echo "UNMAPPED"
                exit 1
            fi
            map_file "$1"
            ;;
    esac
}

main "$@"
