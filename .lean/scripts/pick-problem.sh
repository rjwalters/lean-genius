#!/bin/bash
#
# Random problem selection from candidate pool
#
# Usage:
#   ./pick-problem.sh           # Random selection
#   ./pick-problem.sh --list    # Show all candidates
#   ./pick-problem.sh --add     # Interactive add (TODO)
#

set -e

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
REPO_ROOT="$(cd "$SCRIPT_DIR/../.." && pwd)"
POOL_FILE="$REPO_ROOT/research/candidate-pool.json"

# Colors
GREEN='\033[0;32m'
YELLOW='\033[1;33m'
BLUE='\033[0;34m'
NC='\033[0m'

# Initialize pool if doesn't exist
init_pool() {
    if [ ! -f "$POOL_FILE" ]; then
        cat > "$POOL_FILE" << 'EOF'
{
  "version": "1.0",
  "last_updated": "",
  "candidates": [
    {
      "id": "bounded-prime-gaps",
      "name": "Bounded Prime Gaps (Zhang/Polymath)",
      "tier": "A",
      "significance": 9,
      "tractability": 3,
      "status": "available",
      "notes": "First Lean formalization of 2013 breakthrough. Gaps < 246.",
      "tags": ["number-theory", "primes", "formalization"]
    },
    {
      "id": "weak-goldbach",
      "name": "Weak Goldbach Conjecture (Helfgott)",
      "tier": "A",
      "significance": 8,
      "tractability": 3,
      "status": "available",
      "notes": "Every odd n > 5 is sum of 3 primes. Proved 2013.",
      "tags": ["number-theory", "primes", "formalization"]
    },
    {
      "id": "szemeredi-theorem",
      "name": "Szemerédi's Theorem",
      "tier": "A",
      "significance": 8,
      "tractability": 4,
      "status": "available",
      "notes": "Dense sets contain arbitrary length AP. Fundamental.",
      "tags": ["combinatorics", "additive", "formalization"]
    },
    {
      "id": "twin-prime-special",
      "name": "Twin Primes in Special Forms",
      "tier": "B",
      "significance": 8,
      "tractability": 4,
      "status": "available",
      "notes": "Prove twin prime existence for specific residue classes.",
      "tags": ["number-theory", "primes", "partial-progress"]
    },
    {
      "id": "collatz-structured",
      "name": "Collatz for Structured Starting Values",
      "tier": "B",
      "significance": 6,
      "tractability": 5,
      "status": "available",
      "notes": "Prove Collatz for 2^n-1, Mersenne numbers, etc.",
      "tags": ["number-theory", "dynamics", "partial-progress"]
    },
    {
      "id": "pnp-barriers",
      "name": "P≠NP Barrier Formalization",
      "tier": "B",
      "significance": 8,
      "tractability": 4,
      "status": "available",
      "notes": "Formalize relativization, natural proofs barriers.",
      "tags": ["complexity", "impossibility", "formalization"]
    },
    {
      "id": "prime-gaps-explicit",
      "name": "Explicit Prime Gap Bounds",
      "tier": "B",
      "significance": 7,
      "tractability": 5,
      "status": "available",
      "notes": "Improve Dusart-type explicit bounds.",
      "tags": ["number-theory", "primes", "bounds"]
    },
    {
      "id": "2d-navier-stokes",
      "name": "2D Navier-Stokes Regularity",
      "tier": "A",
      "significance": 8,
      "tractability": 4,
      "status": "available",
      "notes": "Known result. Major formalization for Millennium context.",
      "tags": ["analysis", "pde", "formalization"]
    },
    {
      "id": "rh-consequences",
      "name": "Riemann Hypothesis Consequences",
      "tier": "B",
      "significance": 8,
      "tractability": 5,
      "status": "available",
      "notes": "Formalize theorems conditional on RH.",
      "tags": ["number-theory", "analytic", "conditional"]
    },
    {
      "id": "legendre-partial",
      "name": "Legendre Conjecture Partial",
      "tier": "B",
      "significance": 7,
      "tractability": 3,
      "status": "available",
      "notes": "Prime between n² and (n+1)² for specific n ranges.",
      "tags": ["number-theory", "primes", "partial-progress"]
    }
  ]
}
EOF
        echo -e "${GREEN}Initialized candidate pool${NC}"
    fi
}

# List all candidates
list_candidates() {
    init_pool
    echo -e "${BLUE}Research Candidate Pool${NC}"
    echo "========================"
    echo ""
    jq -r '.candidates[] | select(.status == "available") | 
        "[\(.tier)] \(.id)\n    \(.name)\n    Sig: \(.significance)/10, Tract: \(.tractability)/10\n    \(.notes)\n"' \
        "$POOL_FILE"
}

# Pick random available candidate
pick_random() {
    init_pool
    
    # Get available candidates
    local count=$(jq '[.candidates[] | select(.status == "available")] | length' "$POOL_FILE")
    
    if [ "$count" -eq 0 ]; then
        echo -e "${YELLOW}No available candidates in pool!${NC}"
        exit 1
    fi
    
    # Random index
    local idx=$(jot -r 1 0 $((count - 1)))
    
    # Get the candidate
    local candidate=$(jq -r "[.candidates[] | select(.status == \"available\")][$idx]" "$POOL_FILE")
    local id=$(echo "$candidate" | jq -r '.id')
    local name=$(echo "$candidate" | jq -r '.name')
    local tier=$(echo "$candidate" | jq -r '.tier')
    local sig=$(echo "$candidate" | jq -r '.significance')
    local tract=$(echo "$candidate" | jq -r '.tractability')
    local notes=$(echo "$candidate" | jq -r '.notes')
    
    echo -e "${GREEN}🎲 Random Selection:${NC}"
    echo ""
    echo -e "  ${BLUE}$name${NC}"
    echo "  ID: $id"
    echo "  Tier: $tier"
    echo "  Significance: $sig/10"
    echo "  Tractability: $tract/10"
    echo "  Notes: $notes"
    echo ""
    echo -e "${YELLOW}To start research:${NC}"
    echo "  ./.lean/scripts/research.sh init $id"
}

# Mark candidate as in-progress
mark_in_progress() {
    local id="$1"
    init_pool
    
    local tmp=$(mktemp)
    jq --arg id "$id" \
        '(.candidates[] | select(.id == $id)) |= . + {"status": "in-progress"}' \
        "$POOL_FILE" > "$tmp" && mv "$tmp" "$POOL_FILE"
    
    echo -e "${GREEN}Marked '$id' as in-progress${NC}"
}

# Mark candidate as completed
mark_completed() {
    local id="$1"
    local result="$2"  # success, partial, blocked
    init_pool
    
    local tmp=$(mktemp)
    jq --arg id "$id" --arg result "$result" \
        '(.candidates[] | select(.id == $id)) |= . + {"status": "completed", "result": $result}' \
        "$POOL_FILE" > "$tmp" && mv "$tmp" "$POOL_FILE"
    
    echo -e "${GREEN}Marked '$id' as completed ($result)${NC}"
}

case "${1:-random}" in
    --list|-l)
        list_candidates
        ;;
    --pick|random|"")
        pick_random
        ;;
    --start)
        mark_in_progress "$2"
        ;;
    --complete)
        mark_completed "$2" "${3:-success}"
        ;;
    --help|-h)
        echo "Usage: ./pick-problem.sh [command]"
        echo ""
        echo "Commands:"
        echo "  (none), --pick    Random selection from pool"
        echo "  --list, -l        Show all available candidates"
        echo "  --start <id>      Mark candidate as in-progress"
        echo "  --complete <id>   Mark as completed"
        echo "  --help, -h        Show this help"
        ;;
    *)
        echo "Unknown command: $1"
        exit 1
        ;;
esac
