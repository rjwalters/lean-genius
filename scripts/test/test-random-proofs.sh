#!/bin/bash
#
# test-random-proofs.sh - Run the random proof checker
#
# Tests N random proofs on the live site by clicking the dice button
# and verifying each proof page loads without errors.
#
# Usage:
#   ./scripts/test/test-random-proofs.sh           # Test 20 random proofs
#   ./scripts/test/test-random-proofs.sh --count 50 # Test 50 random proofs
#   ./scripts/test/test-random-proofs.sh --url http://localhost:5173  # Test local dev
#
# Exit codes:
#   0 - All proofs loaded successfully
#   1 - One or more proofs failed (issues filed)
#   2 - Script/infrastructure error

set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
REPO_ROOT="$(cd "$SCRIPT_DIR/../.." && pwd)"

# Colors
RED='\033[0;31m'
GREEN='\033[0;32m'
BLUE='\033[0;34m'
NC='\033[0m'

print_error() { echo -e "${RED}✗ $1${NC}"; }
print_success() { echo -e "${GREEN}✓ $1${NC}"; }
print_info() { echo -e "${BLUE}ℹ $1${NC}"; }

# Check dependencies
check_deps() {
    local missing=()
    command -v npx >/dev/null 2>&1 || missing+=("npx (install Node.js)")
    command -v gh >/dev/null 2>&1 || missing+=("gh (GitHub CLI)")

    if [[ ${#missing[@]} -gt 0 ]]; then
        print_error "Missing dependencies: ${missing[*]}"
        exit 2
    fi
}

# Ensure Playwright browsers are installed
ensure_browsers() {
    if ! npx playwright install --dry-run chromium >/dev/null 2>&1; then
        print_info "Installing Playwright Chromium browser..."
        npx playwright install chromium 2>&1 || {
            print_error "Failed to install Playwright browsers"
            exit 2
        }
        print_success "Playwright browsers installed"
    fi
}

# Main
main() {
    check_deps

    print_info "Ensuring Playwright browsers are available..."
    ensure_browsers

    print_info "Starting random proof checker..."
    echo ""

    cd "$REPO_ROOT"
    set +e
    npx tsx scripts/test/random-proof-checker.ts "$@"
    local exit_code=$?
    set -e

    echo ""
    if [[ $exit_code -eq 0 ]]; then
        print_success "All proofs loaded successfully"
    elif [[ $exit_code -eq 1 ]]; then
        print_error "Some proofs failed - issues filed on GitHub"
    else
        print_error "Script error (exit code: $exit_code)"
    fi

    return $exit_code
}

main "$@"
