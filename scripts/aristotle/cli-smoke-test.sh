#!/usr/bin/env bash
#
# cli-smoke-test.sh - Smoke-test the Aristotle v2 CLI (aristotlelib >= 1.0).
#
# Replaces the retired mcp-smoke-test.sh (issue #38098). The MCP wrapper
# (septract/lean-aristotle-mcp) pinned aristotlelib ~=0.6.0 and broke when
# Harmonic cut over to the v1+ API server-side (HTTP 426 Upgrade Required,
# surfaced as "Resource not found"). There is no official MCP server for
# aristotlelib 2.x, so the working path is the CLI, wrapped by
# scripts/aristotle/{submit-batch,check-jobs,retrieve-integrate}.sh.
#
# What it does:
#   1. Resolves ARISTOTLE_API_KEY (from env or ~/.aristotle_key) — exits
#      non-zero with a clear message if neither is present.
#   2. Verifies uvx is installed.
#   3. Makes ONE read-only, quota-free API call: `aristotle list --limit 1`.
#      (Listing projects does not consume proof-search budget. This does NOT
#      call submit/continue/formalize, which DO consume quota.)
#   4. Exits 0 if the CLI authenticates and returns a well-formed listing.
#
# Usage:
#   ./scripts/aristotle/cli-smoke-test.sh
#   ARISTOTLE_API_KEY=sk-... ./scripts/aristotle/cli-smoke-test.sh
#
# Exit codes:
#   0 - CLI reachable and authenticated (list returned successfully)
#   1 - API key missing
#   2 - uvx / uv not installed
#   3 - CLI call failed (auth error, network, or unexpected output)

set -uo pipefail

# Colors (only emit when stdout is a tty)
if [[ -t 1 ]]; then
    RED='\033[0;31m'
    GREEN='\033[0;32m'
    YELLOW='\033[1;33m'
    NC='\033[0m'
else
    RED=''; GREEN=''; YELLOW=''; NC=''
fi

err() { echo -e "${RED}ERROR:${NC} $*" >&2; }
warn() { echo -e "${YELLOW}WARN:${NC} $*" >&2; }
ok() { echo -e "${GREEN}OK:${NC} $*"; }

# ----- Step 1: resolve API key -------------------------------------------

if [[ -z "${ARISTOTLE_API_KEY:-}" ]]; then
    if [[ -f "$HOME/.aristotle_key" ]]; then
        ARISTOTLE_API_KEY="$(cat "$HOME/.aristotle_key")"
        export ARISTOTLE_API_KEY
    else
        err "ARISTOTLE_API_KEY is not set and ~/.aristotle_key does not exist."
        echo "  To fix: export ARISTOTLE_API_KEY=sk-... or write your key to ~/.aristotle_key" >&2
        exit 1
    fi
fi

if [[ -z "${ARISTOTLE_API_KEY:-}" ]]; then
    err "ARISTOTLE_API_KEY resolved to an empty string."
    exit 1
fi

# ----- Step 2: verify uvx is installed -----------------------------------

if ! command -v uvx >/dev/null 2>&1; then
    err "uvx not found on PATH. Install uv from https://docs.astral.sh/uv/ (brew install uv)."
    exit 2
fi

# ----- Step 3: one read-only, quota-free CLI call ------------------------

echo "Running: uvx --from aristotlelib aristotle list --limit 1"
OUTPUT="$(uvx --from aristotlelib aristotle list --limit 1 2>&1)"
RC=$?

if [[ $RC -ne 0 ]]; then
    err "aristotle list exited $RC — CLI unreachable or unauthenticated."
    echo "--- output ---" >&2
    echo "$OUTPUT" | head -c 2048 >&2
    echo >&2
    exit 3
fi

# A well-formed listing has a header row containing the ID/STATUS columns.
# (An empty project list is still a success — the CLI authenticated.)
if echo "$OUTPUT" | grep -qiE 'ID[[:space:]]+CREATED|STATUS'; then
    ok "aristotle CLI reachable and authenticated (list returned a well-formed table)"
    # Show the first project row if present, for a quick human sanity check.
    FIRST=$(echo "$OUTPUT" | grep -E '^[0-9a-f]{8}-[0-9a-f]{4}-[0-9a-f]{4}-[0-9a-f]{4}-[0-9a-f]{12}' | head -n1 || true)
    if [[ -n "$FIRST" ]]; then
        echo "  Newest project: $FIRST"
    else
        echo "  (no projects listed — account has none, which is fine)"
    fi
    exit 0
fi

err "aristotle list returned unexpected output (no recognizable table header)."
echo "--- output ---" >&2
echo "$OUTPUT" | head -c 2048 >&2
echo >&2
exit 3
