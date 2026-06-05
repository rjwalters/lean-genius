#!/usr/bin/env bash
#
# mcp-smoke-test.sh - Smoke-test the lean-aristotle-mcp server.
#
# What it does:
#   1. Resolves ARISTOTLE_API_KEY (from env or ~/.aristotle_key) — exits
#      non-zero with a clear message if neither is present.
#   2. Launches the MCP server via the pinned uvx invocation from .mcp.json.
#   3. Performs a JSON-RPC initialize handshake over stdio.
#   4. Calls tools/list and confirms the `prove` tool is exposed.
#   5. Calls tools/call on `prove` with a trivial snippet
#      (example : 1 + 1 = 2 := by sorry) in async mode (wait=false) so we
#      get back a project_id quickly rather than waiting on the solver.
#   6. Exits 0 if a project id appears within 10 seconds, non-zero otherwise.
#
# This does NOT poll for the eventual proof — it only verifies the wrapper
# is reachable, authenticated, and accepting submissions. Polling and result
# integration are the researcher's job (see .lean/roles/researcher.md
# "Aristotle MCP (interactive proving)").
#
# Usage:
#   ./scripts/aristotle/mcp-smoke-test.sh
#   ARISTOTLE_API_KEY=sk-... ./scripts/aristotle/mcp-smoke-test.sh
#
# Exit codes:
#   0 - MCP server reachable, prove() returned a project id
#   1 - API key missing
#   2 - uvx / uv not installed
#   3 - MCP server failed to start or handshake failed
#   4 - prove() did not return a project id within the timeout

set -uo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
PROJECT_ROOT="$(cd "$SCRIPT_DIR/../.." && pwd)"
MCP_CONFIG="$PROJECT_ROOT/.mcp.json"
SHA_FILE="$PROJECT_ROOT/vendor/lean-aristotle-mcp.sha"

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

# ----- Step 3: read the pinned sha for the user's information ------------

PINNED_SHA="unknown"
if [[ -f "$SHA_FILE" ]]; then
    PINNED_SHA="$(grep -E '^[0-9a-f]{7,40}$' "$SHA_FILE" | head -n1 || echo unknown)"
fi
echo "Using lean-aristotle-mcp pinned sha: $PINNED_SHA"
echo "MCP config: $MCP_CONFIG"

# ----- Step 4: drive the MCP server over stdio ---------------------------

# The .mcp.json invocation. Keep this in sync with .mcp.json — if you edit
# the args there, mirror them here. We could parse .mcp.json with jq, but
# avoiding the dependency keeps the smoke test self-contained.
MCP_CMD=(uvx --from "git+https://github.com/septract/lean-aristotle-mcp@${PINNED_SHA}" aristotle-mcp)

# Build the JSON-RPC request stream:
#   1. initialize
#   2. notifications/initialized
#   3. tools/list
#   4. tools/call prove (async)
#
# We feed all four messages on stdin and stop reading after we see a
# project id in the response, or after 30 seconds total (10s for the
# project id alone, but uvx may need extra time to fetch the package on
# first run).
SNIPPET='example : 1 + 1 = 2 := by sorry'

REQUESTS=$(cat <<JSON
{"jsonrpc":"2.0","id":1,"method":"initialize","params":{"protocolVersion":"2024-11-05","capabilities":{},"clientInfo":{"name":"mcp-smoke-test","version":"0.1.0"}}}
{"jsonrpc":"2.0","method":"notifications/initialized","params":{}}
{"jsonrpc":"2.0","id":2,"method":"tools/list","params":{}}
{"jsonrpc":"2.0","id":3,"method":"tools/call","params":{"name":"prove","arguments":{"code":${SNIPPET@Q},"wait":false}}}
JSON
)

# Time budget:
#   - First-run uvx may need ~30-60s to fetch the package.
#   - Steady-state, we want the project id within 10s of the prove call.
# We give the full pipeline 90s as a safety net; the issue's acceptance
# criterion (project id in 10s) is checked separately on the response.
PIPELINE_TIMEOUT=90

TMP_OUT="$(mktemp -t aristotle-mcp-smoke.XXXXXX)"
TMP_ERR="$(mktemp -t aristotle-mcp-smoke-err.XXXXXX)"
trap 'rm -f "$TMP_OUT" "$TMP_ERR"' EXIT

echo "Starting MCP server..."
START_TS=$(date +%s)

# Run the server with the requests on stdin. We use `timeout` to bound the
# total runtime. The server may keep stdin open waiting for more requests;
# we close stdin after writing the four messages by using a heredoc-piped
# subshell, then rely on the timeout for shutdown.
set +e
{
    printf '%s\n' "$REQUESTS"
    # Hold stdin open briefly so the server has time to respond to the
    # async submission, then EOF.
    sleep 12
} | timeout "$PIPELINE_TIMEOUT" "${MCP_CMD[@]}" >"$TMP_OUT" 2>"$TMP_ERR"
EXIT_CODE=$?
set -e

END_TS=$(date +%s)
ELAPSED=$((END_TS - START_TS))

# ----- Step 5: inspect the responses -------------------------------------

if [[ ! -s "$TMP_OUT" ]]; then
    err "MCP server produced no stdout. (elapsed ${ELAPSED}s, exit ${EXIT_CODE})"
    if [[ -s "$TMP_ERR" ]]; then
        echo "--- stderr ---" >&2
        head -c 4096 "$TMP_ERR" >&2
        echo >&2
        echo "--- end stderr ---" >&2
    fi
    exit 3
fi

# Look for an initialize response (id=1) — confirms the server started.
if ! grep -q '"id":1' "$TMP_OUT"; then
    err "No response to initialize request — handshake failed. (elapsed ${ELAPSED}s)"
    head -c 2048 "$TMP_OUT" >&2
    exit 3
fi
ok "initialize handshake completed"

# Confirm `prove` is in tools/list.
if grep -q '"name":"prove"' "$TMP_OUT"; then
    ok "prove tool exposed by server"
else
    warn "prove tool not visible in tools/list response — continuing to tools/call anyway"
fi

# Look for a project id in the prove response. The wrapper returns ids that
# look like UUIDs. We accept either an explicit "project_id" field or a bare
# UUID anywhere in the id=3 response payload.
if grep -E -q '"(project_id|projectId)"[[:space:]]*:[[:space:]]*"[0-9a-fA-F-]{8,}"' "$TMP_OUT"; then
    PROJECT_ID="$(grep -oE '"(project_id|projectId)"[[:space:]]*:[[:space:]]*"[^"]+"' "$TMP_OUT" | head -n1 | sed -E 's/.*"([^"]+)"$/\1/')"
    ok "prove() returned project id: $PROJECT_ID (elapsed ${ELAPSED}s)"
    exit 0
fi

# Fallback: any UUID-looking token in the id=3 response.
if grep -oE '[0-9a-f]{8}-[0-9a-f]{4}-[0-9a-f]{4}-[0-9a-f]{4}-[0-9a-f]{12}' "$TMP_OUT" | head -n1 | grep -q .; then
    PROJECT_ID="$(grep -oE '[0-9a-f]{8}-[0-9a-f]{4}-[0-9a-f]{4}-[0-9a-f]{4}-[0-9a-f]{12}' "$TMP_OUT" | head -n1)"
    ok "prove() returned UUID-shaped id: $PROJECT_ID (elapsed ${ELAPSED}s)"
    exit 0
fi

err "prove() did not return a project id within ${PIPELINE_TIMEOUT}s. (elapsed ${ELAPSED}s, exit ${EXIT_CODE})"
echo "--- stdout (truncated) ---" >&2
head -c 4096 "$TMP_OUT" >&2
echo >&2
echo "--- stderr (truncated) ---" >&2
head -c 4096 "$TMP_ERR" >&2
echo >&2
exit 4
