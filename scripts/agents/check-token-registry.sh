#!/bin/bash
#
# check-token-registry.sh - Verify the .env account registry agrees with
#                           the actual token files in .loom/tokens/.
#
# Background
# ----------
# The Claude account pool is declared in .env as parallel triples:
#
#     ACCOUNT_EMAIL_N       human label for account N (e.g. robb@example.com)
#     ACCOUNT_KEY_N         the OAuth token value for account N   (SECRET)
#     ACCOUNT_TOKEN_FILE_N  the token filename the registry claims for account N
#
# But scripts/agents/claude-wrapper.sh bootstraps and rotates tokens
# POSITIONALLY: it materialises ACCOUNT_KEY_N into ".loom/tokens/agent-N.token"
# and selects by globbing "*.token". It never reads ACCOUNT_TOKEN_FILE_N.
#
# If ACCOUNT_TOKEN_FILE_N holds semantic names (robb-2amlogic.token, ...) that
# don't exist on disk, the registry's account -> token-file mapping is a dead
# column: anything that trusts it to locate a specific account's token gets a
# path that isn't there. See issue #38967.
#
# This script makes that rot loud instead of silent. It FAILS (non-zero exit)
# when any referenced ACCOUNT_TOKEN_FILE_N has no matching file under
# .loom/tokens/. Wire it into CI / a pre-flight lint so the columns can't
# drift apart again unnoticed.
#
# The honest, wrapper-consistent value for ACCOUNT_TOKEN_FILE_N is
# "agent-N.token" (see scripts/agents/sync-token-registry.sh to regenerate it).
#
# SECURITY: this script never reads, prints, or logs ACCOUNT_KEY_* values or
# token file contents. It only inspects filenames and existence.
#
# Usage:
#   ./scripts/agents/check-token-registry.sh          # human-readable report
#   ./scripts/agents/check-token-registry.sh --quiet  # only print on failure
#
# Exit codes:
#   0  every ACCOUNT_TOKEN_FILE_N resolves to an existing token file
#   1  one or more referenced token files are missing (registry is stale)
#   2  usage / environment error (no .env, no tokens dir, etc.)
#

set -uo pipefail

REPO_ROOT="${REPO_ROOT:-$(cd "$(dirname "$0")/../.." && pwd)}"
ENV_FILE="${ENV_FILE:-$REPO_ROOT/.env}"
TOKENS_DIR="${TOKENS_DIR:-$REPO_ROOT/.loom/tokens}"
QUIET=false

for arg in "$@"; do
    case "$arg" in
        --quiet|-q) QUIET=true ;;
        --help|-h)
            sed -n '2,45p' "$0" | sed 's/^# \{0,1\}//'
            exit 0
            ;;
        *)
            echo "Unknown option: $arg" >&2
            exit 2
            ;;
    esac
done

say() { $QUIET || echo "$@"; }

if [[ ! -f "$ENV_FILE" ]]; then
    echo "[check-token-registry] No .env file at $ENV_FILE — nothing to check." >&2
    # Absence of .env is not a failure (e.g. a fresh clone / CI without secrets).
    exit 0
fi

if ! grep -q '^ACCOUNT_TOKEN_FILE_[0-9]\+=' "$ENV_FILE" 2>/dev/null; then
    say "[check-token-registry] .env declares no ACCOUNT_TOKEN_FILE_* entries — nothing to check."
    exit 0
fi

missing=0
checked=0
declare -a referenced_basenames=()

# Read each ACCOUNT_TOKEN_FILE_N=value line. Values may be quoted and may be a
# bare basename or a path; we resolve bare names against $TOKENS_DIR.
while IFS='=' read -r key val; do
    n="${key#ACCOUNT_TOKEN_FILE_}"
    [[ "$n" =~ ^[0-9]+$ ]] || continue
    # Strip surrounding quotes / whitespace from the value (NOT a secret).
    val="${val%\"}"; val="${val#\"}"
    val="${val%\'}"; val="${val#\'}"
    val="$(printf '%s' "$val" | tr -d '[:space:]')"
    [[ -z "$val" ]] && continue

    checked=$((checked + 1))

    if [[ "$val" = /* ]]; then
        resolved="$val"
    else
        resolved="$TOKENS_DIR/$val"
    fi
    referenced_basenames+=("$(basename "$resolved")")

    if [[ -f "$resolved" ]]; then
        say "  ok    account $n -> $val"
    else
        echo "  MISS  account $n (ACCOUNT_EMAIL_$n) -> $val  [no such file under .loom/tokens/]" >&2
        missing=$((missing + 1))
    fi
done < <(grep '^ACCOUNT_TOKEN_FILE_[0-9]\+=' "$ENV_FILE")

# Report token files on disk that no registry entry points at (orphans). This
# is informational only and does not affect the exit code — the wrapper globs
# the directory, so extra files are used, they're just undocumented.
if [[ -d "$TOKENS_DIR" ]]; then
    while IFS= read -r tok; do
        [[ -e "$tok" ]] || continue
        b="$(basename "$tok")"
        found=false
        for ref in "${referenced_basenames[@]:-}"; do
            [[ "$ref" == "$b" ]] && { found=true; break; }
        done
        $found || say "  note  $b exists on disk but no ACCOUNT_TOKEN_FILE_* references it"
    done < <(find "$TOKENS_DIR" -maxdepth 1 -name '*.token' 2>/dev/null | sort)
fi

if [[ $missing -gt 0 ]]; then
    echo "" >&2
    echo "[check-token-registry] FAIL: $missing of $checked ACCOUNT_TOKEN_FILE_* entries" >&2
    echo "  point at token files that do not exist under $TOKENS_DIR." >&2
    echo "  The registry column is stale (see issue #38967)." >&2
    echo "  Fix: run scripts/agents/sync-token-registry.sh to regenerate the" >&2
    echo "  ACCOUNT_TOKEN_FILE_* values to the real positional agent-N.token names." >&2
    exit 1
fi

say "[check-token-registry] OK: all $checked ACCOUNT_TOKEN_FILE_* entries resolve to existing token files."
exit 0
