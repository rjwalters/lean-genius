#!/bin/bash
#
# sync-token-registry.sh - Make the .env account registry honest.
#
# Rewrites every ACCOUNT_TOKEN_FILE_N value in .env to the real, positional
# token filename that scripts/agents/claude-wrapper.sh actually creates and
# reads: "agent-N.token" (the same N as the account's ACCOUNT_KEY_N /
# ACCOUNT_EMAIL_N). After running this, the registry's account -> token-file
# mapping matches what is on disk, and check-token-registry.sh passes.
#
# Why this and not a rename of the token files?
#   The token pool is LIVE. The wrapper bootstraps ACCOUNT_KEY_N into
#   agent-N.token and rotates by globbing "*.token". Renaming those files (or
#   changing the wrapper's naming) risks breaking the running pool. The safe
#   fix is to correct the *documentation* column so it describes reality.
#   See issue #38967.
#
# SECURITY
#   - Operates ONLY on the ACCOUNT_TOKEN_FILE_N lines (filenames, never secrets).
#   - Never reads, prints, or modifies ACCOUNT_KEY_N values.
#   - .env is gitignored and must never be committed. This script edits it in
#     place (with a timestamped .bak backup); it does not touch git.
#
# Usage:
#   ./scripts/agents/sync-token-registry.sh            # apply (writes .env)
#   ./scripts/agents/sync-token-registry.sh --dry-run  # preview, write nothing
#
# Exit codes:
#   0  applied (or dry-run completed)
#   2  usage / environment error
#

set -uo pipefail

REPO_ROOT="${REPO_ROOT:-$(cd "$(dirname "$0")/../.." && pwd)}"
ENV_FILE="${ENV_FILE:-$REPO_ROOT/.env}"
DRY_RUN=false

for arg in "$@"; do
    case "$arg" in
        --dry-run|-n) DRY_RUN=true ;;
        --help|-h)
            sed -n '2,33p' "$0" | sed 's/^# \{0,1\}//'
            exit 0
            ;;
        *)
            echo "Unknown option: $arg" >&2
            exit 2
            ;;
    esac
done

if [[ ! -f "$ENV_FILE" ]]; then
    echo "[sync-token-registry] No .env file at $ENV_FILE" >&2
    exit 2
fi

if ! grep -q '^ACCOUNT_TOKEN_FILE_[0-9]\+=' "$ENV_FILE" 2>/dev/null; then
    echo "[sync-token-registry] .env declares no ACCOUNT_TOKEN_FILE_* entries — nothing to do." >&2
    exit 0
fi

changes=0
tmp="$(mktemp)"
trap 'rm -f "$tmp"' EXIT

while IFS= read -r line || [[ -n "$line" ]]; do
    if [[ "$line" =~ ^ACCOUNT_TOKEN_FILE_([0-9]+)= ]]; then
        n="${BASH_REMATCH[1]}"
        want="agent-${n}.token"
        # Current value (strip quotes/space) for reporting — never a secret.
        cur="${line#*=}"
        cur="${cur%\"}"; cur="${cur#\"}"; cur="${cur%\'}"; cur="${cur#\'}"
        cur="$(printf '%s' "$cur" | tr -d '[:space:]')"
        if [[ "$cur" != "$want" ]]; then
            echo "  account $n: $cur -> $want"
            changes=$((changes + 1))
        fi
        printf 'ACCOUNT_TOKEN_FILE_%s=%s\n' "$n" "$want" >> "$tmp"
    else
        printf '%s\n' "$line" >> "$tmp"
    fi
done < "$ENV_FILE"

if [[ $changes -eq 0 ]]; then
    echo "[sync-token-registry] Registry already honest — no changes needed."
    exit 0
fi

if $DRY_RUN; then
    echo "[sync-token-registry] --dry-run: $changes entr(y/ies) would change; .env left untouched."
    exit 0
fi

backup="${ENV_FILE}.bak-$(date +%Y%m%d%H%M%S)"
cp "$ENV_FILE" "$backup"
cp "$tmp" "$ENV_FILE"
echo "[sync-token-registry] Updated $changes ACCOUNT_TOKEN_FILE_* entr(y/ies)."
echo "[sync-token-registry] Backup written to $backup (also gitignored)."
echo "[sync-token-registry] Verify with: ./scripts/agents/check-token-registry.sh"
exit 0
