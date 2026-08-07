#!/bin/bash
#
# sync-token-registry.sh - Normalize a registry's ACCOUNT_TOKEN_FILE_* column
#                          to the EMAIL-DERIVED token filename convention.
#
# Under the claude-monitor migration (#41033/#41044/#41045) the token pool is
# named by an EMAIL-DERIVED stem, NOT a positional agent-N.token. The wrapper
# (scripts/agents/claude-wrapper.sh) bootstraps + selects tokens via loom
# 0.12.0's derive_token_filename (rjwalters/loom#3699): strip '.' and '-' from
# the email local-part, append '-<first-domain-label>', lowercase, drop unsafe
# chars, then '.token'. Examples:
#
#     alice@example.com             -> alice-example.token
#     a.b.carol@example.net         -> abcarol-example.token
#     dave@example.org              -> dave-example.token
#     agent-1@2amlogic.com          -> agent1-2amlogic.token
#     agent-2@2amlogic.com          -> agent2-2amlogic.token
#
# The wrapper's ranking.json consumer ("Strategy 0") joins ranking emails to
# on-disk tokens by this SAME derivation. If a registry's ACCOUNT_TOKEN_FILE_N
# names a file that doesn't match (e.g. the OLD agent-N.token positional name),
# the join finds nothing and silently falls through to round-robin, disabling
# claude-monitor balancing. This script keeps the column honest.
#
# What it does
# ------------
# For each account N in the target registry that declares ACCOUNT_TOKEN_FILE_N,
# it computes the canonical filename and rewrites the value if they differ:
#   - If ACCOUNT_EMAIL_N is present, the canonical name is the email-derived
#     stem ('<stem>.token'). This is the normal case and CORRECTS any stale /
#     deprecated agent-N.token value.
#   - If ACCOUNT_EMAIL_N is absent (nothing to derive from), the declared value
#     is preferred (left unchanged).
# It NEVER writes the deprecated positional agent-N.token name.
#
# Note: the claude-monitor PRIMARY source (~/.claude-monitor/accounts.env) is
# EMAIL + KEY only and declares NO ACCOUNT_TOKEN_FILE_* column by design -- the
# wrapper derives filenames from email. Running this against such a source is a
# no-op (nothing to sync). It is meant for a LEGACY registry (e.g. <repo>/.env)
# that still carries an ACCOUNT_TOKEN_FILE_* column.
#
# Why rewrite the column and not rename the token files?
#   The token pool is LIVE. The wrapper writes/globs the email-derived .token
#   files. Renaming those (or changing the wrapper) risks breaking the running
#   pool. The safe fix is to correct the registry's documentation column so it
#   describes reality. See issue #41051 (supersedes #38967).
#
# SECURITY
#   - Operates ONLY on ACCOUNT_TOKEN_FILE_N lines (filenames, never secrets).
#   - Never reads, prints, or modifies ACCOUNT_KEY_N values.
#   - The target file is gitignored and must never be committed. This script
#     edits it in place (with a timestamped .bak backup); it does not touch git.
#
# Source resolution (matches the wrapper's PRIMARY source):
#   1. $ENV_FILE if set in the environment (explicit override), else
#   2. ~/.claude-monitor/accounts.env (dir overridable via
#      LOOM_CLAUDE_MONITOR_DIR), else
#   3. legacy <repo>/.env.
#
# Usage:
#   ./scripts/agents/sync-token-registry.sh            # apply (writes the file)
#   ./scripts/agents/sync-token-registry.sh --dry-run  # preview, write nothing
#
# Exit codes:
#   0  applied (or dry-run completed / nothing to do)
#   2  usage / environment error
#

set -uo pipefail

REPO_ROOT="${REPO_ROOT:-$(cd "$(dirname "$0")/../.." && pwd)}"
DRY_RUN=false

# Resolve the claude-monitor PRIMARY source (loom monitor.claude_monitor_dir()).
if [[ -n "${LOOM_CLAUDE_MONITOR_DIR:-}" ]]; then
    _MONITOR_ACCTS="$LOOM_CLAUDE_MONITOR_DIR/accounts.env"
else
    _MONITOR_ACCTS="$HOME/.claude-monitor/accounts.env"
fi

# Source resolution: explicit $ENV_FILE wins, else claude-monitor primary, else
# legacy repo .env.
if [[ -n "${ENV_FILE:-}" ]]; then
    ENV_FILE="$ENV_FILE"
elif [[ -f "$_MONITOR_ACCTS" ]]; then
    ENV_FILE="$_MONITOR_ACCTS"
else
    ENV_FILE="$REPO_ROOT/.env"
fi

for arg in "$@"; do
    case "$arg" in
        --dry-run|-n) DRY_RUN=true ;;
        --help|-h)
            sed -n '2,68p' "$0" | sed 's/^# \{0,1\}//'
            exit 0
            ;;
        *)
            echo "Unknown option: $arg" >&2
            exit 2
            ;;
    esac
done

# loom 0.12.0 derive_token_filename (#3699): strip '.' and '-' from the email
# local-part, append '-<first-domain-label>', lowercase, drop unsafe chars.
# MUST match scripts/agents/claude-wrapper.sh (_bootstrap_derive_stem /
# _derive_token_stem) exactly.
derive_token_stem() {
    local _email="$1" _local _domain _label
    [[ "$_email" == *@* ]] || return 1
    _local="${_email%@*}"
    _domain="${_email#*@}"
    _label="${_domain%%.*}"
    [[ -n "$_local" && -n "$_label" ]] || return 1
    _local=$(printf '%s' "$_local" | tr -d '.-')
    printf '%s-%s' "$_local" "$_label" \
        | tr '[:upper:]' '[:lower:]' \
        | tr -cd 'a-z0-9._-'
}

# Strip surrounding quotes / whitespace from a value (NEVER a secret here).
_clean() {
    local _v="$1"
    _v="${_v%\"}"; _v="${_v#\"}"
    _v="${_v%\'}"; _v="${_v#\'}"
    printf '%s' "$_v" | tr -d '[:space:]'
}

if [[ ! -f "$ENV_FILE" ]]; then
    echo "[sync-token-registry] No account source at $ENV_FILE" >&2
    exit 2
fi

if ! grep -q '^ACCOUNT_TOKEN_FILE_[0-9]\+=' "$ENV_FILE" 2>/dev/null; then
    echo "[sync-token-registry] $ENV_FILE declares no ACCOUNT_TOKEN_FILE_* entries —" >&2
    echo "  nothing to sync. (Under claude-monitor, token filenames are email-derived;" >&2
    echo "  the accounts.env source carries EMAIL + KEY only, by design.)" >&2
    exit 0
fi

changes=0
tmp="$(mktemp)"
trap 'rm -f "$tmp"' EXIT

while IFS= read -r line || [[ -n "$line" ]]; do
    if [[ "$line" =~ ^ACCOUNT_TOKEN_FILE_([0-9]+)= ]]; then
        n="${BASH_REMATCH[1]}"
        cur="$(_clean "${line#*=}")"

        # Canonical name: email-derived when an ACCOUNT_EMAIL_N exists (the
        # normal case; corrects deprecated agent-N.token). Otherwise keep the
        # declared value (prefer it — nothing to derive from). Never agent-N.token.
        _email=$(_clean "$(grep -E "^ACCOUNT_EMAIL_${n}=" "$ENV_FILE" | head -1 | cut -d= -f2-)")
        want="$cur"
        if [[ -n "$_email" ]]; then
            _stem=$(derive_token_stem "$_email") || _stem=""
            if [[ -n "$_stem" ]]; then
                want="${_stem}.token"
            else
                echo "  warn  account $n ('$_email'): cannot derive; keeping '$cur'" >&2
            fi
        fi

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
    echo "[sync-token-registry] --dry-run: $changes entr(y/ies) would change; file left untouched."
    exit 0
fi

backup="${ENV_FILE}.bak-$(date +%Y%m%d%H%M%S)"
cp "$ENV_FILE" "$backup"
cp "$tmp" "$ENV_FILE"
echo "[sync-token-registry] Updated $changes ACCOUNT_TOKEN_FILE_* entr(y/ies)."
echo "[sync-token-registry] Backup written to $backup (also gitignored)."
echo "[sync-token-registry] Verify with: ./scripts/agents/check-token-registry.sh"
exit 0
