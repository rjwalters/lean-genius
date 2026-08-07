#!/bin/bash
#
# check-token-registry.sh - Verify the account registry agrees with the
#                           actual token files in .loom/tokens/.
#
# Background
# ----------
# The Claude account pool is declared as numbered ACCOUNT_* entries. Under the
# claude-monitor migration (#41033/#41044/#41045) the PRIMARY source is
# ~/.claude-monitor/accounts.env, which carries EMAIL + KEY only:
#
#     ACCOUNT_EMAIL_N       account email  (e.g. alice@example.com)
#     ACCOUNT_KEY_N         the OAuth token value                    (SECRET)
#     ACCOUNT_TOKEN_FILE_N  OPTIONAL explicit token filename (legacy .env only)
#
# scripts/agents/claude-wrapper.sh bootstraps + selects tokens by an
# EMAIL-DERIVED stem (loom 0.12.0 derive_token_filename, rjwalters/loom#3699):
# strip '.' and '-' from the email local-part, append '-<first-domain-label>',
# lowercase, drop unsafe chars, then '.token'. Examples:
#
#     alice@example.com             -> alice-example.token
#     a.b.carol@example.net         -> abcarol-example.token
#     dave@example.org              -> dave-example.token
#     agent-1@2amlogic.com          -> agent1-2amlogic.token
#     agent-2@2amlogic.com          -> agent2-2amlogic.token
#
# The wrapper's ranking.json consumer ("Strategy 0", _derive_token_stem) joins
# ranking emails to on-disk tokens by the SAME derivation. If the canonical
# token file for an account is missing, the join silently falls through to
# round-robin -- disabling smart claude-monitor balancing with no error.
#
# This script makes that rot loud. For each account it computes the canonical
# token filename the wrapper actually uses -- the declared ACCOUNT_TOKEN_FILE_N
# if a source provides one, else the email-derived stem -- and FAILS (non-zero)
# when that file is missing under .loom/tokens/. The OLD positional convention
# (agent-N.token) is DEPRECATED: it is no longer emitted, and is flagged if a
# source still declares it. See issue #41051 (supersedes #38967).
#
# Source resolution (matches the wrapper's PRIMARY source):
#   1. $ENV_FILE if set in the environment (explicit override), else
#   2. ~/.claude-monitor/accounts.env (dir overridable via
#      LOOM_CLAUDE_MONITOR_DIR, mirroring loom monitor.claude_monitor_dir()),
#      else
#   3. legacy <repo>/.env.
#
# SECURITY: this script never reads, prints, or logs ACCOUNT_KEY_* values or
# token file contents. It only inspects emails, filenames, and existence.
#
# Usage:
#   ./scripts/agents/check-token-registry.sh          # human-readable report
#   ./scripts/agents/check-token-registry.sh --quiet  # only print on failure
#
# Exit codes:
#   0  every account's canonical token file exists (or no accounts declared)
#   1  one or more canonical token files are missing (registry is stale)
#   2  usage / environment error
#

set -uo pipefail

REPO_ROOT="${REPO_ROOT:-$(cd "$(dirname "$0")/../.." && pwd)}"
TOKENS_DIR="${TOKENS_DIR:-$REPO_ROOT/.loom/tokens}"
QUIET=false

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
        --quiet|-q) QUIET=true ;;
        --help|-h)
            sed -n '2,58p' "$0" | sed 's/^# \{0,1\}//'
            exit 0
            ;;
        *)
            echo "Unknown option: $arg" >&2
            exit 2
            ;;
    esac
done

say() { $QUIET || echo "$@"; }

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

if [[ ! -f "$ENV_FILE" ]]; then
    echo "[check-token-registry] No account source at $ENV_FILE — nothing to check." >&2
    # Absence of a source is not a failure (e.g. a fresh clone / CI without secrets).
    exit 0
fi

# Enumerate account indices from ANY declared ACCOUNT_(EMAIL|KEY|TOKEN_FILE)_N.
_indices=$(grep -oE '^ACCOUNT_(EMAIL|KEY|TOKEN_FILE)_[0-9]+=' "$ENV_FILE" 2>/dev/null \
    | sed -E 's/^ACCOUNT_(EMAIL|KEY|TOKEN_FILE)_([0-9]+)=/\2/' | sort -un)

if [[ -z "$_indices" ]]; then
    say "[check-token-registry] $ENV_FILE declares no ACCOUNT_* entries — nothing to check."
    exit 0
fi

# Strip surrounding quotes / whitespace from a value (NEVER a secret here).
_clean() {
    local _v="$1"
    _v="${_v%\"}"; _v="${_v#\"}"
    _v="${_v%\'}"; _v="${_v#\'}"
    printf '%s' "$_v" | tr -d '[:space:]'
}

missing=0
checked=0
declare -a referenced_basenames=()

for n in $_indices; do
    _email=$(_clean "$(grep -E "^ACCOUNT_EMAIL_${n}=" "$ENV_FILE" | head -1 | cut -d= -f2-)")
    _file=$(_clean "$(grep -E "^ACCOUNT_TOKEN_FILE_${n}=" "$ENV_FILE" | head -1 | cut -d= -f2-)")

    # Canonical filename the wrapper uses: prefer a declared ACCOUNT_TOKEN_FILE_N,
    # else derive from ACCOUNT_EMAIL_N. (Never agent-N.token.)
    if [[ -n "$_file" ]]; then
        _canon="$_file"
    elif [[ -n "$_email" ]]; then
        _stem=$(derive_token_stem "$_email") || _stem=""
        if [[ -z "$_stem" ]]; then
            echo "  MISS  account $n ('$_email'): cannot derive token filename" >&2
            missing=$((missing + 1))
            continue
        fi
        _canon="${_stem}.token"
    else
        # Neither a declared file nor an email: nothing resolvable for this index.
        continue
    fi

    # Flag the deprecated positional convention if a source still declares it.
    if [[ "$_canon" =~ ^agent-[0-9]+\.token$ ]]; then
        echo "  WARN  account $n -> $_canon  [deprecated positional name; expected email-derived stem]" >&2
    fi

    checked=$((checked + 1))
    if [[ "$_canon" = /* ]]; then
        resolved="$_canon"
    else
        resolved="$TOKENS_DIR/$_canon"
    fi
    referenced_basenames+=("$(basename "$resolved")")

    if [[ -f "$resolved" ]]; then
        say "  ok    account $n (${_email:-?}) -> $_canon"
    else
        echo "  MISS  account $n (${_email:-?}) -> $_canon  [no such file under .loom/tokens/]" >&2
        missing=$((missing + 1))
    fi
done

# Report token files on disk that no account points at (orphans). Informational
# only — the wrapper globs the directory, so extra files are still used.
if [[ -d "$TOKENS_DIR" ]]; then
    while IFS= read -r tok; do
        [[ -e "$tok" ]] || continue
        b="$(basename "$tok")"
        found=false
        for ref in "${referenced_basenames[@]:-}"; do
            [[ "$ref" == "$b" ]] && { found=true; break; }
        done
        $found || say "  note  $b exists on disk but no account references it"
    done < <(find "$TOKENS_DIR" -maxdepth 1 -name '*.token' 2>/dev/null | sort)
fi

if [[ $missing -gt 0 ]]; then
    echo "" >&2
    echo "[check-token-registry] FAIL: $missing of $checked account(s) resolve to a" >&2
    echo "  canonical token file that does not exist under $TOKENS_DIR." >&2
    echo "  The registry is stale, or the pool has not been bootstrapped." >&2
    echo "  Fix: re-run the wrapper to re-bootstrap the pool, or run" >&2
    echo "  scripts/agents/sync-token-registry.sh to normalize ACCOUNT_TOKEN_FILE_*" >&2
    echo "  to the email-derived convention." >&2
    exit 1
fi

say "[check-token-registry] OK: all $checked account(s) resolve to existing token files."
exit 0
