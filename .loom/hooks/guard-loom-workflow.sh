#!/usr/bin/env bash
# guard-loom-workflow.sh - PreToolUse hook for Loom-workflow-specific Bash guards
#
# Claude Code PreToolUse hook that intercepts Bash commands before execution.
# Receives JSON on stdin with tool_input.command and cwd fields.
#
# This hook carries ONLY the two Loom-workflow-specific guards that were
# extracted from guard-destructive.sh (issue #3604):
#
#   1. LOOM: Prefer merge-pr.sh over 'gh pr merge'
#   2. LOOM: Block 'pip install -e' inside worktrees (issue #2495)
#
# The generic repository-hygiene guards (catastrophic denies, SQL/cloud toggles,
# ASK patterns) live in guard-destructive.sh and are being migrated toward Repo
# Skills (rjwalters/repo#13). This file stays Loom-owned because both guards are
# specific to the Loom worktree/merge workflow.
#
# IMPORTANT: This hook only fires when Claude Code is invoked with:
#   --dangerously-skip-permissions  ← hooks FIRE (used by Loom agents)
#
# It does NOT fire with:
#   --permission-mode bypassPermissions  ← hooks SKIPPED entirely
#
# Output format (Claude Code hooks spec):
#   { "hookSpecificOutput": { "hookEventName": "PreToolUse", "permissionDecision": "deny|ask", "permissionDecisionReason": "..." } }
#
# NOTE: The "hookEventName": "PreToolUse" field is REQUIRED by Claude Code's
# PreToolUse hook schema. Without it, Claude Code silently discards the
# decision and the guard becomes inert (see issue #3550).
#
# Error handling: This script MUST never exit with a non-zero code or produce
# invalid output. Any internal error is caught by the trap, logged for
# diagnostics, and results in an "allow" decision to prevent infinite retry
# loops in Claude Code.

# Determine log directory relative to this script's location
SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd 2>/dev/null || echo ".")"
HOOK_ERROR_LOG="${SCRIPT_DIR}/../logs/hook-errors.log"

# Log a diagnostic error message (best-effort, never fails the script)
log_hook_error() {
    local msg="$1"
    # Ensure log directory exists
    mkdir -p "$(dirname "$HOOK_ERROR_LOG")" 2>/dev/null || true
    echo "[$(date -u '+%Y-%m-%dT%H:%M:%SZ')] [guard-loom-workflow] $msg" >> "$HOOK_ERROR_LOG" 2>/dev/null || true
}

# Top-level error trap: on ANY unexpected error, output valid JSON "allow"
# and log the failure for debugging. This prevents Claude Code from showing
# "PreToolUse:Bash hook error" which causes infinite retry loops.
trap 'log_hook_error "Unexpected error on line ${LINENO}: ${BASH_COMMAND:-unknown} (exit=$?)"; exit 0' ERR

# Read stdin safely — if cat or jq fails, the ERR trap fires and we allow
INPUT=$(cat 2>/dev/null) || INPUT=""

# Verify jq is available before attempting to parse
if ! command -v jq &>/dev/null; then
    log_hook_error "jq not found in PATH — allowing command (cannot parse input)"
    exit 0
fi

COMMAND=$(echo "$INPUT" | jq -r '.tool_input.command // empty' 2>/dev/null) || COMMAND=""
CWD=$(echo "$INPUT" | jq -r '.cwd // empty' 2>/dev/null) || CWD=""

# If no command to check, allow
if [[ -z "$COMMAND" ]]; then
    exit 0
fi

# Resolve repo root from cwd (handles worktree paths safely)
REPO_ROOT=""
if [[ -n "$CWD" ]] && [[ -d "$CWD" ]]; then
    REPO_ROOT=$(git -C "$CWD" rev-parse --show-toplevel 2>/dev/null || true)
elif [[ -n "$CWD" ]]; then
    # CWD doesn't exist (e.g., deleted worktree) — log but continue without repo root
    log_hook_error "cwd does not exist: $CWD — skipping repo root resolution"
fi

# Helper: output a deny decision and exit
deny() {
    local reason="$1"
    if jq -n --arg reason "$reason" '{
        hookSpecificOutput: {
            hookEventName: "PreToolUse",
            permissionDecision: "deny",
            permissionDecisionReason: $reason
        }
    }' 2>/dev/null; then
        exit 0
    fi
    # jq failed — emit raw JSON as fallback
    local escaped_reason
    escaped_reason=$(echo "$reason" | sed 's/\\/\\\\/g; s/"/\\"/g; s/\t/\\t/g; s/\n/\\n/g')
    echo "{\"hookSpecificOutput\":{\"hookEventName\":\"PreToolUse\",\"permissionDecision\":\"deny\",\"permissionDecisionReason\":\"${escaped_reason}\"}}"
    exit 0
}

# Helper: output an ask decision and exit
ask() {
    local reason="$1"
    if jq -n --arg reason "$reason" '{
        hookSpecificOutput: {
            hookEventName: "PreToolUse",
            permissionDecision: "ask",
            permissionDecisionReason: $reason
        }
    }' 2>/dev/null; then
        exit 0
    fi
    # jq failed — emit raw JSON as fallback
    local escaped_reason
    escaped_reason=$(echo "$reason" | sed 's/\\/\\\\/g; s/"/\\"/g; s/\t/\\t/g; s/\n/\\n/g')
    echo "{\"hookSpecificOutput\":{\"hookEventName\":\"PreToolUse\",\"permissionDecision\":\"ask\",\"permissionDecisionReason\":\"${escaped_reason}\"}}"
    exit 0
}

# =============================================================================
# LOOM: Prefer merge-pr.sh over gh pr merge (issue #43639)
#
# Detects a genuine `gh pr merge` INVOCATION -- the phrase anchored at a
# command position (start of the command string, or immediately after one of
# the shell command separators ; & && | || $( or a literal newline) -- not a
# bare substring match anywhere in the command text. The original
# `grep -qE 'gh\s+pr\s+merge'` matched the phrase ANYWHERE in the command
# string, so it false-positived on read-only commands that merely MENTION the
# phrase, e.g.:
#   grep -n "auto|graphql|gh pr merge|gh api" ./.loom/scripts/merge-pr.sh
#   echo "=== hook gh pr merge block ==="; gh api 'search/issues?...'
# Both of those are read-only / unrelated to merging and must pass through
# unblocked; only an actual `gh pr merge ...` invocation should deny.
#
# gh_pr_merge_invocation() runs two passes:
#
#   1. mask_heredocs(): a line-oriented pre-pass that blanks out heredoc
#      BODY lines (e.g. `git commit -m "$(cat <<'EOF' ... EOF)"`, used
#      constantly for commit messages / PR bodies). Without this, a commit
#      message that merely prose-mentions "gh pr merge" would itself get
#      denied, since heredoc body text is otherwise indistinguishable from
#      real command lines to the per-line scan below (#43639 follow-up: this
#      was caught by the fix's own commit message during testing). A heredoc
#      whose delimiter is quoted (<<'EOF'/<<"EOF") never expands $(...) or
#      backticks, so its body is unconditionally inert; an UNQUOTED
#      delimiter (<<EOF) still expands substitutions, so a body line
#      containing $( or a backtick is left in place (not blanked) so a
#      smuggled `<<EOF` \n `$(gh pr merge 1)` \n `EOF` is still caught below.
#
#   2. check(), run per remaining line: a quote-aware command-position
#      scanner (mirrors the qsplit() quote-tracking approach used for the
#      same class of bug in guard-destructive.sh, #3755/#71). Each input
#      line is its own scan (awk's default per-record split on \n already
#      gives "start of a new line = a command position", which covers plain
#      multi-line commands); within a line it walks character by character,
#      tracking whether the current position is a command position (start of
#      line, or right after ; & && | || $() and whether it is inside a
#      quoted span. A quoted span with no $( or backtick inside is INERT --
#      its contents (including any literal "gh pr merge" text used as a grep
#      pattern or echo label) are skipped entirely and never checked. Only
#      text sitting at an actual command position is tested against
#      ^gh[ \t]+pr[ \t]+merge<boundary>. A quoted span that DOES carry a $(
#      or backtick is walked char-by-char with separators kept active, so a
#      merge smuggled inside command substitution (e.g.
#      `echo "$(gh pr merge 1)"`) is still caught. Best-effort/fail-safe: an
#      unterminated quote treats the remainder as inert text (never
#      escalates a parse failure into a spurious deny).
# =============================================================================

gh_pr_merge_invocation() {
    # Args: <command string>. Echoes "1" if a genuine `gh pr merge` invocation
    # is found at a command position, "0" otherwise. Portable awk only.
    printf '%s' "$1" | awk '
    # Blank heredoc body lines so they cannot manufacture a phantom match or
    # a phantom command-position boundary in the per-line scan below.
    BEGIN {
        SQ = sprintf("%c", 39)
        DQ = sprintf("%c", 34)
        in_hd = 0
        delim = ""
        quoted = 0
    }
    {
        line = $0
        if (!in_hd) {
            idx = index(line, "<<")
            if (idx > 0) {
                rest = substr(line, idx + 2)
                sub(/^-/, "", rest)          # <<- (tab-stripping variant)
                sub(/^[ \t]+/, "", rest)
                if (substr(rest, 1, 1) == DQ || substr(rest, 1, 1) == SQ) {
                    q = substr(rest, 1, 1)
                    rest2 = substr(rest, 2)
                    ci = index(rest2, q)
                    if (ci > 0) {
                        delim = substr(rest2, 1, ci - 1)
                        quoted = 1
                        in_hd = (delim != "")
                    }
                } else if (match(rest, /^[A-Za-z_][A-Za-z0-9_]*/)) {
                    delim = substr(rest, 1, RLENGTH)
                    quoted = 0
                    in_hd = 1
                }
            }
            print line
            next
        }
        check_line = line
        sub(/^[ \t]+/, "", check_line)
        if (check_line == delim) {
            in_hd = 0
            print line
            next
        }
        if (!quoted && (index(line, "$(") > 0 || index(line, "`") > 0)) {
            print line
        } else {
            print ""
        }
    }
    ' | awk '
    function check(s,    n, i, c, qc, j, ci, inner, at_start, rest, SQ, DQ) {
        SQ = sprintf("%c", 39)   # single quote
        DQ = sprintf("%c", 34)   # double quote
        n = length(s)
        i = 1
        at_start = 1
        while (i <= n) {
            c = substr(s, i, 1)
            if (c == DQ || c == SQ) {
                qc = c
                ci = 0
                for (j = i + 1; j <= n; j++) {
                    if (substr(s, j, 1) == qc) { ci = j; break }
                }
                if (ci == 0) {
                    # Unterminated quote: treat remainder as inert text.
                    return 0
                }
                inner = substr(s, i + 1, ci - i - 1)
                if (index(inner, "$(") == 0 && index(inner, "`") == 0) {
                    # Inert quoted span: skip entirely -- its contents are
                    # argument text (grep pattern, echo label, ...), never a
                    # command position.
                    i = ci + 1
                    at_start = 0
                    continue
                }
                # Carries command substitution: keep separators ACTIVE by
                # consuming only the opening quote and continuing the scan
                # char-by-char, so a nested $( is still checked.
                i++
                at_start = 0
                continue
            }
            if (c == ";") { at_start = 1; i++; continue }
            if (c == "&") {
                at_start = 1
                if (i < n && substr(s, i + 1, 1) == "&") { i += 2 } else { i++ }
                continue
            }
            if (c == "|") {
                at_start = 1
                if (i < n && substr(s, i + 1, 1) == "|") { i += 2 } else { i++ }
                continue
            }
            if (c == "$" && i < n && substr(s, i + 1, 1) == "(") {
                at_start = 1
                i += 2
                continue
            }
            if (c == " " || c == "\t") { i++; continue }
            if (at_start) {
                rest = substr(s, i)
                if (rest ~ /^gh[ \t]+pr[ \t]+merge([ \t;&|)<>]|$)/) {
                    return 1
                }
                at_start = 0
            }
            i++
        }
        return 0
    }
    { if (check($0)) found = 1 }
    END { print (found ? "1" : "0") }
    '
}

GH_PR_MERGE_MATCH=$(gh_pr_merge_invocation "$COMMAND" 2>/dev/null) || GH_PR_MERGE_MATCH=""
if [[ "$GH_PR_MERGE_MATCH" == "1" ]]; then
    # Resolve the merge-pr.sh path for the current repo context. Prefer an
    # in-repo installed copy (./.loom/scripts/merge-pr.sh); fall back to the
    # loom-checkout copy under defaults/scripts/ (via $LOOM_HOME) when the repo
    # runs scripts directly from the checkout rather than an installed copy.
    MERGE_SCRIPT="./.loom/scripts/merge-pr.sh"
    if [[ -n "$REPO_ROOT" ]] && [[ ! -x "$REPO_ROOT/.loom/scripts/merge-pr.sh" ]]; then
        if [[ -n "${LOOM_HOME:-}" ]] && [[ -x "$LOOM_HOME/defaults/scripts/merge-pr.sh" ]]; then
            MERGE_SCRIPT="$LOOM_HOME/defaults/scripts/merge-pr.sh"
        elif [[ -x "$REPO_ROOT/defaults/scripts/merge-pr.sh" ]]; then
            MERGE_SCRIPT="$REPO_ROOT/defaults/scripts/merge-pr.sh"
        fi
    fi
    deny "Use $MERGE_SCRIPT <PR_NUMBER> instead of 'gh pr merge'. The script merges via the GitHub API without local checkout, which avoids worktree errors."
fi

# =============================================================================
# LOOM: Block pip install -e inside worktrees (issue #2495)
#
# Editable pip installs overwrite a global .pth file in site-packages.
# When multiple builders run in parallel worktrees, each 'pip install -e .'
# clobbers the .pth to point at its own worktree, causing all other Python
# processes to import from the wrong source tree.
#
# PYTHONPATH is already set by agent-spawn.sh and _build_worktree_env()
# so editable installs are unnecessary inside worktrees.
# =============================================================================

WORKTREE_PATH="${LOOM_WORKTREE_PATH:-}"
if [[ -n "$WORKTREE_PATH" ]]; then
    if echo "$COMMAND" | grep -qE '(pip|pip3|uv pip)\s+install\s+.*-e\s' || \
       echo "$COMMAND" | grep -qE '(pip|pip3|uv pip)\s+install\s+.*--editable\s'; then
        deny "BLOCKED: 'pip install -e' is not allowed inside worktrees. Editable installs overwrite the global .pth file, breaking parallel builders (see issue #2495). PYTHONPATH is already configured for this worktree — imports resolve correctly without editable installs."
    fi
fi

# =============================================================================
# ALLOW - Everything else passes through
# =============================================================================

exit 0
