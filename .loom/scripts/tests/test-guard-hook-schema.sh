#!/usr/bin/env bash
# test-guard-hook-schema.sh - Regression tests for the PreToolUse hook schema
# emitted by guard-destructive.sh and guard-readonly-dirs.sh.template (issue #3550).
#
# Claude Code's PreToolUse hook schema REQUIRES a `hookEventName: "PreToolUse"`
# field inside the `hookSpecificOutput` object. Without it, Claude Code silently
# discards the permission decision and the guard becomes inert — every deny/ask
# is a no-op and the guarded command runs anyway.
#
# These tests feed crafted stdin JSON to each hook and assert the emitted JSON
# carries `.hookSpecificOutput.hookEventName == "PreToolUse"` for both the deny
# and ask decisions. They also assert the raw jq-fallback echo strings (used when
# jq -n fails at runtime) carry the same field, so future schema drift is caught
# on either code path.
#
# Usage:
#   bash defaults/scripts/tests/test-guard-hook-schema.sh

set -uo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
DEFAULTS_DIR="$(cd "$SCRIPT_DIR/../.." && pwd)"
GUARD_DESTRUCTIVE="$DEFAULTS_DIR/hooks/guard-destructive.sh"
GUARD_LOOM_WORKFLOW="$DEFAULTS_DIR/hooks/guard-loom-workflow.sh"
GUARD_READONLY_TEMPLATE="$DEFAULTS_DIR/hooks/guard-readonly-dirs.sh.template"

RED='\033[0;31m'
GREEN='\033[0;32m'
NC='\033[0m'

TESTS_RUN=0
TESTS_PASSED=0
TESTS_FAILED=0

pass() {
    TESTS_RUN=$((TESTS_RUN + 1))
    TESTS_PASSED=$((TESTS_PASSED + 1))
    echo -e "  ${GREEN}PASS${NC}: $1"
}

fail() {
    TESTS_RUN=$((TESTS_RUN + 1))
    TESTS_FAILED=$((TESTS_FAILED + 1))
    echo -e "  ${RED}FAIL${NC}: $1"
    [[ -n "${2:-}" ]] && echo "    $2"
}

# Assert a JSON blob has the given jq boolean expression evaluate to true.
assert_jq_true() {
    local json="$1" expr="$2" msg="$3"
    local result
    result=$(printf '%s' "$json" | jq -r "$expr" 2>/dev/null) || result="<jq-parse-error>"
    if [[ "$result" == "true" ]]; then
        pass "$msg"
    else
        fail "$msg" "expected '$expr' == true, got '$result'; json: $json"
    fi
}

if ! command -v jq &>/dev/null; then
    echo "ERROR: jq is required to run these tests" >&2
    exit 1
fi

if [[ ! -f "$GUARD_DESTRUCTIVE" ]]; then
    echo "ERROR: $GUARD_DESTRUCTIVE not found" >&2
    exit 1
fi
if [[ ! -f "$GUARD_LOOM_WORKFLOW" ]]; then
    echo "ERROR: $GUARD_LOOM_WORKFLOW not found" >&2
    exit 1
fi
if [[ ! -f "$GUARD_READONLY_TEMPLATE" ]]; then
    echo "ERROR: $GUARD_READONLY_TEMPLATE not found" >&2
    exit 1
fi

# ---------------------------------------------------------------------------
# guard-destructive.sh — functional deny path
# ---------------------------------------------------------------------------
echo "guard-destructive.sh: deny decision carries hookEventName"
DENY_INPUT=$(jq -n --arg cmd "rm -rf /" --arg cwd "$DEFAULTS_DIR" \
    '{tool_input: {command: $cmd}, cwd: $cwd}')
DENY_OUT=$(printf '%s' "$DENY_INPUT" | bash "$GUARD_DESTRUCTIVE" 2>/dev/null)

assert_jq_true "$DENY_OUT" '.hookSpecificOutput.hookEventName == "PreToolUse"' \
    "deny: hookEventName == PreToolUse"
assert_jq_true "$DENY_OUT" '.hookSpecificOutput.permissionDecision == "deny"' \
    "deny: permissionDecision == deny"
echo ""

# ---------------------------------------------------------------------------
# guard-destructive.sh — functional ask path
# ---------------------------------------------------------------------------
echo "guard-destructive.sh: ask decision carries hookEventName"
ASK_INPUT=$(jq -n --arg cmd "git reset --hard HEAD~1" --arg cwd "$DEFAULTS_DIR" \
    '{tool_input: {command: $cmd}, cwd: $cwd}')
ASK_OUT=$(printf '%s' "$ASK_INPUT" | bash "$GUARD_DESTRUCTIVE" 2>/dev/null)

assert_jq_true "$ASK_OUT" '.hookSpecificOutput.hookEventName == "PreToolUse"' \
    "ask: hookEventName == PreToolUse"
assert_jq_true "$ASK_OUT" '.hookSpecificOutput.permissionDecision == "ask"' \
    "ask: permissionDecision == ask"
echo ""

# ---------------------------------------------------------------------------
# guard-destructive.sh — raw jq-fallback echo strings carry the field
# ---------------------------------------------------------------------------
echo "guard-destructive.sh: raw jq-fallback echoes carry hookEventName"
FALLBACK_LINES=$(grep -c 'echo "{\\"hookSpecificOutput\\":{\\"hookEventName\\":\\"PreToolUse\\"' "$GUARD_DESTRUCTIVE")
TESTS_RUN=$((TESTS_RUN + 1))
if [[ "$FALLBACK_LINES" -eq 2 ]]; then
    TESTS_PASSED=$((TESTS_PASSED + 1))
    echo -e "  ${GREEN}PASS${NC}: both raw fallback echoes (deny + ask) include hookEventName"
else
    TESTS_FAILED=$((TESTS_FAILED + 1))
    echo -e "  ${RED}FAIL${NC}: expected 2 raw fallback echoes with hookEventName, found $FALLBACK_LINES"
fi
echo ""

# ---------------------------------------------------------------------------
# guard-loom-workflow.sh — functional deny path (gh pr merge redirect)
# ---------------------------------------------------------------------------
echo "guard-loom-workflow.sh: deny decision carries hookEventName"
LW_DENY_INPUT=$(jq -n --arg cmd "gh pr merge 123" --arg cwd "$DEFAULTS_DIR" \
    '{tool_input: {command: $cmd}, cwd: $cwd}')
LW_DENY_OUT=$(printf '%s' "$LW_DENY_INPUT" | bash "$GUARD_LOOM_WORKFLOW" 2>/dev/null)

assert_jq_true "$LW_DENY_OUT" '.hookSpecificOutput.hookEventName == "PreToolUse"' \
    "loom-workflow deny: hookEventName == PreToolUse"
assert_jq_true "$LW_DENY_OUT" '.hookSpecificOutput.permissionDecision == "deny"' \
    "loom-workflow deny: permissionDecision == deny"
assert_jq_true "$LW_DENY_OUT" '(.hookSpecificOutput.permissionDecisionReason // "") | contains("merge-pr.sh")' \
    "loom-workflow deny: reason points at merge-pr.sh"
echo ""

# ---------------------------------------------------------------------------
# guard-loom-workflow.sh — precision matching for gh pr merge (issue #43639)
#
# The original matcher (`grep -qE 'gh\s+pr\s+merge'`) matched the phrase as a
# bare substring ANYWHERE in the command, so it false-positived on read-only
# commands that merely MENTION the phrase (a grep pattern searching for it, an
# echo section label). These cases assert the fix: the phrase must be
# anchored at an actual command position to deny; quoted mentions of it must
# pass through; and a genuine invocation at any command position (start,
# after ;, after &&, after $() must still be denied.
# ---------------------------------------------------------------------------
echo "guard-loom-workflow.sh: precision matching (issue #43639)"

lw_decision() {
    # Args: <command>. Echoes the permissionDecision, or "allow" if the hook
    # produced no output (the normal silent-allow contract).
    local cmd="$1" input out decision
    input=$(jq -n --arg cmd "$cmd" --arg cwd "$DEFAULTS_DIR" \
        '{tool_input: {command: $cmd}, cwd: $cwd}')
    out=$(printf '%s' "$input" | bash "$GUARD_LOOM_WORKFLOW" 2>/dev/null)
    if [[ -z "$out" ]]; then
        decision="allow"
    else
        decision=$(printf '%s' "$out" | jq -r '.hookSpecificOutput.permissionDecision // "allow"' 2>/dev/null) || decision="<parse-error>"
    fi
    printf '%s' "$decision"
}

assert_lw_decision() {
    local desc="$1" cmd="$2" expect="$3" got
    got=$(lw_decision "$cmd")
    if [[ "$got" == "$expect" ]]; then
        pass "$desc"
    else
        fail "$desc" "expected decision=$expect got=$got; cmd=[$cmd]"
    fi
}

# False positive #1 (issue #43639): grep searching for the phrase in the
# merge script itself must pass through -- it's read-only and never invokes
# `gh pr merge`.
assert_lw_decision "grep pattern mentioning the phrase passes through" \
    'grep -n "auto|graphql|gh pr merge|gh api" ./.loom/scripts/merge-pr.sh' \
    "allow"

# False positive #2 (issue #43639): an echo section label mentioning the
# phrase inside a compound command must not block the whole command,
# including the unrelated gh api call that follows it.
assert_lw_decision "echo label mentioning the phrase in a compound command passes through" \
    'echo "=== lean-genius: hook gh pr merge block ==="; gh api "search/issues?q=foo"' \
    "allow"

# A genuine invocation must still be blocked at every command position named
# in the acceptance criteria.
assert_lw_decision "genuine invocation at start of command is still denied" \
    'gh pr merge 123' \
    "deny"
assert_lw_decision "genuine invocation after ; is still denied" \
    'echo hi; gh pr merge 123' \
    "deny"
assert_lw_decision "genuine invocation after && is still denied" \
    'true && gh pr merge 123' \
    "deny"
assert_lw_decision "genuine invocation after \$( is still denied" \
    'echo "$(gh pr merge 123)"' \
    "deny"

# A quoted heredoc body (e.g. a commit message built with
# `git commit -m "$(cat <<'EOF' ... EOF)"`) that merely PROSE-MENTIONS the
# phrase must pass through -- heredoc body lines are otherwise
# indistinguishable from real command lines to a per-line scan, and this
# exact pattern is how this fix's own commit message was almost blocked by
# an earlier draft of the matcher during development.
LW_HEREDOC_PROSE=$(cat <<'HDEOF'
git commit -m "$(cat <<'INNER'
fix: anchor gh pr merge deny hook to command position, not substring
INNER
)"
HDEOF
)
assert_lw_decision "quoted heredoc commit message mentioning the phrase passes through" \
    "$LW_HEREDOC_PROSE" \
    "allow"

# A quoted heredoc body that literally contains invocation-looking text is
# still inert (no expansion happens inside a quoted-delimiter heredoc) and
# must pass through.
LW_HEREDOC_LITERAL=$(cat <<'HDEOF'
cat <<'HD'
gh pr merge 999
HD
HDEOF
)
assert_lw_decision "quoted heredoc body containing literal invocation-looking text passes through" \
    "$LW_HEREDOC_LITERAL" \
    "allow"

# An UNQUOTED heredoc delimiter still expands $(...) inside its body, so a
# genuine invocation smuggled that way must still be denied.
LW_HEREDOC_SMUGGLED=$(cat <<'HDEOF'
cat <<HD
$(gh pr merge 123)
HD
HDEOF
)
assert_lw_decision "unquoted heredoc body with smuggled invocation via \$(...) is still denied" \
    "$LW_HEREDOC_SMUGGLED" \
    "deny"

# A genuine invocation on its own line (no heredoc involved) is still denied.
LW_MULTILINE_GENUINE=$(cat <<'HDEOF'
echo about to merge
gh pr merge 123
HDEOF
)
assert_lw_decision "genuine invocation on its own line is still denied" \
    "$LW_MULTILINE_GENUINE" \
    "deny"
echo ""

# ---------------------------------------------------------------------------
# guard-loom-workflow.sh — raw jq-fallback echo strings carry the field
# ---------------------------------------------------------------------------
echo "guard-loom-workflow.sh: raw jq-fallback echoes carry hookEventName"
LW_FALLBACK_LINES=$(grep -c 'echo "{\\"hookSpecificOutput\\":{\\"hookEventName\\":\\"PreToolUse\\"' "$GUARD_LOOM_WORKFLOW")
TESTS_RUN=$((TESTS_RUN + 1))
if [[ "$LW_FALLBACK_LINES" -eq 2 ]]; then
    TESTS_PASSED=$((TESTS_PASSED + 1))
    echo -e "  ${GREEN}PASS${NC}: both raw fallback echoes (deny + ask) include hookEventName"
else
    TESTS_FAILED=$((TESTS_FAILED + 1))
    echo -e "  ${RED}FAIL${NC}: expected 2 raw fallback echoes with hookEventName, found $LW_FALLBACK_LINES"
fi
echo ""

# ---------------------------------------------------------------------------
# guard-readonly-dirs.sh.template — functional deny path
# ---------------------------------------------------------------------------
echo "guard-readonly-dirs.sh.template: deny decision carries hookEventName"
# Materialize the template into a temp git repo with a configured protected dir.
TMP_REPO=$(mktemp -d /tmp/loom-guard-readonly-test.XXXXXX)
trap 'rm -rf "$TMP_REPO"' EXIT
# Canonicalize to defeat the macOS /tmp -> /private/tmp symlink, so the path we
# feed the hook matches the repo root git resolves via `rev-parse`.
TMP_REPO=$(cd "$TMP_REPO" && pwd -P)
(
    cd "$TMP_REPO" || exit 1
    git init -q .
    git config user.email "test@example.com"
    git config user.name "Test"
    mkdir -p vendor
)
READONLY_HOOK="$TMP_REPO/guard-readonly-dirs.sh"
# Inject a non-empty PROTECTED_DIRS array so the guard is active.
sed 's|^PROTECTED_DIRS=(|PROTECTED_DIRS=(\n    "vendor/"|' \
    "$GUARD_READONLY_TEMPLATE" > "$READONLY_HOOK"
chmod +x "$READONLY_HOOK"

RO_INPUT=$(jq -n --arg fp "$TMP_REPO/vendor/lib.js" --arg cwd "$TMP_REPO" \
    '{tool_input: {file_path: $fp}, cwd: $cwd}')
RO_OUT=$(printf '%s' "$RO_INPUT" | bash "$READONLY_HOOK" 2>/dev/null)

assert_jq_true "$RO_OUT" '.hookSpecificOutput.hookEventName == "PreToolUse"' \
    "readonly deny: hookEventName == PreToolUse"
assert_jq_true "$RO_OUT" '.hookSpecificOutput.permissionDecision == "deny"' \
    "readonly deny: permissionDecision == deny"
echo ""

# ---------------------------------------------------------------------------
# guard-readonly-dirs.sh.template — raw jq-fallback echo carries the field
# ---------------------------------------------------------------------------
echo "guard-readonly-dirs.sh.template: raw jq-fallback echo carries hookEventName"
RO_FALLBACK_LINES=$(grep -c 'echo "{\\"hookSpecificOutput\\":{\\"hookEventName\\":\\"PreToolUse\\"' "$GUARD_READONLY_TEMPLATE")
TESTS_RUN=$((TESTS_RUN + 1))
if [[ "$RO_FALLBACK_LINES" -eq 1 ]]; then
    TESTS_PASSED=$((TESTS_PASSED + 1))
    echo -e "  ${GREEN}PASS${NC}: raw fallback echo (deny) includes hookEventName"
else
    TESTS_FAILED=$((TESTS_FAILED + 1))
    echo -e "  ${RED}FAIL${NC}: expected 1 raw fallback echo with hookEventName, found $RO_FALLBACK_LINES"
fi
echo ""

# --- Summary ---
echo "Tests run: $TESTS_RUN, Passed: $TESTS_PASSED, Failed: $TESTS_FAILED"

if [[ $TESTS_FAILED -gt 0 ]]; then
    exit 1
fi
