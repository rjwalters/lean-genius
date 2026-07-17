#!/usr/bin/env bash
# guard-destructive.sh - PreToolUse hook to block destructive agent commands
#
# Claude Code PreToolUse hook that intercepts Bash commands before execution.
# Receives JSON on stdin with tool_input.command and cwd fields.
#
# IMPORTANT: This hook only fires when Claude Code is invoked with:
#   --dangerously-skip-permissions  ← hooks FIRE (used by Loom agents)
#
# It does NOT fire with:
#   --permission-mode bypassPermissions  ← hooks SKIPPED entirely
#
# If you have a shell alias like 'alias claude="claude --permission-mode bypassPermissions"',
# this safety hook will be silently disabled in interactive sessions.
# Use --dangerously-skip-permissions instead for automation that needs hooks.
#
# Decisions:
#   - Block (deny): Dangerous commands that should never run
#   - Ask: Commands that need human confirmation
#   - Allow: Everything else (exit 0, no output)
#
# Output format (Claude Code hooks spec):
#   { "hookSpecificOutput": { "hookEventName": "PreToolUse", "permissionDecision": "deny|ask", "permissionDecisionReason": "..." } }
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
    echo "[$(date -u '+%Y-%m-%dT%H:%M:%SZ')] [guard-destructive] $msg" >> "$HOOK_ERROR_LOG" 2>/dev/null || true
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
# ALWAYS BLOCK - Catastrophic commands that should never execute
# =============================================================================

ALWAYS_BLOCK_PATTERNS=(
    # GitHub destructive operations
    'gh repo delete'
    'gh repo archive'

    # Force push to main/master (various flag forms)
    'git push --force origin main'
    'git push --force origin master'
    'git push -f origin main'
    'git push -f origin master'
    'git push --force-with-lease origin main'
    'git push --force-with-lease origin master'

    # Filesystem destruction — root only. Anchor the target to exactly `/`
    # (end / whitespace / glob) so legitimate absolute paths like
    # `rm -rf /Volumes/Stripe/...` fall through to the scope check below
    # instead of being caught by a bare `/` substring. Flag order tolerant.
    'rm\s+-[a-zA-Z]*[rf][a-zA-Z]*\s+/(\s|$|\*)'
    'rm\s+-[a-zA-Z]*[rf][a-zA-Z]*\s+/\*'
    'rm -rf ~'
    'rm -rf \$HOME'

    # Fork bombs
    ':\(\)\{ :\|:& \};:'

    # Pipe to shell (supply chain risk)
    'curl .* \| .*sh'
    'curl .* \| bash'
    'wget .* \| .*sh'
    'wget .* -O- \| sh'

    # Cloud infrastructure destruction
    'aws s3 rm.*--recursive'
    'aws s3 rb'
    'aws ec2 terminate'
    'aws iam delete'
    'aws cloudformation delete-stack'
    'gcloud.*delete'
    'az.*delete'
    'az group delete'

    # Docker mass destruction
    'docker system prune'

    # System reboot/shutdown
    'reboot'
    'shutdown'
    'halt'
    'poweroff'
    'init 0'
    'init 6'

    # Database destruction
    'DROP DATABASE'
    'DROP TABLE'
    'DROP SCHEMA'
    'TRUNCATE TABLE'
)

for pattern in "${ALWAYS_BLOCK_PATTERNS[@]}"; do
    if echo "$COMMAND" | grep -qiE "$pattern"; then
        deny "BLOCKED: Command matches dangerous pattern: $pattern"
    fi
done

# =============================================================================
# rm -rf SCOPE CHECK - Block rm with recursive/force flags outside repo
#
# Only inspects command SEGMENTS whose command word is a bare filesystem `rm`.
# `docker rm` / `git rm` / `podman rm` are container/index ops, not filesystem
# path removals, and are exempt. Target paths are extracted from the rm segment
# ONLY (split on ; && || | newline), so a path mentioned in an unrelated
# segment of a compound command (e.g. `docker rm c ; git -C /Volumes/... ...`)
# is not misread as an rm target. Agent worktree roots (default .loom/worktrees
# and any configured worktree.root such as /Volumes/Stripe) are in-scope.
# =============================================================================

# Configured worktree root (best-effort; runtime .loom/config.json is gitignored)
WORKTREE_ROOT=""
if [[ -n "$REPO_ROOT" ]] && [[ -f "$REPO_ROOT/.loom/config.json" ]] && command -v jq &>/dev/null; then
    WORKTREE_ROOT=$(jq -r '.worktree.root // empty' "$REPO_ROOT/.loom/config.json" 2>/dev/null) || WORKTREE_ROOT=""
fi

# Split the compound command into segments and inspect each that is a bare `rm`.
while IFS= read -r segment; do
    # Trim leading whitespace
    segment="${segment#"${segment%%[![:space:]]*}"}"
    # Command word must be exactly `rm` (exempts docker/git/podman rm, and words
    # like `confirm`, `rmdir`).
    [[ "$segment" =~ ^rm[[:space:]] ]] || continue
    # Only care about recursive/force removals
    echo "$segment" | grep -qE 'rm\s+(-[a-zA-Z]*[rf][a-zA-Z]*\s+)+' || continue

    TARGETS=$(echo "$segment" | sed 's/rm\s\+//' | tr ' ' '\n' | grep -v '^-' | head -20)

    for target in $TARGETS; do
        [[ -z "$target" ]] && continue

        # Skip known-safe patterns (allowlist)
        case "$target" in
            node_modules|./node_modules|*/node_modules) continue ;;
            target|./target|*/target) continue ;;
            dist|./dist|*/dist) continue ;;
            build|./build|*/build) continue ;;
            .loom/worktrees/*|*/.loom/worktrees/*) continue ;;
            .next|./.next|*/.next) continue ;;
            __pycache__|./__pycache__|*/__pycache__) continue ;;
            .pytest_cache|./.pytest_cache|*/.pytest_cache) continue ;;
            *.pyc) continue ;;
        esac

        # Resolve path to absolute
        ABS_PATH=""
        if [[ "$target" = /* ]]; then
            ABS_PATH="$target"
        elif [[ -n "$CWD" ]]; then
            ABS_PATH=$(cd "$CWD" 2>/dev/null && realpath -m "$target" 2>/dev/null || echo "$CWD/$target")
        fi

        # Block dangerous absolute paths
        if [[ "$ABS_PATH" == "/" ]] || [[ "$ABS_PATH" == "/home" ]] || \
           [[ "$ABS_PATH" == "$HOME" ]] || [[ "$ABS_PATH" == "/tmp" ]] || \
           [[ "$ABS_PATH" == "/usr" ]] || [[ "$ABS_PATH" == "/var" ]] || \
           [[ "$ABS_PATH" == "/etc" ]] || [[ "$ABS_PATH" == "/opt" ]]; then
            deny "BLOCKED: rm on protected system path: $ABS_PATH"
        fi

        # In-scope roots: repo root, configured worktree root, and the default
        # worktree area. rm inside any of these is fine.
        if [[ -n "$ABS_PATH" ]]; then
            in_scope=0
            [[ -n "$REPO_ROOT" ]] && [[ "$ABS_PATH" == "$REPO_ROOT"* ]] && in_scope=1
            [[ -n "$WORKTREE_ROOT" ]] && [[ "$ABS_PATH" == "$WORKTREE_ROOT"* ]] && in_scope=1
            # Agent worktrees for this repo (basename match) under any root
            case "$ABS_PATH" in
                */lean-genius/*) in_scope=1 ;;
                # Ephemeral temp/scratchpad roots. Only SUBPATHS are allowed here
                # (bare /tmp, /var, etc. are already denied by the protected-path
                # block above). This matches upstream loom, which permits
                # `rm -rf /tmp/whatever`, and covers the Claude Code scratchpad at
                # /private/tmp/... and $TMPDIR on macOS (/var/folders/...), so
                # agents can clean up their own temp files.
                /tmp/*|/private/tmp/*|/var/tmp/*|/private/var/tmp/*|/var/folders/*|/private/var/folders/*) in_scope=1 ;;
            esac
            if [[ -n "$REPO_ROOT" ]] && [[ "$in_scope" -eq 0 ]]; then
                deny "BLOCKED: rm target outside repository/worktree roots: $ABS_PATH (repo: $REPO_ROOT)"
            fi
        fi
    done
done < <(echo "$COMMAND" | tr ';|&' '\n')

# =============================================================================
# DELETE without WHERE - Database safety
# =============================================================================

if echo "$COMMAND" | grep -qiE 'DELETE\s+FROM\s+' && \
   ! echo "$COMMAND" | grep -qiE 'WHERE\s+'; then
    deny "BLOCKED: DELETE FROM without WHERE clause"
fi

# =============================================================================
# BRANCH-AWARE GIT FORCE OPS
#
# Force pushes and hard resets stay strict on main/master but are allowed
# without confirmation on working branches, so autonomous/background agents
# (which cannot answer an "ask" prompt) don't stall on routine branch resets.
# Operator preference: merge-and-fix-conflicts on shared history; force ops
# are only routine on single-owner working branches.
#
# Destination resolution, in order:
#   1. explicit refspec on the push command (dst side of src:dst)
#   2. the branch checked out where the command runs (cwd or `git -C <path>`)
#   3. unresolvable (detached HEAD, not a repo) -> ask, as before
# =============================================================================

is_protected_branch() {
    case "$1" in
        main|master) return 0 ;;
        *) return 1 ;;
    esac
}

# First simple-command segment of COMMAND matching a pattern (splits on ;|&)
command_segment() {
    echo "$COMMAND" | tr ';|&' '\n' | grep -m1 -E "$1" 2>/dev/null || true
}

# Branch checked out where the command will run (honors `git -C <path>`)
checked_out_branch() {
    local seg="$1" path="${CWD:-.}" c_path=""
    c_path=$(echo "$seg" | sed -nE 's/.*git[[:space:]]+-C[[:space:]]+([^[:space:]]+).*/\1/p' 2>/dev/null) || c_path=""
    [[ -n "$c_path" ]] && path="$c_path"
    git -C "$path" symbolic-ref --short -q HEAD 2>/dev/null || true
}

# --- git push --force / -f / --force-with-lease ---
if echo "$COMMAND" | grep -qE 'git[[:space:]].*push[[:space:]].*(--force([[:space:]=]|$)|--force-with-lease|-[a-zA-Z]*f[a-zA-Z]*([[:space:]]|$))'; then
    seg=$(command_segment 'git[[:space:]].*push')
    push_dest=""
    if [[ -n "$seg" ]]; then
        # Non-flag tokens after 'push' are [remote] [refspec...]
        rest="${seg#*push}"
        pos_args=()
        for tok in $rest; do
            case "$tok" in
                -*) ;;                 # skip flags (incl. --force-with-lease=ref)
                *) pos_args+=("$tok") ;;
            esac
        done
        if (( ${#pos_args[@]} >= 2 )); then
            push_dest="${pos_args[1]##*:}"   # dst side of refspec
            push_dest="${push_dest#refs/heads/}"
        fi
    fi
    # No explicit refspec -> the push targets the checked-out branch
    if [[ -z "$push_dest" ]]; then
        push_dest=$(checked_out_branch "$seg")
    fi
    if [[ -z "$push_dest" ]]; then
        ask "Force push with unresolvable target branch — confirm: $COMMAND"
    elif is_protected_branch "$push_dest"; then
        deny "BLOCKED: Force push targeting protected branch '$push_dest'"
    fi
    # Working branch -> allowed, fall through
fi

# --- git reset --hard ---
if echo "$COMMAND" | grep -qE 'git[[:space:]].*reset[[:space:]]+.*--hard'; then
    seg=$(command_segment 'git[[:space:]].*reset')
    reset_branch=$(checked_out_branch "$seg")
    if [[ -z "$reset_branch" ]]; then
        ask "Hard reset with unresolvable checkout (detached HEAD or not a repo) — confirm: $COMMAND"
    elif is_protected_branch "$reset_branch"; then
        ask "Hard reset on protected branch '$reset_branch' — confirm: $COMMAND"
    fi
    # Working branch -> allowed, fall through
fi

# =============================================================================
# REQUIRE CONFIRMATION - Potentially dangerous but sometimes legitimate
# =============================================================================

ASK_PATTERNS=(
    # Git destructive operations
    # NOTE: force pushes and hard resets are handled by the branch-aware
    # section below (strict on main/master, allowed on working branches).
    'git clean -fd'
    'git checkout \.'
    'git restore \.'

    # GitHub operations that modify shared state
    'gh pr close'
    'gh issue close'
    'gh release delete'
    'gh label delete'

    # Cloud CLI operations
    'aws s3'
    'aws ec2'
    'aws lambda'

    # Docker operations
    # Container lifecycle ops (rm/stop/kill/restart) are intentionally NOT
    # listed — containers are disposable and agents routinely manage their
    # own build containers. Images and volumes stay guarded: images are
    # shared and volumes hold multi-hour mathlib cache builds.
    'docker rmi'
    'docker image rm'
    'docker image prune'
    'docker volume rm'
    'docker volume prune'

    # Service management
    'systemctl restart'
    'systemctl stop'
    'systemctl disable'

    # Kubernetes operations
    'kubectl delete'
    'kubectl rollout restart'
    'kubectl drain'

    # SkyPilot infrastructure
    'sky down'
    'sky stop'

    # Credential exposure
    'printenv.*SECRET'
    'printenv.*TOKEN'
    'printenv.*KEY'
    'cat.*/\.ssh/'
    'cat.*/\.aws/credentials'
)

# Match ask-patterns against the command with quoted strings removed, so a
# pattern appearing only inside a string argument (grep "docker rmi" file,
# echo 'gh pr close', a commit message mentioning a command) doesn't prompt.
# Real invocations are unquoted at command position and still match. The
# deny tier above intentionally keeps matching the raw text (fail-safe).
COMMAND_UNQUOTED=$(printf '%s' "$COMMAND" | sed -E "s/'[^']*'/ /g; s/\"[^\"]*\"/ /g" 2>/dev/null) || COMMAND_UNQUOTED="$COMMAND"

for pattern in "${ASK_PATTERNS[@]}"; do
    if echo "$COMMAND_UNQUOTED" | grep -qE "$pattern"; then
        ask "Command requires confirmation: $COMMAND"
    fi
done

# =============================================================================
# LOOM: Prefer merge-pr.sh over gh pr merge
# =============================================================================

if echo "$COMMAND" | grep -qE 'gh\s+pr\s+merge'; then
    # .loom/scripts/ is gitignored runtime state and is not installed in this
    # repo, so resolve the merge script from the loom checkout as a fallback
    # rather than pointing agents at a path that doesn't exist.
    MERGE_PR_SCRIPT="./.loom/scripts/merge-pr.sh"
    if [[ ! -x "$MERGE_PR_SCRIPT" ]]; then
        for candidate in \
            "${LOOM_HOME:-$HOME/GitHub/loom}/defaults/scripts/merge-pr.sh" \
            "$HOME/GitHub/loom/defaults/scripts/merge-pr.sh"; do
            if [[ -x "$candidate" ]]; then
                MERGE_PR_SCRIPT="$candidate"
                break
            fi
        done
    fi
    deny "Use $MERGE_PR_SCRIPT <PR_NUMBER> instead of 'gh pr merge'. The script merges via the GitHub API without local checkout, which avoids worktree errors. Known issue: on this host the script's post-merge verify false-negatives ('Merge API call returned but PR is not merged') even when the merge succeeded — always confirm with 'gh pr view <PR_NUMBER> --json state' before retrying."
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
