#!/bin/bash
# guard-destructive.sh - Claude Code PreToolUse hook for blocking destructive commands
#
# Protocol: Reads JSON from stdin with tool_name and tool_input.command
# Exit 0 = allow, Exit 2 = block (stderr shown to Claude as reason)

set -euo pipefail

# Read JSON from stdin; default to empty object on failure
INPUT=$(cat 2>/dev/null) || INPUT="{}"

# Extract the command; default to empty string if missing/malformed
COMMAND=$(echo "$INPUT" | jq -r '.tool_input.command // ""' 2>/dev/null) || COMMAND=""

# Nothing to check if command is empty
if [[ -z "$COMMAND" ]]; then
  exit 0
fi

# --- Git destructive operations ---

# git push --force variants (--force, -f, --force-with-lease)
if echo "$COMMAND" | grep -qE 'git\s+push\s+.*(-f|--force)'; then
  echo "BLOCKED: git push --force is destructive. Use normal 'git push' instead." >&2
  exit 2
fi

# git reset --hard
if echo "$COMMAND" | grep -qE 'git\s+reset\s+--hard'; then
  echo "BLOCKED: git reset --hard discards all local changes irreversibly." >&2
  exit 2
fi

# git clean -f (with optional other flags like -d)
if echo "$COMMAND" | grep -qE 'git\s+clean\s+.*-[a-zA-Z]*f'; then
  echo "BLOCKED: git clean -f permanently deletes untracked files." >&2
  exit 2
fi

# git branch -D (force delete)
if echo "$COMMAND" | grep -qE 'git\s+branch\s+.*-[a-zA-Z]*D'; then
  echo "BLOCKED: git branch -D force-deletes branches. Use 'git branch -d' for safe delete." >&2
  exit 2
fi

# git checkout . (discard all changes)
if echo "$COMMAND" | grep -qE 'git\s+checkout\s+\.'; then
  echo "BLOCKED: git checkout . discards all uncommitted changes." >&2
  exit 2
fi

# git restore . (discard all changes)
if echo "$COMMAND" | grep -qE 'git\s+restore\s+\.'; then
  echo "BLOCKED: git restore . discards all uncommitted changes." >&2
  exit 2
fi

# --- Dangerous filesystem operations ---

# rm -rf on catastrophic paths (/, ~, $HOME)
if echo "$COMMAND" | grep -qE 'rm\s+.*-[a-zA-Z]*r[a-zA-Z]*f.*\s+(/|~|\$HOME)\s*$'; then
  echo "BLOCKED: rm -rf on root/home directory is catastrophic." >&2
  exit 2
fi
if echo "$COMMAND" | grep -qE 'rm\s+.*-[a-zA-Z]*f[a-zA-Z]*r.*\s+(/|~|\$HOME)\s*$'; then
  echo "BLOCKED: rm -rf on root/home directory is catastrophic." >&2
  exit 2
fi

# --- Project-specific: lake build without Docker ---

# Block direct lake build (can consume 100GB+ memory)
if echo "$COMMAND" | grep -qE '(^|\s|&&|\|\||;)lake\s+build'; then
  # Allow if LAKE_UNSAFE=1 is set in the command
  if echo "$COMMAND" | grep -qE 'LAKE_UNSAFE=1'; then
    exit 0
  fi
  echo "BLOCKED: Direct 'lake build' can consume 100GB+ memory and crash the system." >&2
  echo "Use instead: ./proofs/scripts/docker-build.sh <target>" >&2
  exit 2
fi

# All checks passed — allow the command
exit 0
