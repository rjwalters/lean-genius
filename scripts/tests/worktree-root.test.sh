#!/bin/bash
# Unit tests for scripts/lib/worktree-root.sh (issue #37509), mirroring
# Loom's defaults/scripts/tests/test-worktree-root-override.sh.
#
# Section 1 exercises the resolver (loom_worktree_root) directly:
#   - default (no override)              => $repo_root/.loom/worktrees
#   - LOOM_WORKTREE_ROOT absolute        => ${env%/}/$(basename repo_root)
#   - LOOM_WORKTREE_ROOT trailing slash  => stripped
#   - LOOM_WORKTREE_ROOT relative        => stderr warning + default fallback
#   - config worktree.root absolute      => ${cfg%/}/$(basename repo_root)
#   - config worktree.root relative      => stderr warning + default fallback
#   - env var beats config
#   - malformed config JSON              => soft-fail to default
#   - config without worktree.root key   => default
#
# Section 2 replicates the janitor/guardian override classification:
#   - clean-branches.sh WORKTREE_SCAN_ROOTS dual-scan (default + override,
#     deduped when equal)
#   - clean-branches.sh outside-pass prefix classification (an override-root
#     worktree is INSIDE / Loom-managed, not out-of-tree)
#   - infra-guardian.sh reaper allow-pattern matches override-root worktrees
#
# Everything is tmpdir-based; no network, no writes outside mktemp dirs.
# Run: bash scripts/tests/worktree-root.test.sh
# Exits non-zero if any assertion fails.
set -u

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
# shellcheck source=../lib/worktree-root.sh
source "$SCRIPT_DIR/../lib/worktree-root.sh"

PASS=0; FAIL=0
assert_eq() { # <desc> <expected> <actual>
    if [[ "$3" == "$2" ]]; then echo "  ok: $1 -> $3"; ((PASS++)); else echo "  FAIL: $1 expected '$2' got '$3'"; ((FAIL++)); fi
}
assert_contains() { # <desc> <needle> <haystack>
    if [[ "$3" == *"$2"* ]]; then echo "  ok: $1"; ((PASS++)); else echo "  FAIL: $1 ('$3' does not contain '$2')"; ((FAIL++)); fi
}

ROOT=$(mktemp -d)
trap 'rm -rf "$ROOT"' EXIT
REPO="$ROOT/lean-genius"
mkdir -p "$REPO/.loom"

echo "--- Section 1: resolver semantics ---"

# Default: no env, no config file.
unset LOOM_WORKTREE_ROOT 2>/dev/null || true
assert_eq "default (no override)" "$REPO/.loom/worktrees" "$(loom_worktree_root "$REPO")"

# Env var, absolute.
assert_eq "env absolute" "$ROOT/stripe/lean-genius" \
    "$(LOOM_WORKTREE_ROOT="$ROOT/stripe" loom_worktree_root "$REPO")"

# Env var, trailing slash stripped.
assert_eq "env trailing slash" "$ROOT/stripe/lean-genius" \
    "$(LOOM_WORKTREE_ROOT="$ROOT/stripe/" loom_worktree_root "$REPO")"

# Env var, relative -> warn + fall back to default.
out="$(LOOM_WORKTREE_ROOT="relative/path" loom_worktree_root "$REPO" 2>/dev/null)"
err="$(LOOM_WORKTREE_ROOT="relative/path" loom_worktree_root "$REPO" 2>&1 >/dev/null)"
assert_eq "env relative falls back" "$REPO/.loom/worktrees" "$out"
assert_contains "env relative warns on stderr" "must be an absolute path" "$err"

# Config key, absolute.
printf '{"worktree": {"root": "%s"}}\n' "$ROOT/stripe" > "$REPO/.loom/config.json"
assert_eq "config absolute" "$ROOT/stripe/lean-genius" "$(loom_worktree_root "$REPO")"

# Config key, trailing slash stripped.
printf '{"worktree": {"root": "%s/"}}\n' "$ROOT/stripe" > "$REPO/.loom/config.json"
assert_eq "config trailing slash" "$ROOT/stripe/lean-genius" "$(loom_worktree_root "$REPO")"

# Env var beats config.
printf '{"worktree": {"root": "%s"}}\n' "$ROOT/config-root" > "$REPO/.loom/config.json"
assert_eq "env beats config" "$ROOT/env-root/lean-genius" \
    "$(LOOM_WORKTREE_ROOT="$ROOT/env-root" loom_worktree_root "$REPO")"

# Config key, relative -> warn + fall back.
printf '{"worktree": {"root": "not/absolute"}}\n' > "$REPO/.loom/config.json"
out="$(loom_worktree_root "$REPO" 2>/dev/null)"
err="$(loom_worktree_root "$REPO" 2>&1 >/dev/null)"
assert_eq "config relative falls back" "$REPO/.loom/worktrees" "$out"
assert_contains "config relative warns on stderr" "must be an absolute path" "$err"

# Malformed JSON -> soft-fail to default.
printf 'this is not json{{{\n' > "$REPO/.loom/config.json"
assert_eq "malformed config soft-fails" "$REPO/.loom/worktrees" "$(loom_worktree_root "$REPO" 2>/dev/null)"

# Config present but key absent -> default.
printf '{"other": true}\n' > "$REPO/.loom/config.json"
assert_eq "config without key" "$REPO/.loom/worktrees" "$(loom_worktree_root "$REPO")"

# Config value null -> default (jq '// empty' guard).
printf '{"worktree": {"root": null}}\n' > "$REPO/.loom/config.json"
assert_eq "config null value" "$REPO/.loom/worktrees" "$(loom_worktree_root "$REPO")"

echo ""
echo "--- Section 2: janitor / guardian override classification ---"

# Mirror of scripts/clean-branches.sh scan-roots computation: both the legacy
# default dir and the resolved override root are serviced; dedupe when equal.
compute_scan_roots() { # <repo_root> -> newline-separated scan roots
    local repo_root="$1" resolved
    resolved="$(loom_worktree_root "$repo_root")"
    local roots=("$repo_root/.loom/worktrees")
    if [[ "$resolved" != "$repo_root/.loom/worktrees" ]]; then
        roots+=("$resolved")
    fi
    printf '%s\n' "${roots[@]}"
}

printf '{"worktree": {"root": "%s"}}\n' "$ROOT/stripe" > "$REPO/.loom/config.json"
scan="$(compute_scan_roots "$REPO")"
assert_contains "dual-scan includes default root" "$REPO/.loom/worktrees" "$scan"
assert_contains "dual-scan includes override root" "$ROOT/stripe/lean-genius" "$scan"
assert_eq "dual-scan has 2 roots when overridden" "2" "$(echo "$scan" | wc -l | tr -d ' ')"

rm -f "$REPO/.loom/config.json"
scan="$(compute_scan_roots "$REPO")"
assert_eq "dual-scan dedupes without override" "1" "$(echo "$scan" | wc -l | tr -d ' ')"

# Mirror of the clean-branches.sh outside-pass: worktrees under the resolved
# override root must classify as INSIDE (Loom-managed), never out-of-tree.
classify_outside() { # <repo_root> <wt_path> -> INSIDE|OUTSIDE
    local repo_root="$1" wt="$2"
    local loom_wt_root="$repo_root/.loom/worktrees"
    local claude_wt_root="$repo_root/.claude/worktrees"
    local override_wt_root
    override_wt_root="$(loom_worktree_root "$repo_root")"
    if [[ "$wt" == "$loom_wt_root"/* || "$wt" == "$claude_wt_root"/* || "$wt" == "$override_wt_root"/* ]]; then
        echo INSIDE
    else
        echo OUTSIDE
    fi
}

printf '{"worktree": {"root": "%s"}}\n' "$ROOT/stripe" > "$REPO/.loom/config.json"
assert_eq "outside-pass: override worktree is INSIDE" "INSIDE" \
    "$(classify_outside "$REPO" "$ROOT/stripe/lean-genius/enricher-1")"
assert_eq "outside-pass: default worktree is INSIDE" "INSIDE" \
    "$(classify_outside "$REPO" "$REPO/.loom/worktrees/researcher-2")"
assert_eq "outside-pass: unrelated path is OUTSIDE" "OUTSIDE" \
    "$(classify_outside "$REPO" "$ROOT/elsewhere/scratch")"

# Mirror of scripts/lean/infra-guardian.sh reaper allow-pattern.
guardian_allows() { # <resolved_root> <wt_path> -> YES|NO
    local WORKTREE_ROOT_RESOLVED="$1" wt="$2"
    case "$wt" in
        *"/.loom/worktrees/"*|*"/.claude/worktrees/"*|/private/tmp/*|"$WORKTREE_ROOT_RESOLVED/"*) echo YES ;;
        *) echo NO ;;
    esac
}

resolved="$(loom_worktree_root "$REPO")"
assert_eq "guardian: override-root worktree reapable" "YES" \
    "$(guardian_allows "$resolved" "$ROOT/stripe/lean-genius/erdos-42")"
assert_eq "guardian: default-root worktree reapable" "YES" \
    "$(guardian_allows "$resolved" "$REPO/.loom/worktrees/auditor-1")"
assert_eq "guardian: foreign path not reapable" "NO" \
    "$(guardian_allows "$resolved" "$HOME/some/other/dir")"

echo ""
echo "PASS=$PASS FAIL=$FAIL"
[[ "$FAIL" -eq 0 ]]
