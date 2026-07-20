#!/bin/bash
# Unit tests for scripts/lib/oq-policy.sh (issue #39827).
#
# Covers:
#   - oq_depth: counts -oq- segments in a slug (0 for roots, N for chains)
#   - oq_max_depth: env var > .lean/config/oq-policy.json > built-in default
#   - oq_over_cap / oq_at_or_over_cap: cap comparisons
#
# tmpdir-based; no network, no writes outside mktemp dirs.
# Run: bash scripts/tests/oq-policy.test.sh
set -u

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
# shellcheck source=../lib/oq-policy.sh
source "$SCRIPT_DIR/../lib/oq-policy.sh"

PASS=0; FAIL=0
assert_eq() { # <desc> <expected> <actual>
    if [[ "$3" == "$2" ]]; then echo "  ok: $1 -> $3"; ((PASS++)); else echo "  FAIL: $1 expected '$2' got '$3'"; ((FAIL++)); fi
}
assert_true() { # <desc> ; runs "$@" from index 2
    local desc="$1"; shift
    if "$@"; then echo "  ok: $desc"; ((PASS++)); else echo "  FAIL: $desc (expected success)"; ((FAIL++)); fi
}
assert_false() { # <desc> ; runs "$@" from index 2
    local desc="$1"; shift
    if "$@"; then echo "  FAIL: $desc (expected failure)"; ((FAIL++)); else echo "  ok: $desc"; ((PASS++)); fi
}

echo "--- Section 1: oq_depth ---"
assert_eq "root entry has depth 0" "0" "$(oq_depth 'abel-ruffini')"
assert_eq "single oq segment" "1" "$(oq_depth 'abel-ruffini-oq-04')"
assert_eq "two oq segments" "2" "$(oq_depth 'dirichlets-theorem-oq-02-oq-01')"
assert_eq "deep chain" "11" "$(oq_depth 'abel-ruffini-oq-04-oq-02-oq-02-oq-08-oq-01-oq-01-oq-01-oq-01-oq-01-oq-01-oq-01')"
assert_eq "empty slug" "0" "$(oq_depth '')"
# A literal "oq" in the base name (no -NN) must not be miscounted.
assert_eq "non-oq token not counted" "0" "$(oq_depth 'oqbert-theorem')"
assert_eq "incomplete suffix not counted as oq" "2" "$(oq_depth 'angle-trisection-oq-02-oq-01-incomplete-01')"

echo "--- Section 2: oq_max_depth resolution ---"
# Isolate from any ambient env / repo config: point the resolver at a temp repo.
ROOT=$(mktemp -d)
trap 'rm -rf "$ROOT"' EXIT
mkdir -p "$ROOT/.git" "$ROOT/.lean/config"
# Make the resolver treat $ROOT as the repo root: run from inside it and neutralize git.
_run_in_repo() { ( cd "$ROOT" && env -u MAX_OQ_DEPTH PATH="$PATH" bash -c "
    source '$SCRIPT_DIR/../lib/oq-policy.sh'
    $1
" ); }

# No env, no config -> built-in default (3).
rm -f "$ROOT/.lean/config/oq-policy.json"
assert_eq "default when unconfigured" "3" "$(_run_in_repo 'oq_max_depth')"

# Config file value is honored.
printf '{"maxOqDepth": 5}\n' > "$ROOT/.lean/config/oq-policy.json"
assert_eq "config file honored" "5" "$(_run_in_repo 'oq_max_depth')"

# Env var beats config file.
assert_eq "env beats config" "2" "$( ( cd "$ROOT" && MAX_OQ_DEPTH=2 bash -c "source '$SCRIPT_DIR/../lib/oq-policy.sh'; oq_max_depth" ) )"

# Non-numeric env var is ignored -> falls back to config (5).
assert_eq "non-numeric env ignored" "5" "$( ( cd "$ROOT" && MAX_OQ_DEPTH=abc bash -c "source '$SCRIPT_DIR/../lib/oq-policy.sh'; oq_max_depth" ) )"

# Malformed config -> built-in default.
printf 'not json\n' > "$ROOT/.lean/config/oq-policy.json"
assert_eq "malformed config falls back to default" "3" "$(_run_in_repo 'oq_max_depth')"

echo "--- Section 3: cap comparisons (cap=3 via env) ---"
export MAX_OQ_DEPTH=3
assert_false "depth 0 not over cap" oq_over_cap 'root-problem'
assert_false "depth 3 not over cap (at cap)" oq_over_cap 'a-oq-01-oq-02-oq-03'
assert_true  "depth 4 over cap" oq_over_cap 'a-oq-01-oq-02-oq-03-oq-04'
assert_false "depth 2 not at-or-over cap" oq_at_or_over_cap 'a-oq-01-oq-02'
assert_true  "depth 3 at-or-over cap" oq_at_or_over_cap 'a-oq-01-oq-02-oq-03'
assert_true  "depth 4 at-or-over cap" oq_at_or_over_cap 'a-oq-01-oq-02-oq-03-oq-04'
unset MAX_OQ_DEPTH

echo ""
echo "Passed: $PASS  Failed: $FAIL"
[[ $FAIL -eq 0 ]]
