#!/usr/bin/env bash
# scripts/lint/test/run-tests.sh
#
# Smoke tests for scripts/lint/check-renamed-namespace-refs.sh.
# Runs the linter against positive and negative fixture files and asserts
# the expected exit codes / output behavior. Also runs against the live
# post-Doctor APN files to confirm they are clean.

set -euo pipefail

here="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
lint="$here/../check-renamed-namespace-refs.sh"
repo_root="$(cd "$here/../../.." && pwd)"

pass=0
fail=0

note() { printf '  %s\n' "$*"; }
ok()   { printf '  [OK] %s\n' "$*"; pass=$((pass + 1)); }
bad()  { printf '  [FAIL] %s\n' "$*" >&2; fail=$((fail + 1)); }

run_case() {
  local desc="$1"; shift
  local expected_exit="$1"; shift
  local expected_stderr_pattern="$1"; shift
  # Remaining args: files to pass to the linter.
  printf '\n%s\n' "$desc"
  local actual_stderr actual_exit
  set +e
  actual_stderr="$("$lint" "$@" 2>&1 >/dev/null)"
  actual_exit=$?
  set -e
  if [ "$actual_exit" -ne "$expected_exit" ]; then
    bad "exit code: expected $expected_exit, got $actual_exit"
    note "stderr was:"
    note "$actual_stderr"
    return
  fi
  ok "exit code = $expected_exit"
  if [ -n "$expected_stderr_pattern" ]; then
    if echo "$actual_stderr" | grep -qE "$expected_stderr_pattern"; then
      ok "stderr matches: $expected_stderr_pattern"
    else
      bad "stderr did NOT match: $expected_stderr_pattern"
      note "stderr was:"
      note "$actual_stderr"
    fi
  else
    if [ -z "$actual_stderr" ]; then
      ok "stderr empty (as expected)"
    else
      bad "expected empty stderr, got:"
      note "$actual_stderr"
    fi
  fi
}

# Case 1: positive fixture should exit 1 and report Erdos741.foo / .bar.
run_case "positive fixture (stale Erdos741.* refs)" \
  1 \
  "stale namespace 'Erdos741'" \
  "$here/positive-stale-ref.lean"

# Case 2: negative clean fixture should exit 0 with empty stderr.
run_case "negative fixture (clean, no stale refs)" \
  0 \
  "" \
  "$here/negative-clean.lean"

# Case 3: file with no namespace declaration should silently exit 0.
run_case "negative fixture (no namespace declared)" \
  0 \
  "" \
  "$here/negative-no-namespace.lean"

# Case 4: file with multiple namespaces where the "base" is itself declared
# (legitimate cross-namespace ref) should exit 0.
run_case "negative fixture (cross-namespace ref to a sibling declared namespace)" \
  0 \
  "" \
  "$here/negative-nested-namespace.lean"

# Case 5 (smoke): real post-Doctor APN files are expected to be clean.
# NOTE: Erdos12ProblemAPNPartII.lean is known to contain legitimate
# `Erdos12.P_n_def` in-body references (see issue #20847 commentary); we
# exclude it from the strict smoke test and verify the others.
apn_files=(
  "$repo_root/proofs/Proofs/Erdos741ProblemAPNPartI.lean"
  "$repo_root/proofs/Proofs/Erdos741ProblemAPNPartII.lean"
  "$repo_root/proofs/Proofs/Erdos152ProblemAPN.lean"
  "$repo_root/proofs/Proofs/Erdos26APN_Tenenbaum.lean"
  "$repo_root/proofs/Proofs/Erdos12ProblemAPNPartI.lean"
  "$repo_root/proofs/Proofs/Erdos846ProblemAPN.lean"
)
existing=()
for f in "${apn_files[@]}"; do
  if [ -f "$f" ]; then existing+=("$f"); fi
done
if [ "${#existing[@]}" -gt 0 ]; then
  run_case "smoke: live APN files are clean (post-Doctor)" \
    0 \
    "" \
    "${existing[@]}"
else
  note "smoke: no APN files found, skipping live-file smoke test"
fi

printf '\nResults: %d passed, %d failed\n' "$pass" "$fail"
if [ "$fail" -ne 0 ]; then
  exit 1
fi
