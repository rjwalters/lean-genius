#!/usr/bin/env bash
#
# Synthetic pollution fixture for issue #21009 (Tailwind v4 oxide scanner hang).
#
# Generates N nested repo-like directories under tmp-tailwind-repro/ that
# mimic the shape of the polluted primary checkout's .claude/worktrees/* +
# .loom/worktrees/* tree. The real polluted state in the primary dev checkout
# has ~725 such dirs; this script defaults to N=50 but is parameterized so
# the operator can crank it up.
#
# Each fixture directory contains:
#
#   - src/index.html, src/index.css, src/App.tsx  (web-scanner targets)
#   - data/blob-*.json                            (volume; mimics src/data/proofs/*/annotations.json)
#   - proofs/*.lean                               (Lean source volume; mimics proofs/Proofs/*.lean)
#   - proofs/.lake -> .                           (TRUE self-referential symlink cycle,
#                                                  replicating the real pollution. Note: this
#                                                  is the kind of cycle most scanners follow
#                                                  unless they track inode IDs.)
#   - nested/<deeper repo skeleton>                (depth-2 fixture so the scanner walks deeper)
#
# The fixture root tmp-tailwind-repro/ is gitignored. Run teardown.sh to clear.
#
# Usage:
#   ./setup.sh           # 50 fixture dirs (default)
#   ./setup.sh 100       # 100 fixture dirs
#   ./setup.sh 200       # 200 fixture dirs
#
# See: https://github.com/rjwalters/lean-genius/issues/21009

set -euo pipefail

ROOT="$(git rev-parse --show-toplevel)"
FIXTURE_ROOT="${ROOT}/tmp-tailwind-repro"
N="${1:-50}"
# Per-fixture volume knobs (mimic the real polluted state's file density)
JSON_PER_DIR="${JSON_PER_DIR:-40}"
LEAN_PER_DIR="${LEAN_PER_DIR:-30}"

if [[ -d "${FIXTURE_ROOT}" ]]; then
  echo "Fixture root already exists at ${FIXTURE_ROOT}. Run teardown.sh first." >&2
  exit 1
fi

echo "Creating ${N} synthetic polluted fixture directories under ${FIXTURE_ROOT}/..."
echo "  (JSON_PER_DIR=${JSON_PER_DIR}, LEAN_PER_DIR=${LEAN_PER_DIR})"

mkdir -p "${FIXTURE_ROOT}"

# Shared blobs (copied into each fixture, not symlinked, to force the scanner
# to actually open / read N copies as it would in the real polluted state).
JSON_BLOB='{"name":"x","tags":["foo","bar","baz"],"classNames":"text-red-500 bg-blue-200 p-4 m-2 grid grid-cols-3 flex items-center justify-between"}'

TSX_BLOB='import React from "react";
export const App = () => (
  <div className="flex items-center justify-center min-h-screen bg-gradient-to-r from-blue-500 to-purple-600">
    <h1 className="text-4xl font-bold text-white mb-4">Synthetic fixture</h1>
    <p className="text-lg text-gray-100">Tailwind v4 scanner stress test</p>
    <button className="mt-4 px-6 py-3 bg-yellow-400 text-black rounded-lg hover:bg-yellow-500 transition-colors">
      Click me
    </button>
    <div className="grid grid-cols-3 gap-4 p-8 bg-slate-800 rounded-2xl shadow-xl">
      <span className="text-pink-300 font-semibold">a</span>
      <span className="text-cyan-300 font-semibold">b</span>
      <span className="text-emerald-300 font-semibold">c</span>
    </div>
  </div>
);
'

HTML_BLOB='<!doctype html>
<html>
  <head><link rel="stylesheet" href="./index.css"/></head>
  <body>
    <div class="flex items-center justify-center min-h-screen bg-gradient-to-r from-blue-500 to-purple-600">
      <h1 class="text-4xl font-bold text-white">Fixture</h1>
    </div>
  </body>
</html>
'

CSS_BLOB='@import "tailwindcss";
.fixture { @apply bg-red-500 text-white p-4; }
'

LEAN_BLOB='import Mathlib.Tactic
namespace Fixture
theorem trivial_eq : 1 + 1 = 2 := by rfl
def foo (n : Nat) : Nat := n + 1
end Fixture
'

for i in $(seq 1 "${N}"); do
  dir="${FIXTURE_ROOT}/fixture-${i}"
  mkdir -p "${dir}/src" "${dir}/data" "${dir}/proofs/Proofs" "${dir}/nested/src" "${dir}/nested/proofs"

  printf '%s' "${HTML_BLOB}" > "${dir}/src/index.html"
  printf '%s' "${CSS_BLOB}"  > "${dir}/src/index.css"
  printf '%s' "${TSX_BLOB}"  > "${dir}/src/App.tsx"

  for j in $(seq 1 "${JSON_PER_DIR}"); do
    printf '%s' "${JSON_BLOB}" > "${dir}/data/blob-${j}.json"
  done

  for j in $(seq 1 "${LEAN_PER_DIR}"); do
    printf '%s' "${LEAN_BLOB}" > "${dir}/proofs/Proofs/Fixture${j}.lean"
  done

  # TRUE self-referential symlink: proofs/.lake -> . (the fixture dir itself).
  # This is the most aggressive form of the cycle observed in the real
  # polluted state. Most scanners that follow symlinks without inode tracking
  # will recurse infinitely through this; oxide v4.1.18 may or may not.
  ln -sf "." "${dir}/proofs/.lake"

  # Depth-2 fixture so the scanner descends further.
  printf '%s' "${HTML_BLOB}" > "${dir}/nested/src/index.html"
  printf '%s' "${TSX_BLOB}"  > "${dir}/nested/src/App.tsx"
  for j in $(seq 1 5); do
    printf '%s' "${LEAN_BLOB}" > "${dir}/nested/proofs/Nested${j}.lean"
  done
done

# Top-level marker so teardown is unambiguous.
echo "synthetic-pollution fixture for issue #21009" > "${FIXTURE_ROOT}/.fixture-marker"

total=$(find "${FIXTURE_ROOT}" -type f 2>/dev/null | wc -l | tr -d ' ')
echo "Created ${N} fixture directories (${total} files) under ${FIXTURE_ROOT}/."
echo "Run: ./scripts/repro/tailwind-scan-hang/teardown.sh  to remove."
