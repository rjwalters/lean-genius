#!/usr/bin/env bash
# scripts/lint/check-renamed-namespace-refs.sh
#
# Catch in-body references to stale namespace prefixes left behind after
# a `sed`-style namespace rename (e.g., `namespace Erdos741` -> `namespace
# Erdos741APN_I`). Naive renames anchor on `^namespace`/`^end` lines and
# silently miss tactic-position references like:
#
#   delta Erdos741.foo at h
#   simp_all [Erdos152.D_set]
#   change Erdos26.X_seq
#   unfold Erdos138.thing
#
# Each leftover surfaces as a Lean error at docker-build time, costing a
# Doctor cycle per file. This script catches them pre-PR.
#
# Motivating PRs (epic #20732, AlphaProof Nexus port):
#   - #20836, #20837, #20838, #20839 — three Doctor cycles burned on the
#     same root cause.
#
# Usage:
#   scripts/lint/check-renamed-namespace-refs.sh <file.lean> [<file.lean> ...]
#   scripts/lint/check-renamed-namespace-refs.sh proofs/Proofs/*.lean
#
# Behavior:
#   - For each file, collect every `^namespace <X>` declared in the file
#     (call this set LOCAL_NS).
#   - For each local namespace, compute a "stripped base" by removing
#     trailing rename suffixes (APN_I, APN_II, APN, _Tenenbaum, Nexus,
#     PartI, PartII, ...). Example: Erdos741APN_I -> Erdos741.
#   - If the stripped base differs from the declared namespace AND is not
#     itself one of the declared namespaces, scan the file body for any
#     reference of the form `\b<base>\.[A-Za-z_]`. Each match is a likely
#     stale reference from the pre-rename source.
#   - Comment-strip (`--` line comments) before scanning to reduce noise.
#     `^namespace <X>` and `^end <X>` declaration/closer lines are skipped.
#
# Exit codes:
#   0 — no stale references found in any file
#   1 — at least one stale reference found (printed to stderr)
#   2 — usage error
#
# Limitations (v1, by design):
#   - grep-based, not a full Lean parser. Block comments (`/- ... -/`) and
#     string literals are NOT stripped; on real APN files this catches >90%
#     of cases (see issue #20847).
#   - Only flags suspects derived from the file's own declared namespaces.
#     Cross-file stale refs (file declares `Foo`, references `Bar.x` where
#     `Bar` lives elsewhere) are out of scope.
#   - Targets POSIX-ish bash 3.2+ (macOS default) — avoids `mapfile`.
#
# See also: issue #20847.

set -u

if [ "$#" -eq 0 ]; then
  echo "usage: $0 <file.lean> [<file.lean> ...]" >&2
  exit 2
fi

# Suffixes we strip when computing the "old base" namespace name from a
# declared (renamed) namespace. Order matters: longest first so we strip
# `APN_I` before `APN`. Adjust here when new rename patterns appear.
strip_suffix() {
  local s="$1"
  # Iterate: keep stripping any recognized suffix until none match.
  local prev=""
  while [ "$s" != "$prev" ]; do
    prev="$s"
    s="${s%APN_I}"
    s="${s%APN_II}"
    s="${s%APN_Tenenbaum}"
    s="${s%APN}"
    s="${s%Nexus}"
    s="${s%PartI}"
    s="${s%PartII}"
    s="${s%_I}"
    s="${s%_II}"
  done
  printf '%s' "$s"
}

status=0

for file in "$@"; do
  if [ ! -f "$file" ]; then
    echo "$0: not a file: $file" >&2
    status=2
    continue
  fi

  # All namespaces declared in this file. Newline-separated string (bash
  # 3.2 compatible — avoid mapfile and array reads from process subs).
  local_ns_str="$(awk '/^namespace [A-Za-z_]/ { print $2 }' "$file" | sort -u)"
  if [ -z "$local_ns_str" ]; then
    continue
  fi

  # Compute candidate "old base" namespaces (one per line).
  bases_str=""
  while IFS= read -r ns; do
    [ -z "$ns" ] && continue
    base="$(strip_suffix "$ns")"
    if [ -z "$base" ] || [ "$base" = "$ns" ]; then
      continue
    fi
    # Skip if base is itself a declared namespace in this file (legitimate).
    if printf '%s\n' "$local_ns_str" | grep -qxF "$base"; then
      continue
    fi
    bases_str="$bases_str$base"$'\n'
  done <<EOF
$local_ns_str
EOF

  # Dedup bases.
  bases_str="$(printf '%s' "$bases_str" | awk 'NF' | sort -u)"
  if [ -z "$bases_str" ]; then
    continue
  fi

  # local_ns rendered space-separated for the diagnostic header.
  local_ns_render="$(printf '%s' "$local_ns_str" | tr '\n' ' ' | sed 's/ *$//')"

  while IFS= read -r base; do
    [ -z "$base" ] && continue
    # Scan file body for `\bbase\.[A-Za-z_]`.
    # Strip `--` line comments (everything from `--` to end of line) before
    # matching, and exclude `^namespace base` / `^end base` declarations.
    # Use awk to keep line numbers intact.
    matches="$(
      awk -v base="$base" '
        {
          line = $0
          # Strip "--" line comments (simple textual strip, no string awareness).
          idx = index(line, "--")
          if (idx > 0) line = substr(line, 1, idx - 1)
          # Skip namespace/end declaration lines for this base.
          if (line ~ ("^namespace[[:space:]]+" base "([[:space:]]|$)")) next
          if (line ~ ("^end[[:space:]]+" base "([[:space:]]|$)")) next
          # Look for `\bbase\.[A-Za-z_]`.
          pat = "(^|[^A-Za-z0-9_])" base "\\.[A-Za-z_]"
          if (match(line, pat)) {
            print FILENAME ":" NR ":" $0
          }
        }
      ' "$file"
    )"

    if [ -n "$matches" ]; then
      echo "$file: in-body references to stale namespace '$base' (declared namespaces: $local_ns_render):" >&2
      printf '%s\n' "$matches" >&2
      status=1
    fi
  done <<EOF
$bases_str
EOF
done

exit "$status"
