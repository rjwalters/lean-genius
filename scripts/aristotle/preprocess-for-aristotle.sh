#!/bin/bash
#
# preprocess-for-aristotle.sh - Preprocess a Lean file for Aristotle submission
#
# Takes a Lean file, creates a preprocessed temp copy with:
#   - /-! docstrings converted to /- (Aristotle parser compat)
#
# Rejects (exit 1):
#   - Files with definition sorries (unfixable, blocks dependent theorems)
#   - Files where ALL sorries are placeholder "True" theorems (no value)
#   - Files with zero sorries after preprocessing (nothing to prove)
#
# Output:
#   Last line of stdout = path to preprocessed temp file
#   Stderr = log of changes made
#
# Usage:
#   ./preprocess-for-aristotle.sh path/to/file.lean
#   preprocessed_file=$(./preprocess-for-aristotle.sh path/to/file.lean | tail -1)
#

set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
PROJECT_ROOT="$(cd "$SCRIPT_DIR/../.." && pwd)"

if [[ $# -lt 1 ]]; then
    echo "Usage: $0 <lean-file>" >&2
    exit 1
fi

INPUT_FILE="$1"

if [[ ! -f "$INPUT_FILE" ]]; then
    echo "ERROR: File not found: $INPUT_FILE" >&2
    exit 1
fi

# Helper: count grep matches safely (grep -c exits 1 on 0 matches)
count_matches() {
    grep -cE "$1" "$2" 2>/dev/null || true
}

# --- Pre-rejection checks (on original file) ---

# Check for definition sorries
def_sorry_count=$(count_matches "^(noncomputable )?def[[:space:]].*(:=.*sorry|sorry$)" "$INPUT_FILE")
if [[ "$def_sorry_count" -gt 0 ]]; then
    echo "REJECT: File has $def_sorry_count definition sorries (Aristotle cannot handle these)" >&2
    grep -nE "^(noncomputable )?def[[:space:]].*(:=.*sorry|sorry$)" "$INPUT_FILE" >&2 || true
    exit 1
fi

# Check if ALL theorem/lemma sorries are placeholder "True" theorems
total_thm_sorry=$(count_matches "^(theorem|lemma)[[:space:]].*sorry" "$INPUT_FILE")
true_thm_sorry=$(count_matches "^(theorem|lemma)[[:space:]].*:[[:space:]]*True[[:space:]]*:=" "$INPUT_FILE")

if [[ "$total_thm_sorry" -gt 0 && "$total_thm_sorry" -eq "$true_thm_sorry" ]]; then
    echo "REJECT: All $total_thm_sorry theorem sorries are placeholder 'True' theorems (no value)" >&2
    exit 1
fi

# --- Create preprocessed copy ---

tmp_dir=$(mktemp -d "${TMPDIR:-/tmp}/aristotle-preprocess-XXXXXX")
tmp_file="$tmp_dir/$(basename "$INPUT_FILE")"
cleanup_tmp_dir() {
    rm -rf "$tmp_dir"
}
trap cleanup_tmp_dir EXIT

cp "$INPUT_FILE" "$tmp_file"

# Copy Lean project files so aristotlelib recognizes it as a valid project
cp "$PROJECT_ROOT/proofs/lakefile.toml" "$tmp_dir/"
cp "$PROJECT_ROOT/proofs/lean-toolchain" "$tmp_dir/"

changes_made=0

# Transform 1: Convert /-! docstrings to /- (Aristotle parser compat)
docstring_count=$(count_matches '/-!' "$tmp_file")
if [[ "$docstring_count" -gt 0 ]]; then
    sed 's|/-!|/-|g' "$tmp_file" > "$tmp_file.tmp"
    mv "$tmp_file.tmp" "$tmp_file"
    echo "PREPROCESS: Converted $docstring_count /-! docstrings to /-" >&2
    changes_made=$((changes_made + docstring_count))
fi

# --- Post-preprocessing validation ---

# Count sorries in preprocessed file
post_sorry_count=$(count_matches "sorry" "$tmp_file")

if [[ "$post_sorry_count" -eq 0 ]]; then
    echo "REJECT: Zero sorries after preprocessing (nothing for Aristotle to prove)" >&2
    rm -f "$tmp_file"
    exit 1
fi

# Re-check: all True placeholders after preprocessing?
post_thm_sorry=$(count_matches "^(theorem|lemma)[[:space:]].*sorry" "$tmp_file")
post_true_sorry=$(count_matches "^(theorem|lemma)[[:space:]].*:[[:space:]]*True[[:space:]]*:=" "$tmp_file")

if [[ "$post_thm_sorry" -gt 0 && "$post_thm_sorry" -eq "$post_true_sorry" ]]; then
    echo "REJECT: After preprocessing, all $post_thm_sorry theorem sorries are placeholder 'True' theorems" >&2
    rm -f "$tmp_file"
    exit 1
fi

# --- Output ---

if [[ "$changes_made" -eq 0 ]]; then
    echo "PREPROCESS: No changes needed (file already compatible)" >&2
fi

echo "PREPROCESS: Result has $post_sorry_count sorries to attempt" >&2

# Last line = path to preprocessed file (caller captures this)
trap - EXIT
echo "$tmp_file"
