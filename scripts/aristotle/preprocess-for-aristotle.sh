#!/bin/bash
#
# preprocess-for-aristotle.sh - Preprocess a Lean file for Aristotle submission
#
# Takes a Lean file, creates a preprocessed temp copy with:
#   - /-! docstrings converted to /- (Aristotle parser compat)
#   - Standard Harmonic-style set_option block injected after imports if missing
#     (applies to all files; idempotent if already present)
#
# Additional checks for *StatementOnly.lean files (Harmonic format):
#   - Warns if there is no /- informal-problem block at the top of the file
#   - Rejects (exit 1) if the file has more than one top-level
#     `theorem|lemma ... := by sorry` (Harmonic recommends one theorem per submission)
#
# Rejects (exit 1):
#   - Files with definition sorries (unfixable, blocks dependent theorems)
#   - Files where ALL sorries are placeholder "True" theorems (no value)
#   - Files with zero sorries after preprocessing (nothing to prove)
#   - *StatementOnly.lean files with multiple top-level theorem/lemma sorries
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

# Detect whether this file follows the Harmonic StatementOnly convention.
# Convention: filename ends with StatementOnly.lean (e.g. FooStatementOnly.lean)
IS_STATEMENT_ONLY=false
if [[ "$(basename "$INPUT_FILE")" == *StatementOnly.lean ]]; then
    IS_STATEMENT_ONLY=true
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

# StatementOnly: enforce one theorem-with-sorry per file.
# A "theorem/lemma sorry" is a top-level declaration that ends with `sorry`,
# which we approximate by `theorem|lemma ... := by sorry` (the canonical form
# Harmonic uses). We also allow the bare-term form `:= sorry`.
if [[ "$IS_STATEMENT_ONLY" == true ]]; then
    multi_sorry_count=$(count_matches "^(theorem|lemma)[[:space:]].*:=[[:space:]]*(by[[:space:]]+)?sorry[[:space:]]*$" "$INPUT_FILE")
    # Fall back to the broader pattern if the strict form turned up zero — this
    # covers multi-line declarations where `:= by sorry` is on its own line.
    if [[ "$multi_sorry_count" -eq 0 ]]; then
        multi_sorry_count="$total_thm_sorry"
    fi
    if [[ "$multi_sorry_count" -gt 1 ]]; then
        echo "REJECT: multi-sorry file (Harmonic recommends one theorem per submission)" >&2
        echo "  Found $multi_sorry_count theorem/lemma sorries in $(basename "$INPUT_FILE")" >&2
        grep -nE "^(theorem|lemma)[[:space:]].*sorry" "$INPUT_FILE" >&2 || true
        exit 1
    fi
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

# Transform 2: Inject the standard Harmonic set_option block if absent.
# Detection: we look for `set_option maxHeartbeats 0` as the canonical marker
# (it is the most important option in the block and the most likely to be
# missing).  If absent, we insert the full block after the last `import` line
# and before any `namespace`/`open`/`set_option`/`noncomputable section` lines.
if ! grep -qE "^set_option[[:space:]]+maxHeartbeats[[:space:]]+0([[:space:]]|$)" "$tmp_file"; then
    # Locate the last `import` line. If there is none, insert at the top of the
    # file (line 0 — i.e. as a leading block).
    last_import_line=$(grep -nE "^import[[:space:]]" "$tmp_file" | tail -1 | cut -d: -f1 || true)
    insert_after="${last_import_line:-0}"

    # Write the set_option block to a sidecar file so we can read it from
    # awk without dealing with multi-line shell quoting (awk -v rejects
    # embedded newlines in variable values).
    block_file="$tmp_dir/.set_option_block"
    cat > "$block_file" <<'BLOCK_EOF'

set_option maxHeartbeats 0
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128
set_option pp.fullNames true
set_option pp.structureInstances true
set_option relaxedAutoImplicit false
set_option autoImplicit false
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true
set_option linter.all false
BLOCK_EOF

    awk -v insert_after="$insert_after" -v block_file="$block_file" '
        BEGIN {
            block = ""
            while ((getline line < block_file) > 0) {
                block = block line "\n"
            }
            close(block_file)
        }
        { print }
        NR == insert_after {
            # Strip the trailing newline added by the loop above so we do not
            # produce a stray blank line at the end of the block.
            sub(/\n$/, "", block)
            print block
        }
    ' "$tmp_file" > "$tmp_file.tmp"
    mv "$tmp_file.tmp" "$tmp_file"
    rm -f "$block_file"
    echo "PREPROCESS: Injected standard set_option block after line $insert_after" >&2
    changes_made=$((changes_made + 1))
fi

# Warn (don't reject) if there is no informal-problem `/-` block at the top.
# "At the top" = before the first declaration (import/namespace/open/theorem/
# def/etc.). We look for a `/-` (but not `/-!`) opening sequence in the first
# few non-blank lines.
has_informal_block=false
# Scan up to the first 80 lines for an early `/-` block opener that precedes
# the first import. We accept any `/-` on a line by itself or starting a line.
first_decl_line=$(grep -nE "^(import|namespace|open|theorem|lemma|def|axiom|structure|class|instance|inductive|abbrev|noncomputable[[:space:]]+section|section)" "$tmp_file" | head -1 | cut -d: -f1 || true)
if [[ -z "$first_decl_line" ]]; then
    first_decl_line=80
fi
# Look at lines 1..first_decl_line for `/-` (not `/-!`)
if awk -v limit="$first_decl_line" 'NR <= limit && /^[[:space:]]*\/-([^!]|$)/ { found=1; exit } END { exit !found }' "$tmp_file"; then
    has_informal_block=true
fi

if [[ "$has_informal_block" != true ]]; then
    echo "PREPROCESS: WARN no informal-problem block at top" >&2
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
