#!/bin/bash
#
# drift-repair.sh - Translate v4.28-era Aristotle output to the v4.31 pin
#
# The Aristotle proof-search backend vendors Mathlib v4.28 and normalizes every
# submission (and therefore every returned proof) to v4.28-era Lean. Our `main`
# pin is v4.31. Before an Aristotle solution can go GREEN in the gallery it must
# be drift-repaired to v4.31. This script applies the confident, pure-rename
# subset of research/toolchain-v4.31-rename-map.md (§1) to a Lean file and
# WARNS about names that need human/Doctor attention (v428-to-v431-flags.tsv).
#
# It does NOT verify the build — that is verify-v431-build.sh's job (the
# in-container v4.31 exit-0 gate). Renaming makes the proof *elaborate-able*;
# only the build gate proves it actually GOES GREEN. See issue #38622 and
# research/ARISTOTLE-WORKFLOW.md ("Boundary translation").
#
# Usage:
#   ./drift-repair.sh <file.lean>            # repair in place (writes <file>.bak)
#   ./drift-repair.sh --check <file.lean>    # report only, do not modify (exit 0)
#   ./drift-repair.sh --stdout <file.lean>   # write repaired file to stdout
#   ./drift-repair.sh --no-backup <file>     # repair in place without a .bak
#   ./drift-repair.sh --quiet <file>         # suppress the per-rule log
#
# Exit codes:
#   0  success (repairs applied, or nothing to do)
#   1  usage / IO error
#   2  --check found flagged names needing manual review (advisory; the
#      retrieve/integrate path treats this as "integrate but do not mark
#      verified" rather than a hard failure)
#
# Matching semantics: each old identifier is matched only as a whole token that
# is not preceded by a word char or `.` and not followed by a word char, `.`,
# `'`, or subscript-zero. This makes qualification-adds (bare -> Namespaced)
# and `₀`-suffix adds idempotent and protects primed sibling lemmas, so the
# script is safe to run on a file that is already partly v4.31.

set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
RENAMES_FILE="$SCRIPT_DIR/v428-to-v431-renames.tsv"
FLAGS_FILE="$SCRIPT_DIR/v428-to-v431-flags.tsv"

# Colors (disabled when stdout is not a tty)
if [[ -t 1 ]]; then
    RED='\033[0;31m'; GREEN='\033[0;32m'; YELLOW='\033[1;33m'; CYAN='\033[0;36m'; NC='\033[0m'
else
    RED=''; GREEN=''; YELLOW=''; CYAN=''; NC=''
fi

MODE="inplace"     # inplace | check | stdout
BACKUP=true
QUIET=false
INPUT=""

while [[ $# -gt 0 ]]; do
    case "$1" in
        --check)     MODE="check"; shift ;;
        --stdout)    MODE="stdout"; shift ;;
        --no-backup) BACKUP=false; shift ;;
        --quiet)     QUIET=true; shift ;;
        -h|--help)
            sed -n '2,40p' "$0"; exit 0 ;;
        --) shift; break ;;
        -*) echo "Unknown option: $1" >&2; exit 1 ;;
        *)  INPUT="$1"; shift ;;
    esac
done
[[ -z "$INPUT" && $# -gt 0 ]] && INPUT="$1"

if [[ -z "$INPUT" ]]; then
    echo "Usage: $0 [--check|--stdout|--no-backup|--quiet] <file.lean>" >&2
    exit 1
fi
if [[ ! -f "$INPUT" ]]; then
    echo -e "${RED}ERROR:${NC} file not found: $INPUT" >&2
    exit 1
fi
if [[ ! -f "$RENAMES_FILE" ]]; then
    echo -e "${RED}ERROR:${NC} rename table missing: $RENAMES_FILE" >&2
    exit 1
fi

log() { [[ "$QUIET" == true ]] && return 0; echo -e "$@" >&2; }

# Apply one whole-identifier rename to a file, in place. Idempotent for
# qualification-adds and ₀-suffix adds. Uses perl for portable Unicode-aware
# lookbehind/lookahead (BSD sed on macOS lacks \b and PCRE lookaround).
apply_rename() {
    local file="$1" old="$2" new="$3"
    OLD="$old" NEW="$new" perl -CSD -MEncode -i -pe '
        BEGIN { $o = decode_utf8($ENV{OLD}); $n = decode_utf8($ENV{NEW}); }
        s/(?<![\w.])\Q$o\E(?![\w.\x{2080}\x{27}])/$n/g;
    ' "$file"
}

# Count whole-identifier occurrences of a name in a file (same boundaries as
# apply_rename), so we can report only genuine hits.
count_occurrences() {
    local file="$1" name="$2"
    NAME="$name" perl -CSD -MEncode -0777 -ne '
        BEGIN { $n = decode_utf8($ENV{NAME}); }
        my $c = () = /(?<![\w.])\Q$n\E(?![\w.\x{2080}\x{27}])/g;
        print $c;
    ' "$file"
}

# --- Work on a scratch copy so --check / --stdout never touch the input ---
work="$(mktemp "${TMPDIR:-/tmp}/drift-repair-XXXXXX.lean")"
cleanup() { rm -f "$work"; }
trap cleanup EXIT
cp "$INPUT" "$work"

applied_total=0
declare -a applied_lines=()

# --- Pass 1: apply the safe pure renames ---
while IFS=$'\t' read -r old new || [[ -n "$old" ]]; do
    # strip comments / blanks / whitespace
    old="${old%%$'\r'}"
    [[ -z "$old" || "$old" == \#* ]] && continue
    new="${new%%$'\r'}"
    # trim surrounding whitespace
    old="$(printf '%s' "$old" | sed -E 's/^[[:space:]]+//; s/[[:space:]]+$//')"
    new="$(printf '%s' "$new" | sed -E 's/^[[:space:]]+//; s/[[:space:]]+$//')"
    [[ -z "$old" || -z "$new" ]] && continue

    local_hits="$(count_occurrences "$work" "$old")"
    if [[ "${local_hits:-0}" -gt 0 ]]; then
        apply_rename "$work" "$old" "$new"
        applied_total=$((applied_total + local_hits))
        applied_lines+=("  ${GREEN}rename${NC} ($local_hits) $old ${CYAN}->${NC} $new")
    fi
done < "$RENAMES_FILE"

# --- Pass 2: scan for flagged names (manual review) ---
flagged_total=0
declare -a flagged_lines=()
if [[ -f "$FLAGS_FILE" ]]; then
    while IFS=$'\t' read -r name reason || [[ -n "$name" ]]; do
        name="${name%%$'\r'}"
        [[ -z "$name" || "$name" == \#* ]] && continue
        name="$(printf '%s' "$name" | sed -E 's/^[[:space:]]+//; s/[[:space:]]+$//')"
        [[ -z "$name" ]] && continue
        reason="$(printf '%s' "$reason" | sed -E 's/^[[:space:]]+//; s/[[:space:]]+$//')"
        local_hits="$(count_occurrences "$work" "$name")"
        if [[ "${local_hits:-0}" -gt 0 ]]; then
            flagged_total=$((flagged_total + 1))
            flagged_lines+=("  ${YELLOW}review${NC} ($local_hits) $name — ${reason:-see rename-map §5}")
        fi
    done < "$FLAGS_FILE"
fi

# --- Report ---
log "${CYAN}drift-repair${NC} $(basename "$INPUT"): applied ${applied_total} rename-hit(s), ${flagged_total} flag(s)"
if [[ "${#applied_lines[@]}" -gt 0 ]]; then
    for l in "${applied_lines[@]}"; do log "$l"; done
fi
if [[ "${#flagged_lines[@]}" -gt 0 ]]; then
    log "${YELLOW}Manual review needed (v4.28->v4.31 changes beyond a blind rename):${NC}"
    for l in "${flagged_lines[@]}"; do log "$l"; done
    log "${YELLOW}Recipes: research/toolchain-v4.31-rename-map.md (§2/§3/§4/§5)${NC}"
fi

# --- Emit result per mode ---
case "$MODE" in
    check)
        # report-only; never modify input
        [[ "$flagged_total" -gt 0 ]] && exit 2
        exit 0
        ;;
    stdout)
        cat "$work"
        [[ "$flagged_total" -gt 0 ]] && exit 2
        exit 0
        ;;
    inplace)
        if [[ "$applied_total" -gt 0 ]]; then
            [[ "$BACKUP" == true ]] && cp "$INPUT" "$INPUT.drift.bak"
            cp "$work" "$INPUT"
        fi
        [[ "$flagged_total" -gt 0 ]] && exit 2
        exit 0
        ;;
esac
