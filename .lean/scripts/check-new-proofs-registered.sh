#!/bin/bash
# check-new-proofs-registered.sh - Fail if a PR adds a proofs/Proofs/*.lean file
# that is NOT registered in proofs/Proofs.lean.
#
# Usage: ./.lean/scripts/check-new-proofs-registered.sh [BASE_REF]
#
#   BASE_REF   git ref to diff against (default: origin/main)
#
# Rationale (issue #31454): proofs/Proofs.lean is auto-generated and must list
# every file under proofs/Proofs/. A large pre-existing orphan backlog means a
# full `generate-proofs-imports.sh --check` would fail on every PR, so this
# guard is intentionally DIFF-BASED: it only flags *newly added* proof files
# that are missing their import line. This prevents the backlog from regrowing
# without blocking PRs on the historical orphans (tracked separately in #31454).

set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
REPO_ROOT="$(cd "$SCRIPT_DIR/../.." && pwd)"

PROOFS_LEAN="$REPO_ROOT/proofs/Proofs.lean"
BASE_REF="${1:-origin/main}"

if [[ ! -f "$PROOFS_LEAN" ]]; then
    echo "Error: $PROOFS_LEAN does not exist" >&2
    exit 1
fi

# Determine the merge-base so we only look at files this branch introduces.
if ! MERGE_BASE="$(git -C "$REPO_ROOT" merge-base "$BASE_REF" HEAD 2>/dev/null)"; then
    echo "Warning: could not compute merge-base against '$BASE_REF'; comparing directly." >&2
    MERGE_BASE="$BASE_REF"
fi

# Newly ADDED .lean files directly under proofs/Proofs/.
ADDED_FILES="$(git -C "$REPO_ROOT" diff --name-only --diff-filter=A "$MERGE_BASE" HEAD -- 'proofs/Proofs/*.lean' \
    | grep -E '^proofs/Proofs/[^/]+\.lean$' || true)"

if [[ -z "$ADDED_FILES" ]]; then
    echo "No newly added proofs/Proofs/*.lean files; nothing to check."
    exit 0
fi

MISSING=()
while IFS= read -r file; do
    [[ -z "$file" ]] && continue
    module="$(basename "$file" .lean)"
    if ! grep -qxF "import Proofs.$module" "$PROOFS_LEAN"; then
        MISSING+=("$module")
    fi
done <<< "$ADDED_FILES"

if [[ ${#MISSING[@]} -gt 0 ]]; then
    echo "Error: the following newly added proof file(s) are not registered in proofs/Proofs.lean:" >&2
    for m in "${MISSING[@]}"; do
        echo "  - proofs/Proofs/$m.lean  (missing: import Proofs.$m)" >&2
    done
    echo "" >&2
    echo "Regenerate the import list and commit it:" >&2
    echo "  ./.lean/scripts/generate-proofs-imports.sh" >&2
    exit 1
fi

echo "All newly added proof files are registered in proofs/Proofs.lean."
exit 0
