#!/bin/bash
# generate-proofs-imports.sh - DEPRECATED no-op.
#
# proofs/Proofs.lean is no longer a flat import list. Modules under
# proofs/Proofs/ are discovered automatically by the Lake `globs` directive in
# proofs/lakefile.toml (`["Proofs", "Proofs.*"]`). The old auto-generated import
# list was a merge-conflict bottleneck — every new-proof PR edited it.
#
# This script is kept only so existing callers (e.g. the deployer) don't break.
# It rewrites proofs/Proofs.lean to the static header form and otherwise does
# nothing. `--check` always succeeds.
#
# Usage: ./.lean/scripts/generate-proofs-imports.sh [--check]

set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
REPO_ROOT="$(cd "$SCRIPT_DIR/../.." && pwd)"
OUTPUT_FILE="$REPO_ROOT/proofs/Proofs.lean"

read -r -d '' STATIC_HEADER <<'EOF' || true
-- Root module for the `Proofs` Lean library.
--
-- Individual proof modules under `proofs/Proofs/` are discovered automatically
-- by the Lake `globs` directive in `proofs/lakefile.toml` (`["Proofs", "Proofs.*"]`).
--
-- Do NOT add per-file `import Proofs.X` lines here. This file used to be an
-- auto-generated flat import list of every proof, which made it a merge-conflict
-- bottleneck: every new-proof PR appended a line, so concurrent PRs conflicted
-- en masse. It is intentionally kept empty of imports.
EOF

if [[ "${1:-}" == "--check" ]]; then
    # Modules are globbed; nothing to verify. Always in sync.
    echo "proofs/Proofs.lean is glob-discovered; registration check is a no-op."
    exit 0
fi

printf '%s\n' "$STATIC_HEADER" > "$OUTPUT_FILE"
echo "Wrote static proofs/Proofs.lean header (modules are discovered by lakefile glob)."
