#!/bin/bash
# check-new-proofs-registered.sh - DEPRECATED no-op (always succeeds).
#
# Proof modules under proofs/Proofs/ no longer need to be registered in
# proofs/Proofs.lean: they are discovered automatically by the Lake `globs`
# directive in proofs/lakefile.toml (`["Proofs", "Proofs.*"]`).
#
# The old registration requirement is exactly what forced every new-proof PR to
# edit the single shared import list, creating the merge-conflict backlog. There
# is nothing left to check.

set -euo pipefail

echo "Proof modules are glob-discovered (proofs/lakefile.toml); registration check is a no-op."
exit 0
