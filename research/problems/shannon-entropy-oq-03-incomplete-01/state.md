# Research State: shannon-entropy-oq-03-incomplete-01

## Current State
**Phase**: COMPLETE (build repair + status correction)
**Path**: full
**Since**: 2026-07-07
**Iteration**: 1
**Status**: resolved — gallery entry now builds and is VERIFIED

## Outcome (researcher-9, 2026-07-07)

The task as originally written ("only the main theorem at line 303 remains as
`sorry`") was stale: `Proofs/ShannonEntropySSA.lean` had **no sorry** but was a
**masked broken build** (merged without Lean CI — math PRs bypass it). Building
`docker-build.sh Proofs.ShannonEntropySSA` surfaced a cascade of ~11 errors:

- 5× `... has already been declared` — the file redeclared `marginalXY`,
  `marginalYZ`, `entropy_chain_rule`, `subadditivity`, `strong_subadditivity`
  (namespace `InformationTheory`) **while also `import`ing the parent
  `Proofs/ShannonEntropy.lean` that already declares all of them**.
- Cascading parse error (calc `:=` at L306) and `linarith` failures (L511/524)
  downstream of the poisoned `strong_subadditivity` elaboration.

Root cause: the file was a self-contained duplicate of infrastructure the parent
file **already proves cleanly (0 sorries, 0 axioms, builds)**, plus a spurious
`import Proofs.ShannonEntropy` that made every duplicated name collide.

### Fix
Replaced the 526-line broken duplicate with a 92-line file that reuses the
parent's verified development:
- `strong_subadditivity` — re-exported from `InformationTheory.strong_subadditivity`
  (H(X,Y,Z)+H(Y) ≤ H(X,Y)+H(Y,Z));
- `conditioning_reduces_entropy_general` — H(X|Y,Z) ≤ H(X|Y);
- `conditional_mi_nonneg` — I(X;Z|Y) ≥ 0.

The two 3-variable corollaries are genuinely new (absent from the parent). New
namespace `InformationTheory.SSA` avoids all collisions. **VERIFIED**:
`docker-build.sh Proofs.ShannonEntropySSA` → ✔ [7744/7744] built (0 sorries,
inherits the parent's axiom-free proof; foundational trio only, no
`native_decide`). Gallery meta upgraded `formalized` → `verified`; sections /
theorem counts / line count synced to the new file.

The full self-contained SSA proof (marginals, chain rule, subadditivity, the KL
telescoping argument) is preserved in the parent `Proofs/ShannonEntropy.lean`, so
no mathematical content is lost.

## Blockers
None.

## Next Action
None — resolved. PR opened.
