# Session S2 ORIENT — Lean stub authored

**Date**: 2026-06-04
**Researcher**: researcher-1
**Phase transition**: S1_OBSERVE → S2_ORIENT
**Type**: Lean stub (scaffold-with-sorries) + state.md + JSON cursor update
**Iteration**: 2 (preceded by S1 OBSERVE iteration 1, merged 2026-06-02 via #22031)

## What this session adds

1. **New file `proofs/Proofs/AbelRuffiniGaloisExtensionsOQ06GaloisDirection.lean`**
   (119 LOC, 7 sorries, 0 axioms, 6 theorems):
   - 5 step-lemma stubs matching the S1 OBSERVE 5-step proof plan
     (Sylow uniqueness → P normal → P is p-cycle → N_{S_p}(P) ≅ AGL(1, p)
     → H ≤ N_{S_p}(P))
   - 1 file-level main theorem stub
     `primitive_solvable_subgroup_embeds_AGL1Z`
   - Imports parent `Proofs.AbelRuffiniGaloisExtensionsOQ06` plus
     `Mathlib.GroupTheory.Sylow` and
     `Mathlib.GroupTheory.Perm.Cycle.Type`.
   - Opens parent namespace `AbelRuffiniGaloisExtensionsOQ06` for
     `AGL1Z`, `AGL1Z.toPerm`, `AGL1Z.toPerm_injective` access.

2. **`proofs/Proofs.lean` auto-regenerated** via
   `./.lean/scripts/generate-proofs-imports.sh` to add the new
   `import Proofs.AbelRuffiniGaloisExtensionsOQ06GaloisDirection` line
   at the correct alphabetic position. Count line in script output:
   "Generated proofs/Proofs.lean with 2985 imports" (+1 from prior).

3. **`research/problems/abel-ruffini-galois-extensions-oq-06-galois-direction/state.md`**
   updated: Phase S1 → S2 ORIENT; Iteration 1 → 2; new Iteration 2
   section describing the S2 ORIENT deliverable; Next action rewritten
   for S3 ACT (discharge Step 1 first).

4. **`src/data/research/problems/abel-ruffini-galois-extensions-oq-06-galois-direction.json`**
   updated: top-level `phase` S1_OBSERVE → S2_ORIENT;
   `currentState.{phase, since, iteration, focus, nextAction, blockers,
   attemptCounts.total, lastUpdate}` refreshed.

5. **This session doc** under `sessions/`.

## What this session deliberately does NOT do

- **Discharge any sorries**. S2 ORIENT is a scaffold-with-sorries
  iteration per the S1 OBSERVE "Next action" specification (~80 LOC,
  ~6 sorries). The actual count is 119 LOC / 7 sorries (slightly
  over-budget on LOC because each step-lemma carries its own
  docstring, and over by 1 sorry because the main theorem is exposed
  as a file-level stub in addition to the 5 step lemmas).
- **Run Docker build**. The G9 lake self-loop blocker in the main repo
  (project memory `[[project_lake_self_loop_main_repo]]`) makes
  `./proofs/scripts/docker-build.sh` unusable from every sharing
  worktree. This PR ships under the documented "build pending — G9
  lake self-loop" qualifier, consistent with sibling research PRs
  (#21477, #21475, #21506, #22088).
- **Author gallery files**. `src/data/proofs/.../{meta.json, index.ts,
  annotations.json}` are deferred until at least one sorry is
  discharged (S5+) so that `meta.status` can claim `formalized` or
  `verified` honestly per the Axiom Integrity Policy. A `status:
  formalized` claim on a 7-sorry file is fine, but I'd rather wait
  until a discharged step lemma gives the gallery entry concrete
  pedagogical value.

## Bearer pre-flight (re-verified)

At lake-pinned SHA `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`, all
S1 OBSERVE bearers are intact (3-day gap, no Mathlib drift):

| Bearer | Path | Step |
|---|---|---|
| `Sylow.exists`, `Sylow.card_eq_multiplicity` | `Mathlib/GroupTheory/Sylow.lean` | 1 |
| `Sylow.normal_of_subsingleton` | `Mathlib/GroupTheory/Sylow.lean:724` | 2 |
| `Equiv.Perm.isCycle_of_prime_order''` | `Mathlib/GroupTheory/Perm/Cycle/Type.lean:412` | 3 |
| `Subgroup.normalizer` | `Mathlib/GroupTheory/Subgroup/Basic.lean` | 4-5 |
| `Subgroup.zpowers` | `Mathlib/GroupTheory/Subgroup/Basic.lean` | 4-5 |
| Parent `AGL1Z`, `AGL1Z.toPerm`, `AGL1Z.toPerm_injective` | `proofs/Proofs/AbelRuffiniGaloisExtensionsOQ06.lean` | 4-5 |

## Next action (S3 ACT)

Discharge **Step 1 (`sylow_p_unique`)** first because:

1. Cleanest bearer surface (`Sylow.exists` + `Sylow` API + divisibility).
2. Prerequisite for Step 2 (`sylow_p_normal` needs unique Sylow to
   extract `Sylow.normal_of_subsingleton`).
3. Argument follows Galois 1832 / Rotman 9.11 verbatim.

Estimated S3 ACT size: ~40-60 LOC additional (one theorem fully
discharged; 6 sorries remaining).

## Honesty / calibration

- 119 LOC, 7 sorries, 6 theorems, 0 axioms (verified by `wc -l` +
  `grep -c`).
- Gallery `status` will remain `formalized` (with `sorries: 7`) at
  minimum until S3+ ACT iterations discharge sorries. Per Axiom
  Integrity Policy: do not claim `verified` while any sorry exists.
- This is **not** a build-verified PR. The G9 blocker is documented
  and the qualifier matches the project's established sibling-PR
  precedent.
- Race-safety: no parallel sub-OQ work observed; the slug was
  scaffolded only 3 days ago (#22031 merged 2026-06-02).
