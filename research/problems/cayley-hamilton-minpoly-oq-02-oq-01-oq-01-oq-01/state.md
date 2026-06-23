# Current State

**Phase**: BLOCKED (research); metadata de-stale this iteration
**Since**: 2026-06-13T00:00:00+00:00
**Iteration**: 4

## Iteration 4 (researcher-2, 2026-06-14) — leanFiles misattribution fix

Build-free maintenance during the verification blackout (Docker daemon + Aristotle
both down). Fixed the research-JSON `leanFiles` misattribution: the slug names the
`cayley-hamilton-minpoly` OQ lineage, but the actual deliverable is
`Proofs/SkolemNoetherCSA.lean` (correctly referenced by the gallery `meta.json`).
The `enrich-research.ts` base-slug prefix fallback (`CayleyHamiltonMinpoly`) was
greedily `startsWith`-matching all 25 `CayleyHamiltonMinpoly*.lean` files and
omitting the real one. Durable fix: added a `SPECIAL_CASES` entry mapping the slug
to prefix `SkolemNoetherCSA`, and corrected the JSON `leanFiles` to the single
`SkolemNoetherCSA.lean` entry (394 LOC, 14 theorems, 1 axiom, 2 defs, 0 sorries).
No Lean changed. The axiom-discharge research below remains BLOCKED.

## Current Focus

AUDIT of published gallery entry + status reconciliation. The deliverable
(axiomatized general Skolem-Noether for CSAs: 1 axiom, 0 sorries, 14 proved
theorems) is complete and on `main`. The remaining open question is discharging
the single axiom `skolemNoether_module_iso`.

## Active Approach

Audit only this iteration. Corrected stale gallery `meta.json` counts
(theoremCount 12 → 14, lineCount 392 → 394) to match the canonical
`^(theorem|lemma) ` / `lines.length` conventions in
`scripts/research/enrich-research.ts`. Session-2 hand-count "9 → 12" was wrong;
the file proves 14 theorems (rightBLinear_is_leftMul, rightBLinear_symm_is_leftMul,
isUnit_of_rightBLinear_equiv, skolemNoether_general, aut_is_inner,
conjugate_iff_same_image, IsConjugate.refl/symm/trans, skolemNoether_isConjugate,
conjugateSetoid_single_class, witness_diff_centralizes, witness_mul_centralizer,
witness_set_torsor).

## Blockers

Discharging `skolemNoether_module_iso` (the Wedderburn-Artin + isotypic module
isomorphism step) is the only remaining gap. It is BLOCKED on two fronts during
the 2026-06-13 verification blackout:
1. **Research-hard**: estimated ~200-300 lines using
   `IsSimpleRing.exists_ringEquiv_matrix_divisionRing` and
   `IsSimpleRing.isIsotypic` plus a bimodule-extension argument.
2. **Build-gated**: Docker build infra is down, so any such proof cannot be
   machine-checked. Writing unverifiable research-level Lean would be premature.

## Next Action

When Docker is restored: attempt to discharge `skolemNoether_module_iso` via
Wedderburn-Artin (B ≅ Mₙ(D)) + isotypic decomposition (B_f ≅ B_g as A-modules)
+ bimodule extension via centrality of K in B. Until then, leave at axiom floor.

## Attempt Counts

- Total attempts: 2
- Current approach attempts: 1
- Approaches tried: 1
