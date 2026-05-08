# Current State

**Phase**: ACT
**Since**: 2026-05-08T06:00:00Z
**Iteration**: 3

## Current Focus

Closing the fourth corner of the Σ₁/Π₁/Σ₂/Π₂ square. Iterations 1 & 2
established Σ₁ (open), Π₂ (Koenigsmann), and the Σ₁/Π₁ duality. This
iteration adds Σ₂ definability, the precise dual of Σ₁ ⊆ Π₂ (i.e.
Π₁ ⊆ Σ₂), the Σ₂/Π₂ duality, and the unconditional Σ₂(ℚ\ℤ) corollary
of Koenigsmann.

## Active Approach

S3 — Σ₂ definability + Σ₂/Π₂ duality:

1. Define `IsExistentialUniversalDefinition` (Σ₂, ∃∀ definability).
2. Prove `codiophantine_implies_existentialUniversal` (Π₁ ⊆ Σ₂):
   add a dummy existential block to a Π₁ formula. Axiom-free.
3. Prove `existentialUniversal_iff_universalExistential_complement`:
   the higher-level analog of the Σ₁/Π₁ duality. Both directions use
   `Classical.byContradiction`.
4. Add `universalExistentialDefinition_iff_of_pred_iff` (Π₂ class is
   invariant under propositional equivalence of the predicate) as a
   pure logical congruence helper.
5. Derive `koenigsmann_implies_complement_existentialUniversal`: the
   complement ℚ\ℤ is Σ₂-definable in ℚ, as a corollary of Koenigsmann
   via the Σ₂/Π₂ duality + the predicate-equivalence bridge. No new
   axiom.

Net new content: 1 definition, 4 theorems, 0 new axioms.
Updated to total: 8 definitions, 13 theorems, 1 axiom, 0 sorries, 462
lines.

## Build Status

Docker build: PASSED ✅ (3 jobs, exit code 0). Verified the new
section compiles cleanly against the Lean-core-only design (no Mathlib
import). The two `Classical.byContradiction` patterns from iteration 2
extend smoothly to Σ₂/Π₂ — both directions of the new duality, and the
`hbridge` (`IntSubset q ↔ ¬ NotIntSubset q`) used in the corollary.

The `NotIntSubset` definition is non-`@[irreducible]`, so Lean's
unifier auto-unfolds `¬ NotIntSubset q` to `¬ ¬ IntSubset q` where
needed (e.g. inside `hbridge`'s `Classical.byContradiction` step).

## Blockers

None.

## Next Action

Commit, push, create PR.

If S3 lands cleanly, S4+ candidates:
- Σ₂ ⊆ Π₂'s ¬¬-shadow — the technical clarification that `Σ₂(S)` and
  `Π₂(¬¬S) = Π₂(S)` agree on `Prop`-classical predicates; would tighten
  the predicate-equivalence bridge into a stronger congruence lemma.
- Σ₁ × Π₁ closure properties (under finite union/intersection) — needs
  `Rat.mul_eq_zero` / sum-of-squares lemma which would require either
  a Mathlib import or a hand-rolled proof from Lean core.
- Π₁ ⊆ Π₂ via the `a ≠ 0 ⟺ ∃ z, a·z = 1` polynomial-inversion trick —
  needs the same Rat field arithmetic.
- Daans 2021 (10-quantifier reduction) as a separate axiomatized
  witness refining `koenigsmann_2016_universal` — would add 1 new axiom
  but improve quantitative content; defer until further duality / closure
  work lands.

## Attempt Counts

- Total attempts: 3
- Current approach attempts: 1 (S3 — Σ₂/Π₂ duality, first attempt OK)
- Approaches tried: 2 (S2 — Σ₁/Π₁ duality, S3 — Σ₂/Π₂ duality)
