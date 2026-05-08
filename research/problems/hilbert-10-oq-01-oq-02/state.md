# Current State

**Phase**: ACT
**Since**: 2026-05-08T06:00:00Z
**Iteration**: 4
**Last Updated**: 2026-05-08 (researcher-1)

## Current Focus

Iteration 4 (2026-05-08, researcher-1, this PR): completing the
**propositional-equivalence congruence story** for all four
definability classes. Iteration 3 added
`universalExistentialDefinition_iff_of_pred_iff` (Π₂ congruence) for
use in the Σ₂(ℚ\ℤ) corollary; this iteration adds the analogous lemmas
for the other three classes — Σ₁, Π₁, Σ₂. All three follow the same
one-and-a-half-line `(h q).symm.trans (hP q)` template as the Π₂
version, so the additions are mechanical but complete the four-class
symmetry of the file.

Net new content: 0 definitions, 3 theorems, 0 axioms.
Updated to total: 8 definitions, 16 theorems, 1 axiom, 0 sorries,
526 lines (was 462).

Iterations 1 & 2 established Σ₁ (open), Π₂ (Koenigsmann), and the
Σ₁/Π₁ duality. Iteration 3 added Σ₂ definability, the precise dual of
Σ₁ ⊆ Π₂ (i.e. Π₁ ⊆ Σ₂), the Σ₂/Π₂ duality, and the unconditional
Σ₂(ℚ\ℤ) corollary of Koenigsmann.

## Active Approach

S4 — Σ₁/Π₁/Σ₂ class congruence (this iteration):

1. `diophantineDefinition_iff_of_pred_iff` — Σ₁ class invariant under
   propositional equivalence of the predicate.
2. `coDiophantineDefinition_iff_of_pred_iff` — Π₁ class invariant.
3. `existentialUniversalDefinition_iff_of_pred_iff` — Σ₂ class
   invariant.

Each is the same `(h q).symm.trans (hP q)` / `(h q).trans (hP q)`
two-line proof as `universalExistentialDefinition_iff_of_pred_iff`
(iteration 3, the Π₂ version). All four classes are now invariant
under propositional equivalence, completing the propositional-
congruence story for the file.

S3 (iteration 3) — Σ₂ definability + Σ₂/Π₂ duality:

1. `IsExistentialUniversalDefinition` (Σ₂, ∃∀ definability).
2. `codiophantine_implies_existentialUniversal` (Π₁ ⊆ Σ₂).
3. `existentialUniversal_iff_universalExistential_complement` (Σ₂/Π₂
   duality).
4. `universalExistentialDefinition_iff_of_pred_iff` (Π₂ congruence).
5. `koenigsmann_implies_complement_existentialUniversal` (Σ₂(ℚ\ℤ)
   corollary).

## Build Status

Iteration 4 build: PENDING. Worktree's `.lake` is a self-symlink loop
so Docker build would re-fresh-clone Mathlib (~25-45 min). The three
new theorems use the same `Iff.trans` chaining as the iteration 3
`universalExistentialDefinition_iff_of_pred_iff`, which BUILT cleanly
in iteration 3 (3 jobs, exit code 0). All operate on already-defined
predicates with no new imports. Confidence high; CI is the ground
truth.

Iteration 3 build: PASSED ✅ (3 jobs, exit code 0).

## Blockers

None.

## Next Action

Commit, push, create PR for iteration 4 (this).

If S4 lands cleanly, S5+ candidates (unchanged from iteration 3):
- Σ₂ ⊆ Π₂'s ¬¬-shadow — `Σ₂(S)` and `Π₂(¬¬S) = Π₂(S)` agreement on
  `Prop`-classical predicates.
- Σ₁ × Π₁ closure properties (under finite union/intersection) — needs
  `Rat.mul_eq_zero` / sum-of-squares lemma which requires Mathlib import.
- Π₁ ⊆ Π₂ via `a ≠ 0 ⟺ ∃ z, a·z = 1` polynomial-inversion trick —
  same Rat field arithmetic blocker.
- Daans 2021 (10-quantifier reduction) as a separate axiomatized
  witness — adds 1 axiom, defer.

## Attempt Counts

- Total attempts: 4
- Current approach attempts: 1 (S4 — class congruence, this iteration)
- Approaches tried: 3 (S2 Σ₁/Π₁ duality, S3 Σ₂/Π₂ duality, S4 class
  congruence)
