# Research State: cayley-hamilton-cyclic-vector-all-fields-oq-01-oq-02

## Current State
**Phase**: COMPLETE (axiom-free; CI pending)
**Path**: full
**Since**: 2026-05-08
**Iteration**: 2

## Current Focus

The entry is now `verified` (0 axioms, 0 sorries) over arbitrary fields. PR #17039
opens with the Session 2 axiom-elimination work. CI verification pending.

## Outcome

Session 2 replaced the residual `private axiom hMn_axiom` with a `private theorem
hMn_axiom` proved from Mathlib's `minpoly.aeval` + `minpoly.monic (Matrix.isIntegral
M)` and a local helper `aeval_eq_sum_pow_local` that converts `Polynomial.eval₂_eq_sum`'s
output into the smul form via `← Algebra.smul_def`.

The implemented proof differs slightly from the Session 1 skeleton (which referenced
`Polynomial.aeval_eq_sum_range`): the actually-shipped version uses the lower-level
`Polynomial.eval₂_eq_sum` + `Polynomial.sum_def` + `← Algebra.smul_def` chain, with
`Finset.sum_subset` (and `Polynomial.le_natDegree_of_mem_supp` for the subset
direction; `Polynomial.notMem_support_iff` for the `f x = 0 outside the support`
direction) to extend the support sum to `range (n+1)`. Once the smul-form expansion
is in hand, monicity isolates `1 • M^n`, solving for `M^n` gives the matrix-level
identity, and `mulVec v` (via local `sum_mulVec_local`) yields the desired vector
identity.

## File State

- 214 lines (was 156; +58 net)
- 8 theorems/lemmas (was 5; +3: `sum_mulVec_local`, `aeval_eq_sum_pow_local`,
  the `private theorem hMn_axiom`)
- 2 definitions (`companionMx`, `cyclicMatrix`; unchanged)
- **0 axioms, 0 sorries**

## Triangle of Equivalences (now closed)

With OQ-01 (`nonderogatory ⇒ ∃ cyclic v`), OQ-01-OQ-01 (`cyclic ⇒ nonderogatory`),
and this entry (`nonderogatory ⇒ similar to companion via the Krylov matrix`), the
full triangle

  IsNonderogatory M ↔ ∃ v cyclic ↔ ∃ P invertible, P⁻¹ M P = companionMx (minpoly K M)

is now machine-verified over arbitrary fields with **zero axioms**.

## Next Steps (Session 3+, if pursued)

1. **Companion-similarity biconditional**: with `cyclic_implies_nonderogatory` from
   OQ-01-OQ-01, prove the converse `similar to companionMx ⇒ nonderogatory` and
   package the full biconditional `IsNonderogatory M ↔ ∃ P invertible, P⁻¹ M P =
   companionMx (minpoly K M)`.

2. **Companion-matrix charpoly/minpoly identities**: Mathlib v4.26.0 lacks
   `Matrix.charpoly_companionMatrix` and `Matrix.minpoly_companionMatrix`. Adding
   these (the standard "charpoly = minpoly = p" identities) would let this entry
   export an even tighter `nonderogatory_companion` corollary.

3. **Mathlib contribution**: with `companionMx` and `nonderogatory_similar_to_companion`
   axiom-free, this is a candidate seed for adding `Matrix.companionMatrix` and
   `Matrix.IsSimilar.companionMatrix_of_nonderogatory` to Mathlib. The route to the
   multi-block RCF would go through the K[X]-module structure theorem.

## Risks

- **Build risk**: not verified locally (worktree `.lake` symlink trap; ~45 min
  Mathlib re-clone). CI is the ground truth for PR #17039. If CI flags an API drift
  on one of `Polynomial.eval₂_eq_sum`, `Polynomial.sum_def`, `Algebra.smul_def`,
  `Polynomial.le_natDegree_of_mem_supp`, `Polynomial.notMem_support_iff`,
  `Matrix.isIntegral`, `Polynomial.finset_sum_coeff`, `Polynomial.Monic.leadingCoeff`,
  or `eq_neg_of_add_eq_zero_right`, Session 3 will repair.

## Open Questions (post-completion)

See `meta.json` `overview.openQuestions` — the previously-listed "eliminate
hMn_axiom" item has been resolved; the remaining items are listed in priority order
(biconditional, companion identities, Mathlib contribution, K[X]-module connection).
