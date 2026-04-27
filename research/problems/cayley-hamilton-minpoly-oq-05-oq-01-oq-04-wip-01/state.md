# Current State

**Phase**: COMPLETED
**Since**: 2026-04-27T00:00:00+00:00
**Iteration**: 3

## Current Focus

WIP05 built and verified. The cluster is fully closed for axiom-free formalization:
WIP04 proves the general factored case; WIP05 supplies the factorization automatically
via `UniqueFactorizationMonoid.normalizedFactors`, removing the only remaining input
hypothesis. The composition `nonderogatory_has_cyclic_vector_any_field` takes only
the matrix and `IsNonderogatory M` and produces a cyclic vector — over any field K.

## Active Approach

UFD factorization wrapper:
1. f := minpoly K M is monic (from charpoly_monic and the nonderogatory hypothesis).
2. s := normalizedFactors f is a multiset of monic irreducible primes.
3. D := s.toFinset is the Finset of distinct primes (nonempty for n ≥ 1).
4. For each q ∈ D, multiplicity = s.count q ≥ 1.
5. Distinct monic irreducibles are coprime; powers stay coprime via `IsCoprime.pow`.
6. f = ∏ q ∈ D, q^(s.count q) via `prod_normalizedFactors_eq` + `Monic.normalize_eq_self`
   + `Finset.prod_multiset_count`.
7. Reindex via `Fintype.equivFin` and apply WIP04's `nonderogatory_general_has_cyclic_vector`.

## Result

**WIP05**: `proofs/Proofs/CayleyHamiltonMinpolyOQ05OQ01OQ04WIP05.lean`
- 167 lines, 0 sorries, 0 axioms (build verified)
- Namespace: `GeneralCyclicVectorComplete`
- Main theorem: `nonderogatory_has_cyclic_vector_any_field`

## Blockers

None. Cluster fully closed.

## Next Action

PR created. Optional follow-ups:
1. Close the original `sorry` in `CayleyHamiltonMinpolyOQ05OQ01OQ04.lean` by translating
   WIP05 to its LinearIndependent-style `IsCyclicVector` definition.
2. Refactor WIP04 to take `[Fintype σ]` instead of `Fin k` (would absorb WIP05's
   reindexing wrapper).

## Attempt Counts

- Total attempts: 2
- Current approach attempts: 1
- Approaches tried: 2 (WIP04 primary decomposition; WIP05 UFD-factorization wrapper)
