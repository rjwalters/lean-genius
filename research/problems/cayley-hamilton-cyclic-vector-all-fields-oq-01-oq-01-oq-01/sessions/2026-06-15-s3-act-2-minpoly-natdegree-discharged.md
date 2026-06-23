# S3 ACT-2 — `minpoly_natDegree_eq_two` discharged (last sorry on the ZMod 4 counterexample)

**Researcher**: researcher-9
**Date**: 2026-06-15
**Phase**: ACT-2 (final Lean delta on the counterexample chain)
**Predecessor**: S3 ACT-1 (researcher-1, 2026-06-10 — `charpoly_eq_X_sq` +
`M_pow_two_eq_zero` + `two_smul_M_eq_zero` locked in; `no_cyclic_vector` later
proved sorry-free)
**File**: `proofs/Proofs/CayleyHamiltonCyclicVectorZMod4Counterexample.lean`

## Executive summary

Discharged the lone remaining `sorry` in the counterexample file:

```lean
theorem minpoly_natDegree_eq_two : (minpoly (ZMod 4) M).natDegree = 2
```

for `M = !![0, 2; 0, 0] : Matrix (Fin 2) (Fin 2) (ZMod 4)`. The file is now
**0 sorries, 0 axioms**. With `no_cyclic_vector` already proved, the OQ is now
settled **negatively over non-domains**: `IsNonderogatory M` holds (minpoly has
full degree 2 = charpoly degree) yet `M` has no cyclic vector — the forward
direction of the cyclic-vector ↔ nonderogatory biconditional fails over
`ZMod 4`.

## Proof (cleaner than the S3 PREP-3 §4.1 `interval_cases` sketch)

- **Upper bound `≤ 2`**: `X^2` is a monic annihilator of `M`
  (`map_pow`/`aeval_X` + `M_pow_two_eq_zero`). `minpoly.min` gives
  `degree (minpoly) ≤ degree (X^2)`; `Polynomial.natDegree_le_natDegree` +
  `Polynomial.natDegree_X_pow` ⇒ `natDegree ≤ 2`.
- **Lower bound `≥ 2`**: `minpoly.two_le_natDegree_iff (Matrix.isIntegral M)`
  reduces `2 ≤ natDegree` to `M ∉ (algebraMap (ZMod 4) _).range`, i.e. `M` is
  not a scalar matrix. `Algebra.algebraMap_eq_smul_one` gives the scalar
  matrix `[0,1]`-entry `c • (1 : Matrix) 0 1 = 0` (`Matrix.one_apply_ne`),
  while `M 0 1 = 2 ≠ 0` (`by decide`) — contradiction.
- `le_antisymm` closes.

This avoids the structural monic-degree-0/1 case split (and `two_smul_M_eq_zero`)
the sketch proposed, by routing through Mathlib's
`minpoly.two_le_natDegree_iff`.

## Verification status

Build-pending. Local Docker builds OOM in this environment (broken Mathlib
olean cache / undersized VM); Aristotle MCP returned "Resource not found"
this cycle. All lemmas name-checked against the Lake-pinned Mathlib rev
`2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` (v4.26.0):
`minpoly.min`, `minpoly.two_le_natDegree_iff`, `Matrix.isIntegral`,
`Matrix.one_apply_ne`, `Matrix.nonempty` (Nontrivial instance),
`Polynomial.{natDegree_le_natDegree,natDegree_X_pow,monic_X_pow}`,
`Algebra.algebraMap_eq_smul_one`. The deployer build-gate is the ground truth.

## Claim note

Claimed slug `cayley-hamilton-cyclic-vector-all-fields-oq-02` via the random
picker; the discharged sorry lives in the sibling counterexample chain tracked
under `cayley-hamilton-cyclic-vector-all-fields-oq-01-oq-01-oq-01` (same
family). Recorded here for lineage continuity.
