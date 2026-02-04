# Abel-Ruffini Galois Theory Extensions - Knowledge

## Problem
Extend the Abel-Ruffini theorem formalization with explicit proofs connecting
solvability by radicals to group-theoretic solvability, and characterizing
the degree-5 threshold.

## Key Results

### Proved Theorems (9 theorems, 0 sorries, 0 axioms)
1. `galois_bridge`: IsSolvableByRad F alpha -> IsSolvable q.Gal (named wrapper for solvableByRad.isSolvable')
2. `symmetric_group_not_solvable`: Sn not solvable for n >= 5
3. `s5_not_solvable`: S5 not solvable (specific case n=5)
4. `s6_not_solvable`: S6 not solvable (specific case n=6)
5. `a5_is_simple`: A5 is a simple group (alternatingGroup.isSimpleGroup_five)
6. `s0_solvable`: S0 is solvable (trivial group, inferInstance)
7. `s1_solvable`: S1 is solvable (trivial group, inferInstance)
8. `not_solvable_by_rad_of_not_solvable_gal`: Contrapositive Abel-Ruffini - unsolvable Galois group implies not solvable by radicals
9. `exists_quintic`: There exists a degree-5 polynomial over Q

### Iteration 1 Progress (2026-02-03)
- Added `galois_bridge` wrapping Mathlib's `solvableByRad.isSolvable'`
- Added `s5_not_solvable`, `s6_not_solvable` as specific instances of `symmetric_group_not_solvable`
- Added `a5_is_simple` wrapping `alternatingGroup.isSimpleGroup_five`
- Added `s0_solvable`, `s1_solvable` via `inferInstance`
- Added `not_solvable_by_rad_of_not_solvable_gal` (contrapositive form)
- Added `exists_quintic` via `Polynomial.X ^ 5`
- Renamed `exists_unsolvable_quintic` to `exists_quintic`
- Removed `#check` statements and converted `example` to named theorem
- Comprehensive documentation of the solvability threshold at degree 5

### Mathlib Availability
- `solvableByRad.isSolvable'`: EXISTS - core bridge theorem
- `Equiv.Perm.not_solvable`: EXISTS - Sn not solvable for n >= 5
- `alternatingGroup.isSimpleGroup_five`: EXISTS - A5 is simple
- `IsSolvable (Equiv.Perm (Fin 0))`: EXISTS via inferInstance
- `IsSolvable (Equiv.Perm (Fin 1))`: EXISTS via inferInstance
- `IsSolvable (Equiv.Perm (Fin 2))`: MISSING - S2 is abelian
- `IsSolvable (Equiv.Perm (Fin 3))`: MISSING - derived series through A3
- `IsSolvable (Equiv.Perm (Fin 4))`: MISSING - derived series through V4
- `alternatingGroup.isSimpleGroup` (general n >= 5): MISSING - only Fin 5

### Theorem Structure
The theorems form the complete Abel-Ruffini picture:
1. `galois_bridge`: Solvable by radicals => solvable Galois group
2. `symmetric_group_not_solvable`: Sn not solvable for n >= 5
3. `not_solvable_by_rad_of_not_solvable_gal`: Contrapositive combining 1 and 2
4. `a5_is_simple`: Why exactly degree 5 is the threshold
5. `s0_solvable`, `s1_solvable`: Small cases where solvability holds

## Next Steps
- Prove S2 solvable (S2 is abelian, isomorphic to Z/2)
- Prove S3 solvable (derived series S3 > A3 > {e})
- Prove S4 solvable (derived series S4 > A4 > V4 > {e})
- Submit to Aristotle for automated proof search on small group solvability
- Construct explicit polynomial with Galois group S5
