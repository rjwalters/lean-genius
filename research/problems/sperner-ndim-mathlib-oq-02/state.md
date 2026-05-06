# Current State

**Phase**: ACT
**Since**: 2026-05-06
**Iteration**: 6

## Current Focus

Lean proof of Brouwer's fixed-point theorem via Sperner's lemma.
Core proof (compactness, coloring, algebraic structure): COMPLETE (0 sorries).
1 axiom remains: `sperner_panchromatic` (Sperner's lemma for Freudenthal grid).
Companion file `SpernerFreudenthalSimplex.lean` written with full proof structure (6 sorries).

## Active Approach

FreudSimplex CellComplex + CellComplex.sperner (SpernerMathlib4.lean).
- CellComplex requires: adj_symm, adj_vertex, adj_ne (no boundary_face needed!)
- boundary_doors_odd: proved by induction on n
- Companion file written with adjacency formulas and proof skeleton

## Correct Adjacency Formulas (derived session 6, verified by example)

For FreudCell (base, σ) with miss = σ(Fin.last n):
- **Face k ∈ {1,...,n-1}**: `adj = some ((base, σ∘swap(k-1,k)), k)` — always valid
- **Face 0**: `adj = some ((base+e_{σ(0)}-e_{miss}, leftRot(σ)), n)` if base[miss]>n; none if base[miss]=n
- **Face n**: `adj = some ((base-e_{σ(n-1)}+e_{miss}, rightRot(σ)), 0)` if base[σ(n-1)]≥1; none if =0

where leftRot(σ): σ'(j)=σ(j+1) for j<n-1, σ'(n-1)=σ(0), σ'(n)=σ(n)
      rightRot(σ): σ'(0)=σ(n-1), σ'(j)=σ(j-1) for j=1..n-1, σ'(n)=σ(n)

Key: leftRot and rightRot are mutual inverses (verified). adj_symm follows.

## Boundary Doors Analysis (key insight, session 6)

- **Face-n boundary doors** (base[σ(n-1)]=0): NOT IsDoor because v_j[σ(n-1)]=0 for j<n
  (Sperner condition prevents color σ(n-1)), so IsDoor fails
- **Face-0 boundary doors** (base[miss]=n): biject with FC cells of (n-1)-dim FreudSimplex
  By induction, count is odd → boundary_doors_odd holds

## Remaining Sorries in SpernerFreudenthalSimplex.lean

1. `FreudCell.fintype`: bounded subtype embedding — ~20 lines (HARD)
2. `perm_preimage_lt_card`: |{i≠miss: σ⁻¹(i)<k}|=k — ~15 lines (HARD)
3. `FreudCell.vertCoord_sum`: ∑vertCoord=N — ~25 lines (HARD, uses 2)
4. `freudAdj_symm` face 0/n: leftRot∘rightRot=id — ~40 lines (HARD)
5. `freudAdj_vertex`: shared face verification — ~50 lines (HARD)
6. `freudBoundaryDoorsOdd`: inductive Sperner parity — ~150 lines (OPEN)

## Next Action

1. Implement `freudBoundaryDoorsOdd` by induction (the core ~150 lines)
2. Fill in mechanical sorries 1-5 (~150 lines total)
3. Wire companion file to main: replace `axiom sperner_panchromatic` with theorem call
4. Docker build to confirm 0 sorries, 0 axioms

## Attempt Counts

- Total attempts: 6
- Current approach (CellComplex + panchromatic tuples): sessions 5-6
- Approaches tried: 3 (SpernerTriangulation → CellComplex → panchromatic direct)
