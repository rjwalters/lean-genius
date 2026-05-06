# Current State

**Phase**: ACT
**Since**: 2026-05-06
**Iteration**: 8

## Current Focus

FreudCell constant-miss triangulation is FUNDAMENTALLY BROKEN for n≥3.
Session 8: verified the n≥3 failure rigorously; fixed perm_preimage_lt_card (1 sorry eliminated).

## Fundamental Finding (Session 8)

The constant-miss FreudCell construction is NOT a valid triangulation of N·Δⁿ for n≥3:

**The failure**: Cell (base=(0,0,0,4), σ=id, n=3, N=4) has face-0 = {v_1,v_2,v_3} =
{(1,0,0,3),(1,1,0,2),(1,1,1,1)}. This face is geometrically interior to 4·Δ³ (vertex
(1,1,1,1) has all positive coordinates). But:
- No other constant-miss FreudCell shares this face (verified: only ordering of {v_1,v_2,v_3}
  with unit consecutive differences and constant miss direction leads back to same cell)
- Session 7 formula says adj(s,0)=none when base[σ(n-1)] < n-2 = 1, but base[σ(2)]=0

Result: FreudCell claims this is a boundary face, but geometrically it's interior.
This invalidates the boundary_doors_odd parity argument for n≥3.

**Why it works for n=2**: For n=2, face-0 of every constant-miss cell HAS a constant-miss
adjacent cell (the session 7 formula for n=2: adj=some always when base[σ(1)]≥0 ✓).

## Active Approach

Main file: 1 axiom (`sperner_panchromatic`), rest proved.
Companion file: fundamentally broken for n≥3; 11 sorries remain.

## Correct Face-0 Adjacency (for n=2 only, fully derived)

For FreudCell (base, σ) with n=2, miss = σ(2):
- adj(s, 0) = some ((b, τ), 0) where:
  - τ = σ ∘ swap(1, 2) [swap last two σ positions]
  - b = base + 2·e_{σ(1)} - 2·e_{miss}
  - Always valid (base[σ(1)] ≥ 0 always for n=2)
- VERIFIED: ((0,1,2),id) ↔ ((0,3,0),(1↔2)) ✓

For n≥3: requires b[miss'] = base[σ(n-1)] + 2 ≥ n, i.e., base[σ(n-1)] ≥ n-2.
Many cells violate this, claiming adj=none for geometrically interior faces. INCORRECT.

## Path Forward

**Option A — Fix for n≥3**: Redesign FreudCell with variable-miss chains
- Each cell is (base, sequence of n (add, subtract) pairs)
- Complex data structure, hard to prove adj_symm/vertex
- Estimated: 400+ lines additional work

**Option B — n=1 direct proof**: sperner_panchromatic for n=1 via discrete IVT (~60 lines)
- Color sequence c(0),...,c(N): c(0)=1, c(N)=0, find transition
- Doesn't prove general n

**Option C — Different main strategy**: Use SpernerNDimOQ03.lean's brouwer_simplex which
needs `sperner` parameter as axiom. Same blocker just renamed.

**Recommended**: Continue accepting `sperner_panchromatic` as the axiom (the gallery entry
is already published with 1 axiom), OR attempt Option B to show n=1 provability.

## Remaining Sorries in SpernerFreudenthalSimplex.lean

1. `FreudCell.fintype`: bounded subtype — ~20 lines (HARD)
2. ~~`perm_preimage_lt_card`~~: FIXED in session 8 ✓
3. `FreudCell.vertCoord_sum`: ∑vertCoord=N — ~25 lines (HARD)
4. `face0Adj`/`faceNAdj` hsum/hmiss: WRONG formulas for n≥3
5. `freudAdj_symm` face 0/n: wrong formula premise
6. `freudAdj_vertex`: ~50 lines (HARD)
7. `freudBoundaryDoorsOdd`: inductive Sperner parity — ~150 lines (OPEN)
   + BLOCKED: parity fails due to wrong adjacency for n≥3
8. `freud_sperner_panchromatic`: assembly — ~20 lines

## Attempt Counts

- Total attempts: 8
- Current approach (CellComplex + panchromatic tuples): sessions 5-8
- Approaches tried: 3 (SpernerTriangulation → CellComplex → panchromatic direct)
