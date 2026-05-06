# Current State

**Phase**: ACT
**Since**: 2026-05-06
**Iteration**: 7

## Current Focus

Fix face-0 adjacency formula in SpernerFreudenthalSimplex.lean (session 6 formula is WRONG).
Session 7 derived correct formula for n=2; n≥3 needs verification.

## Active Approach

FreudSimplex CellComplex + CellComplex.sperner (SpernerMathlib4.lean).
- 1 axiom remains in main file: `sperner_panchromatic`
- Companion file SpernerFreudenthalSimplex.lean has 8 sorries (face-0 adj is wrong)

## CORRECT Adjacency Formulas (session 7 correction)

For FreudCell (base, σ) with miss = σ(Fin.last n):
- **Middle face k ∈ {1,...,n-1}**: `adj = some ((base, σ∘swap(k-1,k)), k)` — CORRECT ✓
- **Face n**: `adj = some ((base-e_{σ(n-1)}+e_{miss}, rightRot(σ)), 0)` if base[σ(n-1)]≥1; none if =0 — CORRECT ✓
  (face-n boundary lies on F_{σ(n-1)} = geometric face of Δⁿ ✓)
- **Face 0** (CORRECTED, was wrong):
  - τ = σ ∘ swap(n-1, n) [NOT leftRotPerm; only swaps last two positions]
  - miss' = σ(n-1) [NOT σ(n) = miss as before]
  - b = base + 2·e_{σ(n-1)} + Σ_{k=1}^{n-2} e_{σ(k)} - n·e_{miss}
  - adj = some((b,τ), 0) if base[σ(n-1)] ≥ n-2; none if base[σ(n-1)] < n-2
  - For n=2: always adjacent (base[σ(1)] ≥ 0 always)
  - VERIFIED for n=2: ((0,1,2),id) ↔ ((0,3,0),(1↔2)) ✓

## Remaining Sorries in SpernerFreudenthalSimplex.lean

1. `FreudCell.fintype`: bounded subtype embedding — ~20 lines (HARD)
2. `perm_preimage_lt_card`: last step |{j<k}|=k — ~5 lines (easy: Fin.card_Iio)
3. `FreudCell.vertCoord_sum`: ∑vertCoord=N — ~25 lines (HARD, uses 2)
4. `face0Adj`/`faceNAdj` hsum/hmiss: arithmetic — ~30 lines (HARD, formula needs rewrite first)
5. `freudAdj_symm` face 0/n: swap∘swap=id, base roundtrip — ~40 lines (HARD)
6. `freudAdj_vertex`: shared face set equality — ~50 lines (HARD)
7. `freudBoundaryDoorsOdd`: inductive Sperner parity — ~150 lines (OPEN)
8. `freud_sperner_panchromatic`: assembly — ~20 lines

## Next Action

1. Fix `face0Adj` in companion file with correct formula (τ=σ∘swap(n-1,n))
2. Verify formula for n=3 by concrete example
3. Prove `freudAdj_symm` and `freudAdj_ne` for corrected formulas
4. Prove `freudBoundaryDoorsOdd` by induction

## Attempt Counts

- Total attempts: 7
- Current approach (CellComplex + panchromatic tuples): sessions 5-7
- Approaches tried: 3 (SpernerTriangulation → CellComplex → panchromatic direct)
