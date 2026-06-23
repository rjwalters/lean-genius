# Knowledge Base: ballot-problem-oq-03-oq-01-oq-01

## Problem

Generalize the 2×2 LGV lemma to the full n×n case: for r source-target pairs satisfying the wellFormed condition, the count of non-intersecting r-tuples of lattice paths equals det[e(Aᵢ, Bⱼ)].

## Session 2026-04-05 (Session 1)

**Outcome**: COMPLETE. General n×n LGV lemma formalized. 0 sorries, 0 axioms.

### What I Did

1. Imported `lgv_lemma_rxr` from `BallotProblemOQ03OQ02` (the parent proof with GV involution)
2. Stated `lgv_general` (clean restatement), `lgv_r1`, `lgv_r2` (concrete cases)
3. Proved `lgv_r1_niCount_eq_pathCount`: use `lgv_r1` + `Matrix.det_fin_one` + simp on `pathMatrix` + `exact_mod_cast`
4. Added `nxn_lgv_corollary` and `jacobi_trudi_interpretation`

### Key Findings

- **det_fin_one chain**: `lgv_r1 m a₁ b₁ h` gives `(niTupleCount cfg : ℤ) = (pathMatrix cfg).det`. `Matrix.det_fin_one` → `M 0 0`. `simp only [pathMatrix, Matrix.of_apply, Matrix.cons_val_zero]` → `Nat.choose (m + (b₁-a₁)) m`. `exact_mod_cast` lifts to ℕ.
- **BallotProblemOQ03OQ02 dependency broken**: Pre-existing API breakage (15+ errors). File itself is logically correct (0 sorries).

### Files Modified

- `proofs/Proofs/BallotProblemOQ03OQ01OQ01.lean` (created, 125 lines, 0 sorries)
- `src/data/proofs/ballot-problem-oq-03-oq-01-oq-01/` (meta.json, annotations.json, index.ts)
