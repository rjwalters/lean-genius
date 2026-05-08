# Research State: cayley-hamilton-cyclic-vector-all-fields-oq-01-oq-02

## Current State
**Phase**: ORIENT (file exists; scaffold in progress)
**Path**: full
**Since**: 2026-05-08
**Iteration**: 1

## Current Focus

The Lean file is already on `origin/main` with the main theorem
`nonderogatory_similar_to_companion` proved modulo one routine axiom (`hMn_axiom`).
This session's focus is to (a) register the file with the gallery and (b) plan the
axiom elimination for the next iteration.

## Active Approach

Conjugation identity:
- Build the Krylov matrix `P[i,j] = (M^j v)_i` (column j is `M^j v`)
- Show `P` is invertible: `mulVec P` is injective because `v` is cyclic — any kernel
  vector `c` produces a polynomial `q = ∑ c_j X^j` with `deg q < n` and `q(M)v = 0`,
  forcing `q = 0` and hence `c = 0`
- Show `M · P = P · C(minpoly)`: column-by-column comparison. For columns `j < n-1`,
  both sides give `(M^{j+1})·v`. For column `n-1`, both sides give `(M^n)·v`,
  using the Cayley-Hamilton relation `M^n = -∑ k<n, c_k M^k`

## Attempt Count
- Total attempts: 1 (existing file landed via PR #16881 side-effect)
- Approaches tried: Krylov-matrix similarity (current)

## Blockers

None. The remaining `hMn_axiom` is a routine consequence of `minpoly.aeval = 0` plus
monicity of `minpoly K M`. Mathlib v4.26.0 has all required API.

## Next Action (Session 2)

Eliminate `hMn_axiom`. Target proof structure:

```lean
private theorem hMn (M : Matrix (Fin n) (Fin n) K) (v : Fin n → K)
    [NeZero n] (hdeg : (minpoly K M).natDegree = n) :
    (M ^ n).mulVec v =
      -(∑ k ∈ Finset.range n, (minpoly K M).coeff k • (M ^ k).mulVec v) := by
  -- 1. minpoly annihilates: aeval M (minpoly K M) = 0
  have h0 : aeval M (minpoly K M) = 0 := minpoly.aeval K M
  -- 2. Monic of degree n: coeff n = 1
  have hmonic : (minpoly K M).Monic := minpoly.monic (Matrix.isIntegral M)
  have hcn : (minpoly K M).coeff n = 1 := hdeg ▸ hmonic
  -- 3. Expand aeval as a finite sum (Polynomial.aeval_eq_sum_range)
  have hexp : aeval M (minpoly K M) =
      ∑ i ∈ Finset.range ((minpoly K M).natDegree + 1),
        (minpoly K M).coeff i • M ^ i := aeval_eq_sum_range _
  rw [hdeg, Finset.sum_range_succ, hcn, one_smul] at hexp
  -- 4. h0 + hexp gives: ∑ i<n, c_i • M^i + M^n = 0 → M^n = -∑ ...
  have hMn_mat : M ^ n = -(∑ i ∈ Finset.range n, (minpoly K M).coeff i • M ^ i) :=
    eq_neg_of_add_eq_zero_right (hexp ▸ h0)
  -- 5. Apply mulVec v
  rw [hMn_mat, Matrix.neg_mulVec, Matrix.sum_mulVec]
  congr 1
  refine Finset.sum_congr rfl (fun k _ => ?_)
  exact (Matrix.smul_mulVec_assoc _ _ _).symm
```

**Build risk**: Lean API names may be slightly off (e.g. `aeval_eq_sum_range` vs
`Polynomial.aeval_eq_sum_range'`). Worth a Docker build to verify.

## Stretch Goals (Session 3+)

- **Generalize companion**: state and prove `IsCyclic v M ↔ ∃ P, IsUnit P ∧ P⁻¹ * M * P = companionMx (minpoly K M)`
  (the converse direction is easier: cyclic ↔ similar to a single companion block).
- **Push toward Mathlib**: extract `Matrix.companionMatrix` and `Matrix.similar_companionMatrix_of_nonderogatory`
  as the seed of a Mathlib RCF contribution.
- **Connection to OQ-01-OQ-01**: `cyclic_implies_nonderogatory` from OQ-01-OQ-01 plus this
  entry give the full equivalence `nonderogatory ↔ similar to single-block companion`.
