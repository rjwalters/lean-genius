# Knowledge Base: erdos-268-oq-01

## Problem Summary

Erdős #268: Prove that the set X_d of harmonic subseries points has nonempty interior in ℝ^d.
The main result (nonempty interior) is axiomatized as `erdos_268_solved`. The question is whether
path-connectedness and other topological properties can be proved.

## Current Status (2026-04-21, Session 3)

**Sorry count**: 4 (reduced from 8 this session)

**Proved this session**:
- `shifted_summable`: If A has convergent harmonic sum, so does any shifted version 1/(n+k).
  Proof: split on n=0 (single finite term via hasSum_ite_eq) and n≥1 (direct comparison).
- `powers_convergent`: {2^k | k ∈ ℕ} has convergent harmonic sum.
  Proof: bijection ℕ → powersOf2Set via k↦2^k, reduces to geometric series (1/2)^k.
- `squares_convergent`: {k^2 | k ≥ 1} has convergent harmonic sum.
  Proof: bijection ℕ → squaresSet via k↦(k+1)^2, reduces to p-series (convergent for p=2>1).
- `harmonicPointSet_nonempty`: X_d is non-empty.
  Proof: use powersOf2Set as witness.

**Remaining sorries (4)**:
1. `harmonicPointSet_path_connected` — HARD: requires showing X_d is path-connected.
2. `harmonicPointSet_dense_somewhere` — WRONG STATEMENT: uses globally-dense (`Dense`).
3. `coordinate_decreasing` — WRONG STATEMENT: FALSE when 0 ∈ A and i=0.
4. `first_coordinate_largest` — WRONG STATEMENT: depends on coordinate_decreasing.

---

## Session 2026-04-21 (Session 3)

**Mode**: REVISIT  
**Outcome**: progress (4 sorries eliminated)

### Key Findings
- The n=0 issue: 1/0=0 in Lean, so n=0 elements behave differently under shifting.
  When i=0 and 0 ∈ A: shiftedHarmonicSum A 0 has 1/0=0 for n=0, but
  shiftedHarmonicSum A 1 has 1/(0+1)=1, making A 1 > A 0 for pathological A.
- `coordinate_decreasing` counterexample: A = {0}∪{2^k}. Then shiftedHarmonicSum A 0 ≈ 2
  but shiftedHarmonicSum A 1 ≈ 3. The theorem needs hypothesis `0 ∉ A`.
- `harmonicPointSet_dense_somewhere`: `Dense` in Lean = globally dense = closure S = univ.
  But interior of a proper set is not globally dense. Statement is wrong.
- `shifted_summable` correct proof uses `hasSum_ite_eq` for the indicator term at n=0.

### Files Modified
- `proofs/Proofs/Erdos268Problem.lean` (4 sorries proved, wrong statements documented)
- `src/data/proofs/erdos-268/meta.json` (sorries: 8 → 4)

### Next Steps
1. Fix `coordinate_decreasing`: add `0 ∉ A`, prove via tsum_lt_tsum with strict term comparison.
2. Fix `harmonicPointSet_dense_somewhere`: change Dense to relative density.
3. Attempt `harmonicPointSet_path_connected` for d=0 (Subsingleton, trivial).
4. d=1 case: characterize X_1 = Ioi 0 via greedy algorithm (hard).

---

## Dead Ends

- Trying to prove `coordinate_decreasing` without `0 ∉ A`: has counterexample, IMPOSSIBLE.
- Trying to prove `harmonicPointSet_dense_somewhere` as globally dense: NOT TRUE.
- `Erdos268Aristotle.lean` proof of `shifted_summable` is incorrect: bound 1/(n+k) ≤ 1/n
  fails for n=0 (gives 1/k ≤ 0, false). The companion file has this bug.
