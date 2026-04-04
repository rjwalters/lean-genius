# Problem: ballot-problem-oq-01-oq-02-oq-02
# LGV Determinant for Path Orderings

**Question**: Given m candidates with a₁ > a₂ > ... > aₘ votes, prove the m-candidate ordering probability equals ∏_{i<j} (aᵢ - aⱼ)/(aᵢ + aⱼ).

**Status**: AXIOMATIZED — 0 sorries, 2 axioms (LGV lemma gap)

## Problem Summary

The MacMahon-LGV product formula for m-candidate ballot orderings:
  P(a₁ > a₂ > ... > aₘ throughout) = ∏_{i<j} ballotRatio(aᵢ, aⱼ)

The 2-candidate case is Mathlib's ballot theorem. The m≥3 case requires the
Lindström-Gessel-Viennot (LGV) lemma for non-intersecting lattice paths, which
is not yet in Mathlib.

---

## Session 2026-04-04 (Session 1) — Initial Survey and Proof

**Mode**: FRESH
**Outcome**: axiomatized (0 sorries, 2 axioms)

### What I Did

1. **Defined `ballotRatio (a b : ℕ) : ℚ`**: The pairwise ballot probability (a-b)/(a+b).

2. **Proved structural theorems**:
   - `ballotRatio_antisymm`: swapping negates ratio
   - `ballotRatio_pos`: positive when a > b
   - `ballotRatio_le_one`: at most 1 when a > b (not strictly < 1; `b = 0` gives ratio = 1)
   - `ballotRatio_mono`: monotone in margin (proved via `div_le_div_iff₀` + `nlinarith`)

3. **Proved 6 numerical examples** (norm_num): (3,1)=1/2, (4,2)=1/3, (5,1)=2/3, (4,2,1)=1/15, (5,3,1)=1/12, (6,4,2)=1/30.

4. **Proved `orderingProbability_two`**: 2-candidate case from `Ballot.ballot_problem b a hab` (ENNReal form with `ProbabilityTheory.uniformOn`).

5. **Proved `det_ballotMatrix2`**: determinant of 2×2 antisymmetric ballot matrix = 1 + r².

6. **Axiomatized** `three_candidate_ordering_formula` and `three_ordering_product_conjecture`.

### Key Lean-Specific Findings

- `MeasurableSpace (List ℤ) := ⊤` needed for `ProbabilityTheory.uniformOn` to work on List types.
- `ballotRatio_lt_one` is FALSE for `b = 0` (ratio = 1 when unanimous); correct form is `≤ 1`.
- `Ballot.ballot_problem b a hab` takes (smaller, larger, proof) in Archive.Wiedijk100Theorems.
- `div_le_div_iff₀` is the Lean4 Mathlib name for cross-multiplication of divided rationals.
- `ballot_problem'` does not exist as a 3-argument function; use `Ballot.ballot_problem` (ENNReal).

### Infrastructure Gap

The LGV lemma (Lindström-Gessel-Viennot) is not in Mathlib. Building it requires ~500 lines:
- Non-intersecting lattice path definitions
- Path sign bijection (involution on intersecting paths)
- Determinant expansion connecting path count to ballot probabilities

### Files Modified
- `proofs/Proofs/BallotProblemOQ01OQ02OQ02.lean`: created, 240 lines, 13 theorems, 2 defs, 0 sorries, 2 axioms
- `proofs/Proofs.lean`: added import
- `src/data/research/problems/ballot-problem-oq-01-oq-02-oq-02.json`: updated metadata

### Next Steps
- Build LGV lemma infrastructure (300-500 lines) as a separate OQ-03
- Prove 3-candidate formula once LGV infrastructure exists
- Generalize to m-candidate formula via Finset.prod
