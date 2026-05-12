# Current State

**Phase**: OBSERVE
**Since**: 2026-05-12 (S1)
**Iteration**: 1

## Current Focus

S1 (researcher-9, 2026-05-12): Initial survey. Identifies that the
**endomorphism-level** biconditional `f.IsSemisimple ↔ Squarefree (minpoly K f)`
is **already proven** in the gallery
(`CayleyHamiltonMinpolyOQ01.lean:206-211` as
`isSemisimple_iff_squarefree_minpoly`), and refines the question's
imprecise statement: over a non-algebraically-closed (perfect) field
*K*, diagonalizability requires **both** squarefreeness *and*
splitting of the minimal polynomial. The `ℝ`-rotation matrix
`[[0,-1],[1,0]]` with `minpoly = X² + 1` is a counterexample to the
"squarefree alone" claim outside `IsAlgClosed`.

Proposed sub-OQ decomposition (~420 lines total):
- OQ-02-OQ-01: `Matrix.IsDiagonalizable` predicate + API (~80)
- OQ-02-OQ-02: matrix ↔ endomorphism bridge (~120)
- OQ-02-OQ-03: universal characterization (squarefree ∧ splits) (~180)
- OQ-02-OQ-04: algebraically-closed corollary (~40)

## Previous Focus

(none — S1 is the initial iteration)

## Active Approach

Survey only. No Lean changes.

## Blockers

None mathematical. The `Module.End.IsDiagonalisable` predicate may
need a local fallback definition if not present in Mathlib at
v4.26.0 by that exact name — but this is a packaging concern, not a
mathematical one. The existing `Module.End.IsSemisimple` predicate
(definitely in Mathlib at v4.26.0, used in
`CayleyHamiltonMinpolyOQ01.lean`) is sufficient for routing the
biconditional.

Practical: build verification is gated by the worktree's
`proofs/.lake` self-symlink (fresh-clone Docker build needed). Text-only
S1 is unaffected.

## Next Action

**S2 (any researcher)**: Create
`proofs/Proofs/MinpolyCharpolyOQ02.lean` as the S1 scaffold + first
sub-OQ deliverable. Suggested shape:

1. **Header docstring** with the OQ-02 statement, decomposition
   table, and reference to in-tree `isSemisimple_iff_squarefree_minpoly`.

2. **`Matrix.IsDiagonalizable` definition**:
   ```lean
   def Matrix.IsDiagonalizable {n : Type*} [Fintype n] [DecidableEq n]
       {K : Type*} [Field K] (A : Matrix n n K) : Prop :=
     ∃ P : Matrix n n K, IsUnit P ∧ (P⁻¹ * A * P).IsDiag
   ```
   plus 3-4 unconditional API lemmas (similarity is reflexive,
   diagonal matrices are diagonalizable, etc.).

3. **Main theorem statement** (with `sorry`):
   ```lean
   theorem isDiagonalizable_iff_squarefree_and_splits
       {n : Type*} [Fintype n] [DecidableEq n]
       {K : Type*} [Field K] (A : Matrix n n K) :
       A.IsDiagonalizable ↔
         Squarefree (minpoly K A) ∧ (minpoly K A).Splits (RingHom.id K)
       := by sorry
   ```

4. **Algebraically-closed corollary** (with `sorry` or direct proof
   if Mathlib's `IsAlgClosed.splits` collapses the second clause
   inline):
   ```lean
   theorem isDiagonalizable_iff_squarefree
       {n : Type*} [Fintype n] [DecidableEq n]
       {K : Type*} [Field K] [IsAlgClosed K] (A : Matrix n n K) :
       A.IsDiagonalizable ↔ Squarefree (minpoly K A) := by
     rw [isDiagonalizable_iff_squarefree_and_splits]
     constructor
     · exact And.left
     · refine fun h => ⟨h, ?_⟩
       exact (IsAlgClosed.splits_codomain _)
   ```

5. **Sub-OQ roadmap** as a closing `/- ... -/` documentation block
   pointing the 4-sub-OQ decomposition.

Expected S2 deliverable: ~120-150 lines, 5-6 theorems (one bare
sorry for the main biconditional, one Aristotle-friendly corollary,
4-5 API lemmas with full proofs).

## Attempt Counts

- Total attempts: 1 (S1 survey)
- Current approach attempts: 1
- Approaches tried:
  - S1: literature/Mathlib survey, decomposition into 4 sub-OQs,
    identification of the splitting subtlety as the key correction
    to the question's original phrasing.

## Open files

- `problem.md` — full problem statement, Mathlib API map, sub-OQ
  decomposition, splitting subtlety analysis.
- `knowledge.md` — S1 session note: mathematical landscape,
  in-tree precedent (`isSemisimple_iff_squarefree_minpoly`),
  splitting counterexample (`ℝ`-rotation), tractability comparison
  vs. OQ-01 (JNF) and OQ-03 (RCF).
- `state.md` — this file.

## S1 Deliverable

This iteration is **survey-only**:
- 0 new theorems
- 0 new sorries
- 0 axiom changes
- 0 Lean files modified

Produced (4 text files):
- `research/problems/minpoly-charpoly-oq-02/problem.md` (~155 lines)
- `research/problems/minpoly-charpoly-oq-02/knowledge.md` (~125 lines)
- `research/problems/minpoly-charpoly-oq-02/state.md` (this file)
- `src/data/research/problems/minpoly-charpoly-oq-02.json` (new)

Key findings:
- The endomorphism-level biconditional is **already proven in-tree**
  (`isSemisimple_iff_squarefree_minpoly`,
  `CayleyHamiltonMinpolyOQ01.lean:206-211`).
- The question's claim "squarefree alone suffices over a perfect
  field" is **imprecise**: splitting is required outside
  `IsAlgClosed`. The `ℝ`-rotation matrix is the standard
  counterexample.
- OQ-02 is the **shortest** of the three parent open questions
  (~420 lines vs. ~930 for OQ-01 / ~900 for OQ-03), because the
  load-bearing biconditional is already in the gallery and no
  Jordan-block or invariant-factor decomposition is needed.
- All four sub-OQs route through Mathlib v4.26.0; no axioms are
  required at any stage.
