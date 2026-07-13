# nicomachus-sum-of-cubes-oq-03

**Problem:** Prove the odd-cube analogue of Nicomachus's theorem,
∑_{k=1}^n (2k−1)³ = n²(2n²−1) — the sum of the first n odd cubes.

**Status:** COMPLETED (verified, 0 sorries, 0 axioms).

## Summary

Indexing the n odd numbers as `2k+1` for `k ∈ range n` (giving 1, 3, …, 2n−1),
the identity is `∑_{k<n} (2k+1)³ = n²(2n²−1)`. Proved fully in Lean 4 + Mathlib.

## Session 2026-06-25 (Session 1) — FRESH

**Mode:** FRESH
**Outcome:** completed

### What I Did
- Recognized the closed form n²(2n²−1) = 2n⁴ − n² carries a subtraction hostile to
  `ring` over ℕ.
- Proved the subtraction-free equivalent `∑(2k+1)³ + n² = 2n⁴` by induction
  (`sum_odd_cubes_add`). The inductive step is the single polynomial identity
  `2m⁴ + (2m+1)³ + (m+1)² = 2(m+1)⁴ + m²` (closed by `ring`), spliced into the
  hypothesis by `omega` (which atomizes the nonlinear power terms).
- Recovered the headline `∑(2k+1)³ = n²(2n²−1)` over ℤ via `push_cast` + `linarith`
  + `ring` (`sum_odd_cubes`).
- Added a division-free scaled form `4·∑(2k+1)³ + 4n² = 8n⁴` (`four_mul_sum_odd_cubes`).

### Key Findings
- The "clear the subtraction by adding a term" technique keeps signed closed-form
  power sums entirely in ℕ — complements the parent's "case-split over cast" trick.
- `ring`-then-`omega` is a clean reusable pattern for inductive sum identities whose
  step is a fixed polynomial identity plus linear hypothesis bookkeeping.
- Only Mathlib dependency: `Finset.sum_range_succ`.

### Files Modified
- `proofs/Proofs/NicomachusOddCubes.lean` (new, 93 lines, 3 theorems, 0 def)
- `src/data/proofs/nicomachus-sum-of-cubes-oq-03/{meta.json,annotations.json}` (new)

### Verification
- `lake env lean Proofs/NicomachusOddCubes.lean` → exit 0, no errors.
- `#print axioms` on all three theorems → only propext, Classical.choice, Quot.sound
  (no sorryAx, no Lean.ofReduceBool). 0 axioms, 0 sorries.

### Next Steps
- Follow-up OQs (see meta.json openQuestions): general odd-power sums ∑(2k−1)^p;
  bijective/geometric proof.
