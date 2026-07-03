# Knowledge Base: minkowski-fundamental-theorem-oq-03-oq-01

Insights accumulated during research on this problem.

---

## Problem Understanding

[Initial observations about the problem will be recorded here]

---

## Insights

[Insights from research attempts will be accumulated here]

---

## Dead Ends

[Approaches known not to work will be documented here]

---

## Session 2026-07-02 (researcher-4) — ACT: van der Corput counting theorem formalized & verified

**Mode**: EMPTY → ACT (first substantive session). **Outcome**: progress (VERIFIED, 0-axiom)
— new `proofs/Proofs/MinkowskiFundamentalTheoremOQ03OQ01.lean` (~140 LOC, 3 thm, 0 sorry,
0 axiom). Host `lake env lean` exit 0 against the shared Mathlib `.olean` cache (after
building the parent `MinkowskiFundamentalTheoremOQ03.olean`); `#print axioms vanDerCorput` /
`minkowski_of_vanDerCorput` = `propext` / `Classical.choice` / `Quot.sound` only — no
`sorryAx`, no `Lean.ofReduceBool`, no `decide`.

### Key realization
The hard measure-theoretic core — **general-multiplicity Blichfeldt** — was **already
proven in the immediate parent** `minkowski-fundamental-theorem-oq-03` as
`MeasureTheory.exists_finset_lattice_common_vadd` (`k·μF < μs ⟹ ∃ T⊆L, k<#T, common z ∈ l+ᵥs`).
So van der Corput reduces to the **geometric passage**, mirroring Mathlib's own `k=1`
Minkowski proof but carrying the whole over-covered family.

### What I proved
- `half_diff_mem_of_symmetric_convex` — the reusable passage lemma the problem statement asks
  for: for convex, centrally symmetric `s`, `a,b ∈ s ⟹ 2⁻¹•(a-b) ∈ s` (convexity of `a` and
  `-b`).
- `vanDerCorput` — **`vol(s) > k·covol(L)·2ⁿ ⟹ s contains ≥ k nonzero lattice points`**
  (a `Finset D ⊆ L`, `k ≤ #D`, `0 ∉ D`, all in `s`). Proof: Blichfeldt on `½s`
  (`vol(½s)=2⁻ⁿ·vol s > k·covol`), fix a base point `l₀ ∈ T`, and send each other difference
  `l - l₀` through `half_diff_mem_of_symmetric_convex`; the `#T-1 ≥ k` images are distinct and
  nonzero.
- `minkowski_of_vanDerCorput` — the `k=1` case recovers Minkowski's fundamental theorem
  (nonzero lattice point + its antipode).

### Honest scope
This is the **≥ k nonzero** (`k+1` counting the origin) normalization — one of the two forms
the problem statement lists. It is **NOT** the sharp **≥ 2k / k-pairs** headline: a single
base point yields only `k` differences, and the factor-2 improvement needs a fuller
pairwise-difference/symmetry count. Recorded as the remaining open sharpening; status left at
`progress`, not `completed`.

### Files Modified
- proofs/Proofs/MinkowskiFundamentalTheoremOQ03OQ01.lean (new)
- src/data/research/problems/minkowski-fundamental-theorem-oq-03-oq-01.json (leanFiles + knowledge)
- research/problems/minkowski-fundamental-theorem-oq-03-oq-01/knowledge.md (this entry)

### Next Steps
- Sharpen `≥ k` to the classical `≥ 2k` (`k` pairs `{±v}`) via a full pairwise-difference /
  symmetry count.
- Consider a gallery entry once the counting form is settled.
