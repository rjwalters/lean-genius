# erdos-751-incomplete-01 — session notes

## 2026-07-22 (researcher-1) — sorry elimination + integrity finding

**Problem:** Erdős #751 (cycle lengths in 4-chromatic graphs). `Erdos751Problem.lean`
carried two `sorry`s:
1. A **def-sorry**: `minCycleLengthGap (lengths : Set ℕ) : ℕ := sorry` (Aristotle skips
   definition sorries, so it needed a human).
2. A dependent **theorem-sorry** in `erdos_751`: `minCycleLengthGap (cycleLengths G) ≤ 2`.

**Work done (0 new axioms, host-verified `lake env lean` v4.31, EXIT=0):**
- Gave `minCycleLengthGap` a faithful total definition:
  `sInf {d | ∃ a ∈ S, ∃ b ∈ S, a < b ∧ d = b - a}` — the minimum difference between
  distinct elements, which equals the minimum *consecutive* gap (the closest pair is
  always consecutive). Empty/singleton sets give `sInf ∅ = 0`.
- Added foundational lemma `minCycleLengthGap_le : a ∈ S → b ∈ S → a < b →
  minCycleLengthGap S ≤ b - a` via `Nat.sInf_le`.
- Discharged the `hgap_bound` sorry: from two distinct close cycle lengths
  `m, m'` with `|m − m'| ≤ 2`, `minCycleLengthGap_le` + `omega` give `≤ 2`.
- Added `import Mathlib.Order.Lattice.Nat` (for `Nat.sInf`/`Nat.sInf_le`).

Both file sorries are now gone; gallery meta updated (`sorries` 2→0, `theoremCount`
6→7, `lineCount`, imports, `status` → `axiomatized`, `badge` → `axiom`).

## Integrity finding (for auditor / mechanic)

The pre-existing axiom
`four_chromatic_minDeg (G) : chromaticNumber G = 4 → minDegree G ≥ 3`
is **FALSE as literally stated**. Counterexample: take `K₄` and attach a pendant
vertex (degree 1) to one of its vertices. The graph is still 4-chromatic (contains
`K₄`) but its minimum degree is 1, not ≥ 3. The correct classical fact is that a
4-chromatic graph has a *subgraph* (its 3-core / degeneracy witness) of minimum
degree ≥ 3 — a global min-degree bound does not hold. The headline `erdos_751`
theorem is nonetheless **true**, but it is currently derived through this unsound
axiom. A faithful restatement would either (a) weaken the axiom to
`∃ H ≤ G, minDegree H ≥ 3` and feed Bondy–Vince on `H`, or (b) route through the
degeneracy/3-core, neither of which has ready Mathlib API.

## Open (blocked)

- `bondy_vince_theorem` (δ ≥ 3 ⇒ two cycle lengths differ by ≤ 2) — deep 1998
  result, no Mathlib cycle-length-spectrum API. Left as an axiom.
