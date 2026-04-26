# Knowledge Base: szemeredi-regularity-oq-02

Insights accumulated during research on this problem.

---

## Problem Understanding

Szemerédi Regularity: Frieze-Kannan Weak Regularity Comparison.

Prove that Szemerédi ε-regularity implies Frieze-Kannan 2ε-cut-approximation,
and quantify the bound gap: Szemerédi uses tower-type parts while FK uses at
most 4^(1/ε²) parts.

---

## Session 1 (2026-04-26)

**Mode**: FRESH
**Outcome**: COMPLETED — Lean file already fully proved (0 sorries, 0 axioms); created gallery entry

### What I Did

1. Discovered SzemerediRegularityOQ02.lean (399 lines) already fully proved with 0 sorries
2. Confirmed key theorems: IsCutApproximation, pair_cut_error_bound, szemeredi_implies_fk,
   sz_stepBound_ge_power, sz_two_steps_tower, fk_bound_at_half
3. Created gallery entry in src/data/proofs/szemeredi-regularity-oq-02/ (meta.json, annotations.json, index.ts)

### Key Insights

- Per-pair proof needs two cases: large A,B (ε-regularity) and small A,B (trivial bound)
- Partition identity: sum_ij |Pi||Pj| = n^2 converts per-pair to global bound
- FK's bound 4^(1/eps^2) is singly exponential vs Szemerédi's tower-type
- The converse (FK implies Szemerédi) fails — FK is strictly weaker

### Files Modified

- src/data/proofs/szemeredi-regularity-oq-02/ (new gallery entry)

---

## Dead Ends

None — the Lean file was already complete when discovered.
