# Knowledge Base: basel-problem-oq-01-oq-03
# Basel Problem: Apéry Technique for ζ(5)

---

## Problem Summary

Can Apéry's method be extended to prove ζ(5) irrational? This requires constructing
integer sequences (pₙ, qₙ) with qₙ·ζ(5) - pₙ → 0 and qₙ·ζ(5) - pₙ ≠ 0.

**Status**: COMPLETED (conditional framework). The irrationality criterion is proved;
the open problem is constructing the witness sequences.

---

## Session 2026-04-04 (Session 1) — Initial Formalization

**Mode**: FRESH
**Outcome**: completed (framework file with 0 sorries)

### What I Did

- Surveyed existing OQ-01 file (BaselProblemOQ01OQ01.lean) for infrastructure
- Created BaselProblemOQ01OQ03.lean with Apéry irrationality criterion
- Proved `apery_criterion` (0 sorries): the core denominators argument
- Defined `AperyWitness` structure and `apery_implies_irrational`
- Proved `zetaFive_irrational_if_apery_witness` (conditional theorem)
- Proved `geometric_decay_tendsto` (geometric decay → convergence to 0)
- Defined `StrongAperyWitness` with explicit rate and `toAperyWitness` conversion
- Stated Apéry's ζ(3) recurrence as template
- Created gallery meta.json

### Key Findings

- The irrationality criterion reduces to: nonzero integers have |·| ≥ 1, giving
  lower bound 1/d on |qₙ·α - pₙ| for rational α = a/d
- Lean's `Metric.tendsto_atTop` provides the ε-N bridge for the contradiction
- `squeeze_zero_norm` + `tendsto_pow_atTop_nhds_zero_of_lt_one` prove geometric decay
- `field_simp` closes the algebraic identity for writing qₙ·r - pₙ as integer/denom
- `div_le_div_right` not available as a rewrite target; `mul_le_mul_of_nonneg_right`
  with explicit inverse works instead

### Files Modified

- `proofs/Proofs/BaselProblemOQ01OQ03.lean` (created, 213 lines, 0 sorries)
- `src/data/proofs/basel-problem-oq-01-oq-03/meta.json` (created)

### Next Steps

- This problem is essentially COMPLETED at the framework level
- Actual ζ(5) irrationality remains open (no known Apéry sequences)
- Possible future work: formalize Ball-Rivoal (infinitely many odd zeta values irrational)
