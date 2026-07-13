# Research: buffons-needle-oq-02-oq-03
## Abstract Cauchy-Crofton Formula

**Problem**: Formalize the abstract Cauchy-Crofton formula: for any measure μ satisfying
E_μ[#(s ∩ H)] = α_n · length(s) for segments, prove E_μ[crossings(P)] = α_n · length(P)
for polygonal paths via linearity of expectation.

**Status**: COMPLETED (2026-05-03)

---

## Session 2026-05-03 (Session 1) - COMPLETED

**Mode**: FRESH
**Outcome**: completed (proof written, 0 sorries, 3 axioms, awaiting Docker build)

### What I Did
- Selected problem from candidate pool (MODERATE knowledge, tractable structure)
- Read parent proofs: BuffonsNeedleOQ02.lean, BuffonsNeedleOQ02OQ01.lean, BuffonsNeedleOQ02OQ02.lean
- Wrote `proofs/Proofs/BuffonsNeedleOQ02OQ03.lean` (286 lines, 3 axioms, 27 theorems)
- Created gallery `src/data/proofs/buffons-needle-oq-02-oq-03/meta.json`

### Key Findings
- The entire polygonal formula follows from integral_add by list induction — no extra geometry needed
- `simp_rw` (not `rw`) is required for rewriting under integral binders (rewrites under λ H)
- Step-2 recurrence α_{n+2} = (n/(n+1))·α_n follows by `push_cast; ring` from the step-4 formula
- π bounds: 3D<2D uses pi_lt_four, 4D<3D uses pi_gt_three, 5D<4D uses pi_lt_315 (9π < 32)
- `Real.pi_lt_3141593` was removed from Mathlib; `Real.pi_lt_315` (available) is sufficient
- Pattern matching needs explicit `| 0, h => absurd h (by omega)` cases for completeness

### Files Modified
- `proofs/Proofs/BuffonsNeedleOQ02OQ03.lean` (NEW)
- `src/data/proofs/buffons-needle-oq-02-oq-03/meta.json` (NEW)
- `research/problems/buffons-needle-oq-02-oq-03/knowledge.md` (NEW)

### Proof Architecture
```
Axioms (3):
  kinematicMeasure : Measure (AffineHyperplane n)
  cauchy_crofton_segment : ∫ crossing H = α_n · length(s)
  crossing_integrable : Integrable crossing (kinematicMeasure n)

Main Theorem (list induction):
  cauchy_crofton_polygonal : ∫ totalCrossings segs H = α_n · totalLength segs
  Proof: nil → simp; cons → simp_rw + integral_add + cauchy_crofton_segment + IH

Consequences (algebra only):
  crofton_shape_independence, crofton_zero_length, crofton_singleton,
  crofton_equal_segments, crofton_append

Dimension Comparison:
  crossingFactor_step2 (n ≥ 1): α_{n+2} = (n/(n+1)) · α_n
  crossingFactor_succ_succ_lt (n ≥ 1): α_{n+2} < α_n
  α₃ < α₂ (π < 4), α₄ < α₃ (π > 3), α₅ < α₄ (9π < 32, π < 3.15)
```

### Next Steps
- Run Docker build to verify compilation
- Submit PR with `research` label
