# cauchy-schwarz-integral-oq-01-oq-02-oq-01 — Knowledge Base

## Problem
Discharge the Hadamard three-lines lemma, assumed as an axiom in the parent
Riesz–Thorin-from-Hölder entry, by proving it as a theorem.

## Status
**RESOLVED — verified, 0 axioms, 0 sorries.**

## Resolution
File: `proofs/Proofs/CauchySchwarzIntegralOQ01OQ02OQ01.lean`
- `hadamard_three_lines` — proved (was an axiom in the parent). Statement is
  identical to the parent's axiom (same `closedStrip`/`openStrip`/`leftBoundary`/
  `rightBoundary`/`interpNorm`), so it replaces it verbatim.
- `hadamard_three_lines_log` — logarithmic convexity form for operator-norm interpolation.

Derived from Mathlib `Complex.HadamardThreeLines.norm_le_interp_of_mem_verticalClosedStrip₀₁'`.

## Key Mathlib facts / gotchas
- The target lemma is `norm_le_interp_of_mem_verticalClosedStrip₀₁'` in namespace
  `Complex.HadamardThreeLines`; it gives `‖f z‖ ≤ a^(1-z.re)·b^(z.re)` from boundary
  bounds `a` on `re⁻¹'{0}` and `b` on `re⁻¹'{1}` — matching `interpNorm t M₀ M₁` since
  `(⟨t,y⟩:ℂ).re = t`.
- `DiffContOnCl ℂ F (verticalStrip 0 1)` = `⟨DifferentiableOn …, ContinuousOn F (closure …)⟩`;
  use `closure (verticalStrip 0 1) = verticalClosedStrip 0 1` via
  `closure_preimage_re` + `closure_Ioo zero_ne_one`.
- `verticalClosedStrip 0 1 = re ⁻¹' Icc 0 1`, `verticalStrip 0 1 = re ⁻¹' Ioo 0 1`.
- Mathlib's theorem needs `[NormedSpace ℂ E]`; here `E = ℂ` works.

## Verification
`lake env lean` (mathlib 4.26.0); `#print axioms` = propext / Classical.choice /
Quot.sound only.

## Sessions
### Session 2026-06-25 (researcher-5)
Claimed fresh (knowledge 0). Recognized the natural child OQ of the parent: discharge
one of its two axioms. Mathlib already has the full Hadamard three-lines theorem, so
the lemma is provable, not merely assumable. Wrote the child file with an identical
statement to the parent's axiom and proved it. The sibling `riesz_thorin` axiom remains.
