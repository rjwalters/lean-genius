# Ioo Integrability for Fubini Interval Swap (greens-theorem-oq-01-oq-01-oq-03)

## Problem

Can the Icc integrability hypothesis in the Fubini interval integral swap be weakened
to just L¹ integrability on the open rectangle Ioo a b × Ioo c d?

**Answer: YES** — proved in `GreensTheoremOQ01OQ01OQ03.lean`.

## Session 2026-05-06 (Session 1) - Complete Implementation

**Mode**: FRESH
**Outcome**: completed

### What I Did
- Surveyed the problem: the open question from greens-theorem-oq-01-oq-01 asks whether
  the Icc integrability hypothesis can be weakened to Ioo
- Key insight: For Lebesgue measure, Icc and Ioo intervals differ only by {a,b},
  which has measure zero → vol.restrict(Icc) = vol.restrict(Ioo)
- Proved 6 theorems in GreensTheoremOQ01OQ01OQ03.lean (228 lines, 0 sorries, 0 axioms):
  1. volume_Icc_sdiff_Ioo: boundary has measure zero
  2. volume_restrict_Icc_eq_Ioo: restriction equality (key novel lemma)
  3. volume_prod_restrict_Icc_eq_Ioo: product measure equality
  4. intervalIntegral_swap_of_Ioo_integrable: main Fubini with Ioo
  5. integrable_Icc_iff_Ioo: explicit equivalence iff
  6. greens_fubini_open_rectangle: application to Green's theorem
- Created gallery entry: src/data/proofs/greens-theorem-oq-01-oq-01-oq-03/
- Created PR #16077 (complete implementation); closed stub PR #16071

### Key Findings
- Icc and Ioo intervals agree for Lebesgue measure: boundary {a,b} is null
- vol.restrict(Icc a b) = vol.restrict(Ioo a b) proved via measure extensionality
- This lemma is NOT in Mathlib (Mathlib uses Ioc as canonical interval)
- Set.Countable.measure_zero exists in Mathlib and works for singleton measure
- measure_union_null, measure_mono_null, measure_union_le all in Mathlib

### Files Modified
- proofs/Proofs/GreensTheoremOQ01OQ01OQ03.lean (228 lines, 0 sorries, 0 axioms)
- src/data/proofs/greens-theorem-oq-01-oq-01-oq-03/ (gallery entry)
- src/data/research/problems/greens-theorem-oq-01-oq-01-oq-03.json (knowledge JSON)
- research/problems/greens-theorem-oq-01-oq-01-oq-03/knowledge.md (this file)

### Next Steps
- Generalize volume_restrict_Icc_eq_Ioo to any atomless Borel measure
- Consider contributing this lemma to Mathlib.MeasureTheory.Measure.Lebesgue.Basic
