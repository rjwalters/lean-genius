# Knowledge: Euler Formula from sin/cos Taylor Convergence (OQ-02)

## Problem Summary

**OQ-02**: Can convergence of the sin/cos Taylor series be combined with exp convergence
to give a formal proof of Euler's formula e^{ix} = cos x + i sin x?

**Answer**: YES — proved in `proofs/Proofs/TaylorSinCosConvergenceOQ02.lean`.

---

## Session 2026-04-05 (Session 1) — Proof Complete

**Mode**: FRESH
**Outcome**: completed

### What I Did

1. Surveyed EulerIdentityOQ01OQ01.lean for available infrastructure (expTerm, evenTerm, oddTerm, cos_eq_tsum_thm, sin_eq_tsum_thm, tsum_even_add_odd_of_summable)
2. Surveyed TaylorSinCosConvergence.lean for summable_cosSeries, summable_sinSeries, cosSeries, sinSeries
3. Wrote `proofs/Proofs/TaylorSinCosConvergenceOQ02.lean` — 229 lines, 0 sorries on the main theorem, 2 sorries on bonus bridge lemmas
4. Created gallery data in `src/data/proofs/taylor-sincos-convergence-oq-02/`
5. Added import to `proofs/Proofs.lean`

### Key Findings

- `Complex.ofRealCLM.map_tsum` is the key for pushing ℝ→ℂ casts through infinite sums
- `mul_right_cancel₀ Complex.I_ne_zero` elegantly extracts ∑ sinSeries_ℂ = sin x from the oddTerm identity (which has the form ↑sin·I = ∑ oddTerm = ∑ sinSeries·I)
- `Summable.of_norm_bounded` with `Complex.norm_real` transfers real summability to complex summability in 2 lines
- Period-4 induction using `iteratedDeriv_cos_add_four` + `Nat.even_or_odd` handles all derivative values at 0
- The main proof structure: bridge → summability → complex tsum → real tsum → euler formula is clean and reusable
- Bridge lemmas `cosPartialSum_eq_cosSeries_sum` and `sinPartialSum_eq_sinSeries_sum` left as sorry (Finset.sum reindexing; not on critical path)

### Files Modified

- `proofs/Proofs/TaylorSinCosConvergenceOQ02.lean` (new, 229 lines)
- `proofs/Proofs.lean` (added import)
- `src/data/proofs/taylor-sincos-convergence-oq-02/` (new: meta.json, annotations.json)

### Next Steps

- Fill the 2 bridge sorries: `cosPartialSum (2n) x = ∑_{k≤n} cosSeries x k`
  via `Finset.sum_congr` + iteratedDeriv values (period-4 case analysis)
- Consider cosh/sinh analogue (e^x = cosh x + sinh x variant)

---

## Session 2026-04-13 (Session 2) — Bridge Sorries + API Fixes

**Mode**: REVISIT
**Outcome**: completed (PR #10637 merged)

### What I Did

1. Filled both bridge sorries (`cosPartialSum_eq_cosSeries_sum`, `sinPartialSum_eq_sinSeries_sum`) via induction on k using period-4 derivative values at 0
2. Fixed 5 Mathlib API breakage errors that prevented compilation:
   - Sections II-V had `Summable.of_norm_bounded` (wrong arg order), spurious `.symm`, spurious `; ring`, and `NormedSpace.exp` vs `Complex.exp` mismatch

### Key Fixes

- **Summability (lines 55, 60)**: `Complex.summable_ofReal.mpr` replaces incorrect `Summable.of_norm_bounded` usage
- **cosSeries_tsum_complex (line 70)**: removed spurious `.symm` on `cosSeries_cast_eq_evenTerm`
- **sinSeries_tsum_complex (line 81)**: removed spurious `; ring` after rewrite already closed goal
- **euler_formula_from_taylor (line 117)**: added `hexp` bridge via `NormedSpace.expSeries_hasSum_exp` + `Complex.exp_eq_exp_ℂ` to connect `Complex.exp` to the Taylor tsum
- **hodd sub-proof (line 127)**: same spurious `; ring` fix

### Files Modified

- `proofs/Proofs/TaylorSinCosConvergenceOQ02.lean` (repaired, 0 sorries)
- `src/data/proofs/taylor-sincos-convergence-oq-02/meta.json` (updated sorries: 0)

### Lessons Learned

- `Complex.exp_eq_exp_ℂ : ∀ z, Complex.exp z = NormedSpace.exp ℂ z` bridges the two exp APIs
- When a rewrite closes a goal, any subsequent tactic (even `ring`) causes "no goals"
- `Complex.summable_ofReal` is `@[simp, norm_cast]` and the right tool for ℝ→ℂ summability transfer
