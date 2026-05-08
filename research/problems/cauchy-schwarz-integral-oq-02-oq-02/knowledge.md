# Knowledge Base: cauchy-schwarz-integral-oq-02-oq-02

## Status: COMPLETE (verified, 0 axioms, 0 sorries)

The original 2-sorry version of this OQ has been **fully closed**: the
gallery entry is now at status `verified` with `axiomCount: 0` and
`sorries: 0`. Updated as of 2026-05-08 (researcher-11 audit, this PR).

## Problem Understanding

**Question**: Can the Lp Minkowski inequality be proved via the explicit
Hölder chain in Lean 4, without the black-box `NormedAddCommGroup`
instance?

**Answer**: YES. The chain `Young → Hölder → Minkowski` is fully
formalized in `proofs/Proofs/CauchySchwarzIntegralOQ02OQ02.lean`
(406 lines, 13 theorems, 0 axioms, 0 sorries) using the Mathlib
v4.26.0 API.

## Insights

- The **factoring trick** (splitting `|f+g|^p` and applying Hölder twice)
  is the critical step. Encoded as `lintegral_rpow_le_split` and
  `holder_applied_to_split`.
- The **conjugate exponent identity** `(p-1)q = p` is essential. Encoded
  as `conjugate_exponent_identity`.
- Three **special cases** bypass Hölder: `p = 1` (direct triangle
  inequality, encoded as `minkowski_l1`), `p = 2` (Cauchy–Schwarz, encoded
  as `minkowski_l2_from_cs`), `p = ∞` (`essSup`, encoded as `minkowski_linfty`).
- **ENNReal rpow arithmetic** was the main technical barrier in the
  original draft (2 sorries flagged in the now-superseded knowledge.md).
  Both sorries were closed in subsequent iterations using
  `ENNReal.rpow_natCast`, `ENNReal.mul_rpow_of_ne_top`, and standard
  `norm_cast` orchestration.

## Built Items (current snapshot, post-this-PR)

- `proofs/Proofs/CauchySchwarzIntegralOQ02OQ02.lean` — 406 lines,
  13 theorems, 0 axioms, 0 sorries.
- 13 proved theorems:
  - `young_ineq`: Young's inequality `a*b ≤ a^p/p + b^q/q` for
    Hölder conjugates `p, q`.
  - `holder_lintegral`: `lintegral` form of Hölder, derived from `young_ineq`.
  - `holder_eLpNorm`: `eLpNorm`-form of Hölder for `ENNReal`-valued
    measurable functions.
  - `abs_add_pow_le_pow_add`: `|a + b|^p ≤ 2^(p-1) (|a|^p + |b|^p)` for
    `p ≥ 1` — the critical factoring lemma.
  - `conjugate_exponent_identity`: `(p − 1) * q = p` for Hölder conjugates.
  - `minkowski_explicit`: Minkowski inequality for `ℝ≥0` lintegrals.
  - `lintegral_rpow_le_split`: the splitting bound combining
    `abs_add_pow_le_pow_add` and `lintegral_add_left'`.
  - `holder_applied_to_split`: applies Hölder to the split form.
  - `minkowski_from_holder_explicit`: assembles the chain into Minkowski.
  - `chain_verification`: explicit verification of the Young → Hölder →
    Minkowski chain.
  - `minkowski_l1`, `minkowski_l2_from_cs`, `minkowski_linfty`: special
    cases for `p ∈ {1, 2, ∞}`.
- Gallery data complete: `meta.json` at status `verified`, `index.ts`,
  `annotations.json`, `tacticStates.json` all in place.

## Why This Matters

This OQ demonstrates that the **explicit Hölder chain** route to
Minkowski's inequality is fully tractable in Lean 4 + Mathlib v4.26.0,
without falling back to Mathlib's black-box `NormedAddCommGroup (Lp …)`
instance. The gallery entry is a reusable template for any future
OQ that needs the explicit Young→Hölder→Minkowski chain (e.g.,
weighted-Lp variants, Bochner-integrable refinements).

## Status / Next Steps

The original two action items in the previous knowledge.md are both
fully discharged:

1. ✅ **Close 2 ENNReal rpow arithmetic sorries**: DONE (sorries
   eliminated; current `grep -c "sorry"` returns 0).
2. ✅ **Submit companion file to Aristotle**: not applicable — the
   file has 0 sorries, so there is nothing for Aristotle to prove.

**No further iterations are required on this slug.** Future work
candidates (none of them blocking):

- Add cross-references from related Lp / inequality entries pointing
  to this file as a canonical Hölder-chain template.
- Extract `young_ineq`, `conjugate_exponent_identity`,
  `abs_add_pow_le_pow_add` into a shared `Mathlib.Analysis.MinkowskiHelpers`
  candidate file for upstream Mathlib contribution. Each is broadly
  applicable beyond this OQ.

## References

- `proofs/Proofs/CauchySchwarzIntegralOQ02OQ02.lean` — main file.
- `src/data/proofs/cauchy-schwarz-integral-oq-02-oq-02/meta.json` —
  gallery entry (status `verified`).
- Hardy–Littlewood–Pólya, *Inequalities*, ch. VI (1934) — classical
  reference for the Young → Hölder → Minkowski chain.
- Mathlib `Mathlib.MeasureTheory.Integral.MeanInequalities` — Mathlib's
  alternative route via `eLpNorm`.
