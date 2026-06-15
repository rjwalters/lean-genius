# minkowski-theorem-oq-03 — Minkowski Bound on Ideal Norms

## Problem

"Minkowski Bound on Ideal Norms: Geometry of Numbers Connection" (tier B, sig 8, tract 6).
Connect the gallery's Minkowski lattice-point theorem to a bound on ideal norms / the class
number of a number field.

## Status Summary

**PROGRESS** (build pending). Produced `proofs/Proofs/MinkowskiTheoremOQ03.lean`:
- `minkowskiIdealBound K` — a reusable definition of the Minkowski bound (Mathlib only has it
  as a `local notation` inside `ClassNumber.lean`).
- `exists_ideal_in_class_absNorm_le` — restatement of the ideal-norm bound against the named
  constant (reduces to `NumberField.exists_ideal_in_class_of_norm_le`).
- `classNumber_le_card_absNorm_le` — **new** quantitative estimate:
  `classNumber K ≤ Nat.card {I : (Ideal (𝓞 K))⁰ // absNorm (↑I) ≤ ⌊minkowskiIdealBound K⌋₊}`.

0 sorries, 0 axiom declarations. NOT kernel-checked this session (worktree Docker cache
unavailable; Aristotle MCP endpoint returned "Resource not found").

## Mathlib API (name-checked @ rev 2df2f0150c)

`Mathlib/NumberTheory/NumberField/ClassNumber.lean`:
- `NumberField.classNumber K := Fintype.card (ClassGroup (𝓞 K))`
- `NumberField.RingOfIntegers.instFintypeClassGroup : Fintype (ClassGroup (𝓞 K))`
- `NumberField.classNumber_eq_one_iff : classNumber K = 1 ↔ IsPrincipalIdealRing (𝓞 K)`
- `NumberField.exists_ideal_in_class_of_norm_le (C) : ∃ I : (Ideal (𝓞 K))⁰, mk0 I = C ∧ absNorm (↑I) ≤ M K`
  where `M K` is the **local notation** `(4/π)^(nrComplexPlaces K) * ((finrank ℚ K)! / (finrank ℚ K)^(finrank ℚ K) * √|discr K|)`.
- `RingOfIntegers.isPrincipalIdealRing_of_abs_discr_lt` — PID if `|discr K| < (2(π/4)^r₂ (nⁿ/n!))²`.
- `RingOfIntegers.isPrincipalIdealRing_of_isPrincipal_of_pow_le_of_mem_primesOver_of_mem_Icc`
  and the Galois variant — the standard prime-by-prime PID criterion.
- `Rat.classNumber_eq : NumberField.classNumber ℚ = 1`.

`Mathlib/RingTheory/Ideal/Norm/AbsNorm.lean`:
- `Ideal.finite_setOf_absNorm_eq [CharZero S] (n) : {I | absNorm I = n}.Finite`
- `Ideal.finite_setOf_absNorm_le [CharZero S] (n) : {I | absNorm I ≤ n}.Finite`
- `Ideal.finite_setOf_absNorm_le₀ [CharZero S] (n) : {I : (Ideal S)⁰ | absNorm (↑I) ≤ n}.Finite`

`Mathlib/NumberTheory/NumberField/CanonicalEmbedding/ConvexBody.lean`:
- `NumberField.mixedEmbedding.exists_ne_zero_mem_ideal_of_norm_le` (the convex-body input)
- `NumberField.mixedEmbedding.minkowskiBound` / `_lt_top` / `_pos`.

Other:
- `Nat.card_le_card_of_surjective {α β} [Finite α] (f) (hf : Surjective f) : Nat.card β ≤ Nat.card α`
  (`Mathlib/SetTheory/Cardinal/Finite.lean`)
- `Nat.card_eq_fintype_card [Fintype α] : Nat.card α = Fintype.card α`
- `Nat.le_floor [IsOrderedRing α] (h : (n:α) ≤ a) : n ≤ ⌊a⌋₊` (`Mathlib/Algebra/Order/Floor/Defs.lean`)

## Insights

- The headline theorem (ideal-norm bound) and the finiteness of the class group are **already
  in Mathlib**. Honest assessment: the new content is (a) exposing the bound as a reusable
  constant, and (b) the explicit head-count `classNumber ≤ #{ideals of norm ≤ ⌊M_K⌋}`, which is
  the formal backbone of the class-number algorithm and is NOT recorded in Mathlib.
- The "small bound ⟹ PID" criterion is also already in Mathlib
  (`isPrincipalIdealRing_of_abs_discr_lt`), so that is not a gap.
- `minkowskiIdealBound K` is written character-for-character as Mathlib's local notation, so
  `unfold minkowskiIdealBound; exact NumberField.exists_ideal_in_class_of_norm_le C` discharges
  the restatement by definitional equality.

## Mathlib Gaps / Why a concrete example was NOT attempted

- A concrete worked example (e.g. "ℚ(√d) has class number 1 via the Minkowski bound") needs a
  `NumberField` instance for the quadratic field together with computed `discr`,
  `nrComplexPlaces`, and `finrank`. No clean quadratic-field discriminant instance was found in
  Mathlib at this rev; building one is a substantial (likely > 500 line) undertaking and was out
  of scope for a build-blocked session. This is the natural next step and the real remaining
  content of oq-03.

## Next Steps

1. Green Docker build of `MinkowskiTheoremOQ03.lean` → promote meta.json status to verified/original.
   If `unfold; exact` fails on the restatement, fall back to `simpa only [minkowskiIdealBound]
   using NumberField.exists_ideal_in_class_of_norm_le C` or massage the coercion on `√|discr K|`.
2. Resubmit the file to Aristotle when its MCP endpoint recovers, to obtain an independent
   verified proof of `classNumber_le_card_absNorm_le`.
3. Concrete instantiation: prove a specific small-discriminant field (Gaussian `ℚ(√-1)`,
   `ℚ(√-3)`, `ℚ(√5)`, all satisfying `isPrincipalIdealRing_of_abs_discr_lt` directly) has class
   number 1, once quadratic-field discriminant infrastructure is available.

## Sessions

### 2026-06-15 (S1) — ORIENT + ACT, build pending

**Mode**: FRESH. **Outcome**: progress (build pending).

- Claimed problem; surveyed Mathlib class-number API (name-checked above).
- Found the headline ideal-norm bound and class-group finiteness already in Mathlib.
- Identified the genuine gap: reusable bound constant + explicit class-number head-count.
- Wrote `MinkowskiTheoremOQ03.lean` (1 def, 3 theorems, 0 sorries, 0 axioms) + gallery
  meta/annotations.
- Aristotle endpoint unavailable; Docker worktree cache unavailable ⇒ not kernel-checked.
