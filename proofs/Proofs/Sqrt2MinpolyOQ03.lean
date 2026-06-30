import Mathlib
import Proofs.Sqrt2Minpoly

/-!
# Class Number 1 for Q(√2) via Minkowski's Bound (S3 ACT SCAFFOLD)

## Problem

Prove `NumberField.classNumber Q_sqrt2 = 1` where `Q_sqrt2 := AdjoinRoot (X^2 - C 2 : ℚ[X])`.

## Strategy (per S2 PREP-1..9 audit chain)

1. Construct `Q_sqrt2` via `AdjoinRoot`; obtain `Field` / `Algebra ℚ` / `NumberField` instances.
2. Compute `NumberField.discr Q_sqrt2 = 8` (S3 sub-target — PREP-3/4/5/6).
3. Compute `NumberField.minkowskiBound Q_sqrt2 < 2` (S3 sub-target).
4. Apply Minkowski's existence-of-small-norm-element lemma.
5. Conclude every ideal class contains a unit ideal; hence `h_K = 1`.

## This SCAFFOLD scope (S3 ACT)

Set up the type, irreducibility `Fact`, and the canonical instance stack, then
state the main theorem `Q_sqrt2_classNumber_eq_one` with a strategic sorry.
The 4-step discriminant/Minkowski chain (PREP-3..8's 128-LOC sketch) is the
S4+ deliverable.

## Status

Strategic sorries: 1 (capstone `classNumber = 1`).
Axioms: 0.
Build-verified sub-targets: `X_sq_sub_two_ne_zero`, `Q_sqrt2_finrank = 2`.
-/

namespace Sqrt2MinpolyOQ03

open Polynomial

/-- The defining polynomial X² − 2 over ℚ; irreducibility imported from parent. -/
noncomputable abbrev X_sq_sub_two : ℚ[X] := X ^ 2 - C 2

/-- Q(√2) constructed as the quotient ℚ[X]/(X² − 2). -/
noncomputable abbrev Q_sqrt2 : Type := AdjoinRoot X_sq_sub_two

/-- The `Fact` instance unlocking `AdjoinRoot.field` for `Q_sqrt2`. -/
instance : Fact (Irreducible X_sq_sub_two) := ⟨Sqrt2Minpoly.irred_X_sq_sub_two⟩

/-- `Q_sqrt2` is a `NumberField`: finite-dimensional over ℚ via the power basis
of the monic irreducible defining polynomial. -/
instance : NumberField Q_sqrt2 where
  to_charZero := inferInstance
  to_finiteDimensional :=
    (PowerBasis.finite (AdjoinRoot.powerBasis
      (f := X_sq_sub_two)
      (by
        -- X² − 2 ≠ 0 (degree 2 ≠ 0)
        intro h
        have : (X_sq_sub_two : ℚ[X]).natDegree = 0 := by
          rw [h]; simp
        have hdeg : (X_sq_sub_two : ℚ[X]).natDegree = 2 := by
          simp [X_sq_sub_two]
        omega)))

/-- `X² − 2 ≠ 0` (it has degree 2). Factored helper, build-verified. -/
theorem X_sq_sub_two_ne_zero : X_sq_sub_two ≠ 0 := by
  intro h
  have hdeg : (X_sq_sub_two : ℚ[X]).natDegree = 2 := by simp [X_sq_sub_two]
  rw [h] at hdeg
  simp at hdeg

/-- **Sub-target (build-verified):** `[Q(√2) : ℚ] = 2`.

This is the field degree `n = finrank ℚ K` appearing in the Minkowski bound
`M K = (4/π)^(nrComplexPlaces K) · (n! / nⁿ · √|discr K|)`. For Q(√2), `n = 2`,
`nrComplexPlaces = 0` (totally real), and `discr = 8`, giving `M K = √2 < 2`.
The degree is computed here from the power basis of the degree-2 defining
polynomial via `AdjoinRoot.powerBasis_dim` + `PowerBasis.finrank`. -/
theorem Q_sqrt2_finrank : Module.finrank ℚ Q_sqrt2 = 2 := by
  rw [(AdjoinRoot.powerBasis X_sq_sub_two_ne_zero).finrank,
      AdjoinRoot.powerBasis_dim]
  simp [X_sq_sub_two]

/-- **Main theorem (strategic sorry, capstone):** the class number of Q(√2) is 1.

Proof route (real Mathlib v4.26.0 API, verified against
`Mathlib/NumberTheory/NumberField/ClassNumber.lean` at pin `2df2f015…`):

1. `classNumber_eq_one_iff : classNumber K = 1 ↔ IsPrincipalIdealRing (𝓞 K)`.
2. `RingOfIntegers.isPrincipalIdealRing_of_isPrincipal_of_pow_le_of_mem_primesOver_of_mem_Icc`
   reduces a PID proof to checking, for each prime `p ∈ Finset.Icc 1 ⌊M K⌋₊`,
   the ideals above `p`. (Mathlib's standard "compute `⌊M K⌋₊` then `fin_cases`"
   technique — Marcus 1977, discussion after Theorem 37.)
3. Compute `⌊M K⌋₊`: with `finrank ℚ K = 2` (`Q_sqrt2_finrank` above),
   `nrComplexPlaces K = 0` (Q(√2) totally real), and `discr K = 8`, the bound is
   `M K = 2!/2² · √8 = √2 ≈ 1.414`, so `⌊M K⌋₊ = 1`.
4. `Finset.Icc 1 1` contains no primes (1 is not prime), so the per-prime
   hypothesis is vacuous and `𝓞 K` is a PID; hence `classNumber K = 1`.

Remaining open sub-targets (each a separate Lean deliverable): `discr Q_sqrt2 = 8`
(quadratic trace-form / `Algebra.discr` computation), `nrComplexPlaces Q_sqrt2 = 0`,
and the `⌊M K⌋₊ = 1` real-arithmetic reduction.

NOTE: the prior state record's assumed bearer `isPrincipalIdealRing_of_abs_discr_lt`
does NOT exist in Mathlib v4.26.0; the route above is the actual available API. -/
theorem Q_sqrt2_classNumber_eq_one :
    NumberField.classNumber Q_sqrt2 = 1 := by
  sorry

end Sqrt2MinpolyOQ03
