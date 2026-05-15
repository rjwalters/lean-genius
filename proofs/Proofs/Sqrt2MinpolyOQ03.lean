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

/-- **Main theorem (strategic sorry, capstone):** the class number of Q(√2) is 1.

Proof strategy (per S2 PREP chain, S4 ACT deliverable):
- `disc Q_sqrt2 = 8` (Marcus Chapter 5; PREP-3/4 verbatim norm-chain).
- Minkowski bound `M_K = (2!/2²)·√8 = √2 < 2`.
- Every nonzero ideal class has an integral representative of norm `< √2`,
  hence of norm 1, hence is the unit class.
- Therefore `|Cl_K| = 1`. -/
theorem Q_sqrt2_classNumber_eq_one :
    NumberField.classNumber Q_sqrt2 = 1 := by
  sorry

end Sqrt2MinpolyOQ03
