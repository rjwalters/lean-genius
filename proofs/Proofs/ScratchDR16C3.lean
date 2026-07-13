import Mathlib

open Polynomial

-- A: explicit application
example : Normal ℚ ((X : ℚ[X]) ^ 4 - C 2).SplittingField :=
  Polynomial.SplittingField.instNormal _

-- B: explicit application IsSplittingField
example : IsSplittingField ℚ ((X:ℚ[X]) ^ 4 - C 2).SplittingField ((X:ℚ[X]) ^ 4 - C 2) :=
  Polynomial.IsSplittingField.splittingField _

-- C: does a general ℚ-specialized re-registration fire?
instance scratchNormalRat (f : ℚ[X]) : Normal ℚ f.SplittingField :=
  Polynomial.SplittingField.instNormal f

example : Normal ℚ ((X : ℚ[X]) ^ 4 - C 2).SplittingField := inferInstance

-- D: generic-over-F test: does it fail for variable F too, or only ℚ?
example (F : Type) [Field F] (f : F[X]) : Normal F f.SplittingField := inferInstance
