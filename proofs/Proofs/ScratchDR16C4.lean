import Mathlib

open Polynomial

attribute [instance 10] DivisionRing.toRatAlgebra

-- With lowered priority, do the original failures now synthesize?
example : Normal ℚ ((X : ℚ[X]) ^ 4 - C 2).SplittingField := inferInstance
example : IsSplittingField ℚ ((X:ℚ[X]) ^ 4 - C 2).SplittingField ((X:ℚ[X]) ^ 4 - C 2) :=
  inferInstance
example (n : ℕ) : IsCyclotomicExtension {n} ℚ (CyclotomicField n ℚ) := inferInstance
example : True := by
  set p := (X : ℚ[X]) ^ 4 - C 2
  haveI : Normal ℚ p.SplittingField := inferInstance
  trivial
