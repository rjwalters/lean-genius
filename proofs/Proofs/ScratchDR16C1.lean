import Mathlib

open Polynomial

-- Test 1: Normal instance on SplittingField with set-var
example : True := by
  set p := (X : ℚ[X]) ^ 4 - C 2
  haveI : Normal ℚ p.SplittingField := inferInstance
  trivial

-- Test 2: Normal without set
example : Normal ℚ ((X : ℚ[X]) ^ 4 - C 2).SplittingField := inferInstance

-- Test 3: IsSplittingField synthesis
example : IsSplittingField ℚ ((X:ℚ[X]) ^ 4 - C 2).SplittingField ((X:ℚ[X]) ^ 4 - C 2) :=
  inferInstance

-- Test 4: cyclotomic synthesis without compat shim
example (n : ℕ) : IsCyclotomicExtension {n} ℚ (CyclotomicField n ℚ) := inferInstance
