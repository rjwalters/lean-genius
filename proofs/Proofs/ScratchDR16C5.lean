import Mathlib

open Polynomial

attribute [instance 10] DivisionRing.toRatAlgebra
set_option synthInstance.maxHeartbeats 80000

example (p : ℕ) [Fact p.Prime] (H : Subgroup (Polynomial.cyclotomic p ℚ).Gal)
    (hn : H.Normal) : True := by
  haveI := hn
  haveI hGal : IsGalois ℚ (Polynomial.cyclotomic p ℚ).SplittingField := sorry
  let e := IsGalois.normalAutEquivQuotient H
  haveI : IsGalois ℚ ↥(IntermediateField.fixedField H) := inferInstance
  trivial
