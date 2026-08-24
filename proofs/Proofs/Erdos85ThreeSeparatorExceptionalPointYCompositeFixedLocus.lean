import Proofs.Erdos85ThreeSeparatorExceptionalPointYTransversalSaturation

/-!
# Fixed locus of the large-shore composite matching

For `c ∈ Y`, compose the exact transversal with the exceptional-point
matching.  The composite lands in K, and any return to the endpoint defect
clique must be the original point.  Its return and fixed loci are therefore
exactly `K ∩ X`, as recorded in (B17Y''').
-/

open Finset

namespace Erdos85

noncomputable section

/-- Finite-set core of B17Y'''. -/
theorem composite_return_and_fixedLocus_eq_cover_inter
    {V : Type*} [DecidableEq V]
    (X K : Finset V) (θ : V → V)
    (himageK : ∀ x ∈ X, θ x ∈ K)
    (hreturn : ∀ x ∈ X, θ x ∈ X → θ x = x)
    (hfix : ∀ x ∈ X, θ x = x ↔ x ∈ K) :
    (∀ x ∈ X, θ x ∈ X ↔ x ∈ K) ∧
      X.image θ ∩ X = K ∩ X ∧
      X.filter (fun x ↦ θ x = x) = K ∩ X := by
  have hreturnIff : ∀ x ∈ X, θ x ∈ X ↔ x ∈ K := by
    intro x hx
    constructor
    · intro hθX
      exact (hfix x hx).mp (hreturn x hx hθX)
    · intro hxK
      rw [(hfix x hx).mpr hxK]
      exact hx
  refine ⟨hreturnIff, ?_, ?_⟩
  · ext z
    constructor
    · intro hz
      obtain ⟨hzImage, hzX⟩ := Finset.mem_inter.mp hz
      obtain ⟨x, hxX, hθx⟩ := Finset.mem_image.mp hzImage
      subst z
      exact Finset.mem_inter.mpr ⟨himageK x hxX, hzX⟩
    · intro hz
      obtain ⟨hzK, hzX⟩ := Finset.mem_inter.mp hz
      have hθz : θ z = z := (hfix z hzX).mpr hzK
      exact Finset.mem_inter.mpr
        ⟨Finset.mem_image.mpr ⟨z, hzX, hθz⟩, hzX⟩
  · ext x
    simp only [Finset.mem_filter, Finset.mem_inter]
    constructor
    · rintro ⟨hxX, hθx⟩
      exact ⟨(hfix x hxX).mp hθx, hxX⟩
    · rintro ⟨hxK, hxX⟩
      exact ⟨hxX, (hfix x hxX).mpr hxK⟩

end

end Erdos85

#print axioms Erdos85.composite_return_and_fixedLocus_eq_cover_inter
