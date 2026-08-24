import Proofs.Erdos85ThreeSeparatorUniformRFiberDeviation

/-!
# The first-slice R-fiber normal form

The union of the two-point R-fibers has degree profile
`deg_M(x) + 1_{U_P}(x) = 1 + 1_u(x)`.  With three P-recipients, this
immediately gives the two alternatives in (B28): a matching with two holes,
or one degree-two center together with three holes.
-/

open Finset

namespace Erdos85

/-- Exact degree-locus form of the B28 dichotomy. -/
theorem firstSlice_RFiber_degree_locus_normalForm
    {V : Type*} [DecidableEq V]
    (X U : Finset V) (u : V) (d : V → ℕ)
    (huX : u ∈ X)
    (hUX : U ⊆ X)
    (hUcard : U.card = 3)
    (hprofile : ∀ x ∈ X,
      d x + (if x ∈ U then 1 else 0) = 1 + (if x = u then 1 else 0)) :
    (u ∈ U ∧
        (∀ x ∈ X, d x ≤ 1) ∧
        (X.filter fun x ↦ d x = 0) = U.erase u ∧
        (X.filter fun x ↦ d x = 1) = X \ (U.erase u) ∧
        (X.filter fun x ↦ d x = 0).card = 2) ∨
      (u ∉ U ∧
        (X.filter fun x ↦ d x = 2) = {u} ∧
        (X.filter fun x ↦ d x = 0) = U ∧
        (X.filter fun x ↦ d x = 1) = X \ insert u U ∧
      (X.filter fun x ↦ d x = 0).card = 3) := by
  have hsingletonX : ({u} : Finset V) ⊆ X := by simpa using huX
  have hprofile' : ∀ x ∈ X,
      d x + (if x ∈ U then 1 else 0) =
        1 + (if x ∈ ({u} : Finset V) then 1 else 0) := by
    intro x hx
    simpa using hprofile x hx
  obtain ⟨hzero, htwo, honeBoth, honeOutside⟩ :=
    uniform_Rfiber_exact_degree_loci X ({u} : Finset V) U d
      hsingletonX hUX hprofile'
  by_cases huU : u ∈ U
  · left
    have hd : ∀ x ∈ X, d x = if x ∈ U ∧ x ≠ u then 0 else 1 := by
      intro x hx
      by_cases hxU : x ∈ U
      · by_cases hxu : x = u
        · subst x
          simpa [huU] using honeBoth u (by simp [huU])
        · simpa [hxU, hxu] using hzero x (Finset.mem_sdiff.mpr ⟨hxU, by simpa⟩)
      · have hxOutside : x ∈ X \ (({u} : Finset V) ∪ U) := by
          have hxu : x ≠ u := by
            intro h
            subst x
            exact hxU huU
          refine Finset.mem_sdiff.mpr ⟨hx, ?_⟩
          simp [hxU, hxu]
        simpa [hxU] using honeOutside x hxOutside
    refine ⟨huU, ?_, ?_, ?_, ?_⟩
    · intro x hx
      rw [hd x hx]
      split <;> omega
    · ext x
      by_cases hx : x ∈ X
      · simp [hx, hd x hx, and_comm]
      · have hxU : x ∉ U := fun h ↦ hx (hUX h)
        simp [hx, hxU]
    · ext x
      by_cases hx : x ∈ X
      · simp [hx, hd x hx, and_comm]
      · have hxU : x ∉ U := fun h ↦ hx (hUX h)
        simp [hx, hxU]
    · rw [show (X.filter fun x ↦ d x = 0) = U.erase u by
        ext x
        by_cases hx : x ∈ X
        · simp [hx, hd x hx, and_comm]
        · have hxU : x ∉ U := fun h ↦ hx (hUX h)
          simp [hx, hxU], Finset.card_erase_of_mem huU, hUcard]
  · right
    have hd : ∀ x ∈ X, d x = if x = u then 2 else if x ∈ U then 0 else 1 := by
      intro x hx
      by_cases hxu : x = u
      · subst x
        simpa [huU] using htwo u (by simp [huU])
      · by_cases hxU : x ∈ U
        · simpa [hxu, hxU] using hzero x
            (Finset.mem_sdiff.mpr ⟨hxU, by simpa⟩)
        · have hxOutside : x ∈ X \ (({u} : Finset V) ∪ U) := by
            refine Finset.mem_sdiff.mpr ⟨hx, ?_⟩
            simp [hxu, hxU]
          simpa [hxu, hxU] using honeOutside x hxOutside
    refine ⟨huU, ?_, ?_, ?_, ?_⟩
    · ext x
      by_cases hx : x ∈ X
      · by_cases hxu : x = u
        · subst x
          simp [huX, hd u huX]
        · by_cases hxU : x ∈ U <;> simp [hx, hd x hx, hxu, hxU]
      · have hxU : x ∉ U := fun h ↦ hx (hUX h)
        have hxu : x ≠ u := fun h ↦ hx (h ▸ huX)
        simp [hx, hxu]
    · ext x
      by_cases hx : x ∈ X
      · by_cases hxu : x = u
        · subst x
          simp [huX, hd u huX, huU]
        · by_cases hxU : x ∈ U <;> simp [hx, hd x hx, hxu, hxU]
      · have hxU : x ∉ U := fun h ↦ hx (hUX h)
        simp [hx, hxU]
    · ext x
      by_cases hx : x ∈ X
      · by_cases hxu : x = u
        · subst x
          simp [huX, hd u huX, huU]
        · by_cases hxU : x ∈ U <;> simp [hx, hd x hx, hxu, hxU]
      · have hxU : x ∉ U := fun h ↦ hx (hUX h)
        have hxu : x ≠ u := fun h ↦ hx (h ▸ huX)
        simp [hx, hxU, hxu]
    · rw [show (X.filter fun x ↦ d x = 0) = U by
        ext x
        by_cases hx : x ∈ X
        · by_cases hxu : x = u
          · subst x
            simp [huX, hd u huX, huU]
          · by_cases hxU : x ∈ U <;> simp [hx, hd x hx, hxu, hxU]
        · have hxU : x ∉ U := fun h ↦ hx (hUX h)
          simp [hx, hxU], hUcard]

#print axioms firstSlice_RFiber_degree_locus_normalForm

end Erdos85
