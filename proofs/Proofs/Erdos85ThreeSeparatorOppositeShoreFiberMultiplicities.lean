import Proofs.Erdos85ThreeSeparatorOppositeShoreFiberPartition

/-!
# Multiplicities in the opposite-shore fiber partitions

The B47 partition theorem supplies disjoint exhaustive fibers.  The signed
fiber-size profiles determine their multiplicities: two short fibers in the
Y-location and one short fiber in the X-location.
-/

open Finset

namespace Erdos85

/-- B47Y multiplicities: exactly the two K-centers give a-point fibers. -/
theorem oppositeShore_Y_fiber_multiplicities
    {V : Type*} [DecidableEq V]
    (Z K : Finset V) (fiberCard : V → ℕ) (q a : ℕ)
    (hZcard : Z.card = q)
    (hKcenters : (Z ∩ K).card = 2)
    (hprofile : ∀ z ∈ Z,
      fiberCard z + (if z ∈ K then 1 else 0) = a + 1) :
    (Z.filter fun z ↦ fiberCard z = a) = Z ∩ K ∧
      (Z.filter fun z ↦ fiberCard z = a + 1) = Z \ K ∧
      (Z.filter fun z ↦ fiberCard z = a).card = 2 ∧
      (Z.filter fun z ↦ fiberCard z = a + 1).card = q - 2 := by
  have hshort : (Z.filter fun z ↦ fiberCard z = a) = Z ∩ K := by
    ext z
    by_cases hz : z ∈ Z
    · have hp := hprofile z hz
      by_cases hzK : z ∈ K <;> simp [hz, hzK] at hp ⊢ <;> omega
    · simp [hz]
  have hlong : (Z.filter fun z ↦ fiberCard z = a + 1) = Z \ K := by
    ext z
    by_cases hz : z ∈ Z
    · have hp := hprofile z hz
      by_cases hzK : z ∈ K <;> simp [hz, hzK] at hp ⊢ <;> omega
    · simp [hz]
  refine ⟨hshort, hlong, ?_, ?_⟩
  · rw [hshort, hKcenters]
  · rw [hlong, Finset.card_sdiff, Finset.inter_comm, hKcenters, hZcard]

/-- B47X multiplicities: exactly the unique R-center gives a
`(b-1)`-point fiber. -/
theorem oppositeShore_X_fiber_multiplicities
    {V : Type*} [DecidableEq V]
    (Z R : Finset V) (fiberCard : V → ℕ) (q b : ℕ)
    (hZcard : Z.card = q)
    (hb : 1 ≤ b)
    (hRcenter : (Z ∩ R).card = 1)
    (hprofile : ∀ z ∈ Z,
      fiberCard z + (if z ∈ R then 1 else 0) = b) :
    (Z.filter fun z ↦ fiberCard z = b - 1) = Z ∩ R ∧
      (Z.filter fun z ↦ fiberCard z = b) = Z \ R ∧
      (Z.filter fun z ↦ fiberCard z = b - 1).card = 1 ∧
      (Z.filter fun z ↦ fiberCard z = b).card = q - 1 := by
  have hshort : (Z.filter fun z ↦ fiberCard z = b - 1) = Z ∩ R := by
    ext z
    by_cases hz : z ∈ Z
    · have hp := hprofile z hz
      by_cases hzR : z ∈ R <;> simp [hz, hzR] at hp ⊢ <;> omega
    · simp [hz]
  have hlong : (Z.filter fun z ↦ fiberCard z = b) = Z \ R := by
    ext z
    by_cases hz : z ∈ Z
    · have hp := hprofile z hz
      by_cases hzR : z ∈ R <;> simp [hz, hzR] at hp ⊢ <;> omega
    · simp [hz]
  refine ⟨hshort, hlong, ?_, ?_⟩
  · rw [hshort, hRcenter]
  · rw [hlong, Finset.card_sdiff, Finset.inter_comm, hRcenter, hZcard]

#print axioms oppositeShore_Y_fiber_multiplicities
#print axioms oppositeShore_X_fiber_multiplicities

end Erdos85
