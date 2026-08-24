import Proofs.Erdos85ThreeSeparatorUniformWingFiberSizes

/-!
# Uniform R-fiber deviation profile

The R-fiber family has point degree
`d(x) + 1_{x∈U} = 1 + 1_{x∈C}`.  Thus its holes are exactly `U \ C`,
its degree-two points exactly `C \ U`, and all remaining points have degree
one.  Since `|U|=3a` and `|C|=a`, holes outnumber degree-two points by
exactly `2a`.  This is the numerical and pointwise content of (B36).
-/

open Finset

namespace Erdos85

noncomputable section

/-- Pointwise degree-locus classification in B36. -/
theorem uniform_Rfiber_exact_degree_loci
    {V : Type*} [DecidableEq V]
    (X C U : Finset V) (d : V → ℕ)
    (hCX : C ⊆ X)
    (hUX : U ⊆ X)
    (hdegree : ∀ x ∈ X,
      d x + (if x ∈ U then 1 else 0) =
        1 + (if x ∈ C then 1 else 0)) :
    (∀ x ∈ U \ C, d x = 0) ∧
      (∀ x ∈ C \ U, d x = 2) ∧
      (∀ x ∈ C ∩ U, d x = 1) ∧
      ∀ x ∈ X \ (C ∪ U), d x = 1 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro x hx
    have hp := hdegree x (hUX (Finset.mem_sdiff.mp hx).1)
    simp [(Finset.mem_sdiff.mp hx).1, (Finset.mem_sdiff.mp hx).2] at hp
    exact hp
  · intro x hx
    have hp := hdegree x (hCX (Finset.mem_sdiff.mp hx).1)
    simp [(Finset.mem_sdiff.mp hx).1, (Finset.mem_sdiff.mp hx).2] at hp
    exact hp
  · intro x hx
    have hparts := Finset.mem_inter.mp hx
    have hp := hdegree x (hCX hparts.1)
    simp [hparts.1, hparts.2] at hp
    exact hp
  · intro x hx
    have hparts := Finset.mem_sdiff.mp hx
    have hnot := hparts.2
    have hxnotC : x ∉ C := by
      intro hxC
      exact hnot (Finset.mem_union_left U hxC)
    have hxnotU : x ∉ U := by
      intro hxU
      exact hnot (Finset.mem_union_right C hxU)
    have hp := hdegree x hparts.1
    simpa [hxnotC, hxnotU] using hp

/-- Global imbalance in B36: the hole locus exceeds the degree-two locus
by exactly `2a`. -/
theorem uniform_Rfiber_hole_surplus
    {V : Type*} [DecidableEq V]
    (C U : Finset V) (a : ℕ)
    (hCcard : C.card = a)
    (hUcard : U.card = 3 * a) :
    (U \ C).card = (C \ U).card + 2 * a := by
  have hU := Finset.card_sdiff_add_card_inter U C
  have hC := Finset.card_sdiff_add_card_inter C U
  rw [Finset.inter_comm C U] at hC
  omega

end

end Erdos85

#print axioms Erdos85.uniform_Rfiber_exact_degree_loci
#print axioms Erdos85.uniform_Rfiber_hole_surplus
