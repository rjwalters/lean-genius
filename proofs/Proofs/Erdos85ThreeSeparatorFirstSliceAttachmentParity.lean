import Proofs.Erdos85ThreeSeparatorFirstSliceWLocation

/-!
# Attachment-fiber parity on the first slice

Let `M` be the X-points that are not defect-neighbors of the exceptional
separator point.  B18 puts the complementary attachment fiber `X \ M`
inside `K`.  Hence the K-endpoints split exactly between `M` and that
fiber.  Since the total number of endpoints is even, the two pieces have
the same parity.  This is the set-theoretic and parity core of (B24).
-/

open Finset

namespace Erdos85

noncomputable section

/-- Arithmetic parity core of B24. -/
theorem parity_eq_of_even_add
    (u v total : ℕ)
    (htotal : Even total)
    (hsum : u + v = total) :
    u % 2 = v % 2 := by
  obtain ⟨t, rfl⟩ := htotal
  omega

/-- Generic endpoint split: if `M ⊆ X` and every point of `X \ M` belongs
to `K`, then the K-points of `X` partition as `K∩M` and `X\M`. -/
theorem cover_inter_split_by_contained_complement
    {V : Type*} [DecidableEq V]
    (X K M : Finset V)
    (hMX : M ⊆ X)
    (hcompK : X \ M ⊆ K) :
    (K ∩ M).card + (X \ M).card = (K ∩ X).card := by
  have hdisj : Disjoint (K ∩ M) (X \ M) := by
    rw [Finset.disjoint_left]
    intro x hxKM hxXM
    exact (Finset.mem_sdiff.mp hxXM).2 (Finset.mem_inter.mp hxKM).2
  have hunion : (K ∩ M) ∪ (X \ M) = K ∩ X := by
    ext x
    simp only [Finset.mem_union, Finset.mem_inter, Finset.mem_sdiff]
    constructor
    · rintro (⟨hxK, hxM⟩ | ⟨hxX, hxnotM⟩)
      · exact ⟨hxK, hMX hxM⟩
      · have hxcomp : x ∈ X \ M := Finset.mem_sdiff.mpr ⟨hxX, hxnotM⟩
        exact ⟨hcompK hxcomp, hxX⟩
    · rintro ⟨hxK, hxX⟩
      by_cases hxM : x ∈ M
      · exact Or.inl ⟨hxK, hxM⟩
      · exact Or.inr ⟨hxX, hxM⟩
  have hc := Finset.card_union_of_disjoint hdisj
  rw [hunion] at hc
  exact hc.symm

/-- Finset form of B24: exact endpoint counts, subtraction form, and parity
coupling for the exceptional attachment fiber. -/
theorem firstSlice_exceptional_attachment_endpoint_split
    {V : Type*} [DecidableEq V]
    (X K M : Finset V) (m : ℕ)
    (hMX : M ⊆ X)
    (hcompK : X \ M ⊆ K)
    (hcompCard : (X \ M).card = m)
    (hkXeven : Even (K ∩ X).card) :
    (K ∩ M).card + m = (K ∩ X).card ∧
      (K ∩ M).card = (K ∩ X).card - m ∧
      (K ∩ M).card % 2 = m % 2 := by
  have hsum := cover_inter_split_by_contained_complement X K M hMX hcompK
  rw [hcompCard] at hsum
  refine ⟨hsum, ?_, parity_eq_of_even_add
    (K ∩ M).card m (K ∩ X).card hkXeven hsum⟩
  omega

end

end Erdos85

#print axioms Erdos85.parity_eq_of_even_add
#print axioms Erdos85.cover_inter_split_by_contained_complement
#print axioms Erdos85.firstSlice_exceptional_attachment_endpoint_split
