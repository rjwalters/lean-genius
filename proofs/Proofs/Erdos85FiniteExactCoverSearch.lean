import Mathlib

namespace Erdos85

/-- Bounded exact-cover search without materializing subsets of the candidate family. -/
def finiteExactCoverSearch {V : Type*} [DecidableEq V]
    (D : List (Finset V)) : ℕ → Finset V → Bool
  | 0, R => decide (R = ∅)
  | n + 1, R => D.any fun S =>
      decide (S ⊆ R) && finiteExactCoverSearch D n (R \ S)

theorem disjoint_family_erase_union {V : Type*} [DecidableEq V]
    (F : Finset (Finset V)) (S : Finset V) (hS : S ∈ F)
    (hdis : ∀ A ∈ F, ∀ B ∈ F, A ≠ B → Disjoint A B) :
    (F.erase S).biUnion id = F.biUnion id \ S := by
  ext x
  constructor
  · intro hx
    obtain ⟨T,hT,hxT⟩ := Finset.mem_biUnion.mp hx
    obtain ⟨hTS,hTF⟩ := Finset.mem_erase.mp hT
    refine Finset.mem_sdiff.mpr ⟨Finset.mem_biUnion.mpr ⟨T,hTF,hxT⟩, ?_⟩
    intro hxS
    exact Finset.disjoint_left.mp (hdis T hTF S hS hTS) hxT hxS
  · intro hx
    obtain ⟨hxF,hxS⟩ := Finset.mem_sdiff.mp hx
    obtain ⟨T,hTF,hxT⟩ := Finset.mem_biUnion.mp hxF
    refine Finset.mem_biUnion.mpr ⟨T, Finset.mem_erase.mpr ⟨?_,hTF⟩,hxT⟩
    intro heq
    subst T
    exact hxS hxT

/-- Every disjoint candidate family is found by the recursive search. -/
theorem finiteExactCoverSearch_of_family {V : Type*} [DecidableEq V]
    (D : List (Finset V)) (n : ℕ) (R : Finset V)
    (F : Finset (Finset V)) (hFD : ∀ S ∈ F, S ∈ D) (hcard : F.card = n)
    (hdis : ∀ A ∈ F, ∀ B ∈ F, A ≠ B → Disjoint A B)
    (hcover : F.biUnion id = R) : finiteExactCoverSearch D n R = true := by
  induction n generalizing R F with
  | zero =>
    have hF : F = ∅ := Finset.card_eq_zero.mp hcard
    subst F
    have hR : R = ∅ := by simpa using hcover.symm
    simp [finiteExactCoverSearch, hR]
  | succ n ih =>
    obtain ⟨S,hS⟩ := Finset.card_pos.mp (show 0 < F.card by omega)
    have hSR : S ⊆ R := by
      intro x hx
      rw [← hcover]
      exact Finset.mem_biUnion.mpr ⟨S,hS,hx⟩
    have hsub : ∀ T ∈ F.erase S, T ∈ D :=
      fun T hT => hFD T (Finset.mem_of_mem_erase hT)
    have hsize : (F.erase S).card = n := by
      rw [Finset.card_erase_of_mem hS, hcard]
      omega
    have hdis' : ∀ A ∈ F.erase S, ∀ B ∈ F.erase S, A ≠ B → Disjoint A B := by
      intro A hA B hB hAB
      exact hdis A (Finset.mem_of_mem_erase hA) B (Finset.mem_of_mem_erase hB) hAB
    have hc : (F.erase S).biUnion id = R \ S := by
      rw [disjoint_family_erase_union F S hS hdis, hcover]
    have hr := ih (R \ S) (F.erase S) hsub hsize hdis' hc
    simp only [finiteExactCoverSearch, List.any_eq_true]
    exact ⟨S, hFD S hS, by simp [hSR, hr]⟩

end Erdos85
#print axioms Erdos85.disjoint_family_erase_union
#print axioms Erdos85.finiteExactCoverSearch_of_family
