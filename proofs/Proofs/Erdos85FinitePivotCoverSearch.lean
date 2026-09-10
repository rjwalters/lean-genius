import Proofs.Erdos85FiniteExactCoverSearch

namespace Erdos85

/-- At each step only candidates containing the least uncovered vertex are considered. -/
def finitePivotCoverSearch {V : Type*} [LinearOrder V]
    (D : List (Finset V)) : ℕ → Finset V → Bool
  | 0, R => decide (R = ∅)
  | n + 1, R => if h : R.Nonempty then
      D.any (fun S => decide (R.min' h ∈ S ∧ S ⊆ R) &&
        finitePivotCoverSearch D n (R \ S))
    else false

theorem finitePivotCoverSearch_of_family {V : Type*} [LinearOrder V]
    (D : List (Finset V)) (n : ℕ) (R : Finset V)
    (F : Finset (Finset V)) (hFD : ∀ S ∈ F, S ∈ D) (hcard : F.card = n)
    (hne : ∀ S ∈ F, S.Nonempty)
    (hdis : ∀ A ∈ F, ∀ B ∈ F, A ≠ B → Disjoint A B)
    (hcover : F.biUnion id = R) : finitePivotCoverSearch D n R = true := by
  induction n generalizing R F with
  | zero =>
    have hF : F = ∅ := Finset.card_eq_zero.mp hcard
    subst F
    have hR : R = ∅ := by simpa using hcover.symm
    simp [finitePivotCoverSearch, hR]
  | succ n ih =>
    have hRN : R.Nonempty := by
      obtain ⟨T,hT⟩ := Finset.card_pos.mp (show 0 < F.card by omega)
      obtain ⟨x,hx⟩ := hne T hT
      refine ⟨x, ?_⟩
      rw [← hcover]
      exact Finset.mem_biUnion.mpr ⟨T,hT,hx⟩
    have hp : R.min' hRN ∈ F.biUnion id := by
      rw [hcover]
      exact Finset.min'_mem R hRN
    obtain ⟨S,hS,hpS⟩ := Finset.mem_biUnion.mp hp
    change R.min' hRN ∈ S at hpS
    have hSR : S ⊆ R := by
      intro x hx
      rw [← hcover]
      exact Finset.mem_biUnion.mpr ⟨S,hS,hx⟩
    have hsub : ∀ T ∈ F.erase S, T ∈ D :=
      fun T hT => hFD T (Finset.mem_of_mem_erase hT)
    have hsize : (F.erase S).card = n := by
      rw [Finset.card_erase_of_mem hS, hcard]
      omega
    have hne' : ∀ T ∈ F.erase S, T.Nonempty :=
      fun T hT => hne T (Finset.mem_of_mem_erase hT)
    have hdis' : ∀ A ∈ F.erase S, ∀ B ∈ F.erase S, A ≠ B → Disjoint A B := by
      intro A hA B hB hAB
      exact hdis A (Finset.mem_of_mem_erase hA) B (Finset.mem_of_mem_erase hB) hAB
    have hc : (F.erase S).biUnion id = R \ S := by
      rw [disjoint_family_erase_union F S hS hdis, hcover]
    have hr := ih (R \ S) (F.erase S) hsub hsize hne' hdis' hc
    simp only [finitePivotCoverSearch, dif_pos hRN, List.any_eq_true]
    exact ⟨S, hFD S hS, by simp [hpS, hSR, hr]⟩

end Erdos85
#print axioms Erdos85.finitePivotCoverSearch_of_family
