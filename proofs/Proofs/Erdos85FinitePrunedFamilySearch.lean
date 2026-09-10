import Proofs.Erdos85FiniteExactCoverSearch

namespace Erdos85

/-- Pivot search with a prefix test on the selected blocks and a terminal test. -/
def finitePrunedFamilySearch {V : Type*} [LinearOrder V]
    (D : List (Finset V)) (keep : Finset (Finset V) → Bool) (accept : Finset (Finset V) → Bool) :
    ℕ → Finset V → Finset (Finset V) → Bool
  | 0, R, chosen => keep chosen && decide (R = ∅) && accept chosen
  | n + 1, R, chosen => keep chosen && (if h : R.Nonempty then
      D.any (fun S => decide (R.min' h ∈ S ∧ S ⊆ R) &&
        finitePrunedFamilySearch D keep accept n (R \ S) (insert S chosen))
    else false)

theorem finitePrunedFamilySearch_of_family {V : Type*} [LinearOrder V]
    (D : List (Finset V)) (keep : Finset (Finset V) → Bool) (accept : Finset (Finset V) → Bool)
    (n : ℕ) (R : Finset V) (F chosen : Finset (Finset V))
    (hFD : ∀ S ∈ F, S ∈ D) (hcard : F.card = n)
    (hne : ∀ S ∈ F, S.Nonempty)
    (hdis : ∀ A ∈ F, ∀ B ∈ F, A ≠ B → Disjoint A B)
    (hcover : F.biUnion id = R)
    (hkeep : ∀ K, K ⊆ F ∪ chosen → keep K = true) (haccept : accept (F ∪ chosen) = true) :
    finitePrunedFamilySearch D keep accept n R chosen = true := by
  induction n generalizing R F chosen with
  | zero =>
    have hF : F = ∅ := Finset.card_eq_zero.mp hcard
    subst F
    have hR : R = ∅ := by simpa using hcover.symm
    have hk : keep chosen = true := hkeep chosen (by simp)
    simpa [finitePrunedFamilySearch, hR, hk] using haccept
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
    have he : F.erase S ∪ insert S chosen = F ∪ chosen := by
      rw [Finset.union_insert, ← Finset.insert_union, Finset.insert_erase hS]
    have ha : accept (F.erase S ∪ insert S chosen) = true := by rwa [he]
    have hk : keep chosen = true := hkeep chosen Finset.subset_union_right
    have hkeep' : ∀ K, K ⊆ F.erase S ∪ insert S chosen → keep K = true := by
      intro K hK
      apply hkeep K
      rwa [he] at hK
    have hr := ih (R \ S) (F.erase S) (insert S chosen) hsub hsize hne' hdis' hc hkeep' ha
    simp only [finitePrunedFamilySearch, hk, Bool.true_and, dif_pos hRN, List.any_eq_true]
    exact ⟨S, hFD S hS, by simp [hpS, hSR, hr]⟩

end Erdos85
#print axioms Erdos85.finitePrunedFamilySearch_of_family
