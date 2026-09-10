import Proofs.Erdos85ThreeHighCrossColumns

namespace Erdos85

def threeHighColumnChoice (c : Fin 3 → Option (Fin 5)) : Finset (Fin 15) :=
  Finset.univ.filter fun i =>
    c ((@finProdFinEquiv 3 5).symm i).1 = some ((@finProdFinEquiv 3 5).symm i).2

theorem threeHighColumnChoice_covers (S : Finset (Fin 15))
    (hcap : ∀ k : Fin 3, (S.filter fun i => ((@finProdFinEquiv 3 5).symm i).1 = k).card ≤ 1) :
    ∃ c : Fin 3 → Option (Fin 5), threeHighColumnChoice c = S := by
  classical
  have hw : ∀ k : Fin 3, ∃ a : Option (Fin 5), ∀ x : Fin 5,
      (@finProdFinEquiv 3 5) (k,x) ∈ S ↔ a = some x := by
    intro k
    by_cases h : ∃ x : Fin 5, (@finProdFinEquiv 3 5) (k,x) ∈ S
    · obtain ⟨a,ha⟩ := h
      refine ⟨some a,?_⟩
      intro x
      constructor
      · intro hx
        have hax := Finset.card_le_one.mp (hcap k)
          ((@finProdFinEquiv 3 5) (k,a)) (by simp [ha])
          ((@finProdFinEquiv 3 5) (k,x)) (by simp [hx])
        have he := congrArg Prod.snd ((@finProdFinEquiv 3 5).injective hax)
        exact congrArg some he
      · intro he
        have he' := Option.some.inj he
        simpa only [← he'] using ha
    · refine ⟨none,?_⟩
      intro x
      constructor
      · intro hx
        exact False.elim (h ⟨x,hx⟩)
      · intro hn
        cases hn
  choose c hc using hw
  refine ⟨c,?_⟩
  ext i
  obtain ⟨⟨k,x⟩,rfl⟩ := (@finProdFinEquiv 3 5).surjective i
  simp only [threeHighColumnChoice,Finset.mem_filter,Finset.mem_univ,true_and,
    Equiv.symm_apply_apply]
  exact (hc k x).symm

def threeHighColumnOptions : List (Option (Fin 5)) := none :: (List.finRange 5).map some

theorem threeHighColumnOptions_complete (a : Option (Fin 5)) : a ∈ threeHighColumnOptions := by
  cases a <;> simp [threeHighColumnOptions]

def threeHighCompactColumnCandidates : List (Finset (Fin 15)) :=
  threeHighColumnOptions.flatMap fun a => threeHighColumnOptions.flatMap fun b =>
    threeHighColumnOptions.map fun c => threeHighColumnChoice ![a,b,c]

set_option maxRecDepth 100000 in
theorem threeHighCompactColumnCandidates_length : threeHighCompactColumnCandidates.length = 216 := by
  decide

theorem threeHighCompactColumnCandidates_complete (S : Finset (Fin 15))
    (hcap : ∀ k : Fin 3, (S.filter fun i => ((@finProdFinEquiv 3 5).symm i).1 = k).card ≤ 1) :
    S ∈ threeHighCompactColumnCandidates := by
  obtain ⟨c,rfl⟩ := threeHighColumnChoice_covers S hcap
  have he : ![c 0,c 1,c 2] = c := by
    funext i
    fin_cases i <;> rfl
  apply List.mem_flatMap.mpr
  refine ⟨c 0,threeHighColumnOptions_complete _,?_⟩
  apply List.mem_flatMap.mpr
  refine ⟨c 1,threeHighColumnOptions_complete _,?_⟩
  apply List.mem_map.mpr
  exact ⟨c 2,threeHighColumnOptions_complete _,by rw [he]⟩

end Erdos85
#print axioms Erdos85.threeHighColumnChoice_covers
#print axioms Erdos85.threeHighCompactColumnCandidates_length
#print axioms Erdos85.threeHighCompactColumnCandidates_complete
