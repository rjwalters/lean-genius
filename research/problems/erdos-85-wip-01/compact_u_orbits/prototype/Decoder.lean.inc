
namespace UPrototype
open Erdos85
/-- Decode the checked disjunction using the actual encoded C4-free premise. -/
theorem covered (p : Fin 120) (hf : encodedC4Free (adj 66 66 p) = true) :
    ∃ (r : Fin 55) (s : Fin 8) (sw : Bool), Function.Bijective (label s sw) ∧
      ∀ x y, adj 66 66 p x y = adj (repA r) (repB r) (repP r) (label s sw x) (label s sw y) := by
  have h := checked p
  cases hc : cert p with
  | cycle x y a b =>
    simp only [check,hc] at h
    obtain ⟨hxy,hab,hxa,hxb,hya,hyb⟩ := h
    unfold encodedC4Free at hf
    simp only [decide_eq_true_eq] at hf
    have hbnd := hf x y hxy
    have ha : a ∈ Finset.univ.filter (fun i => adj 66 66 p x i && adj 66 66 p y i) := by
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _,?_⟩
      simp only [Bool.and_eq_true]
      exact ⟨hxa,hya⟩
    have hb : b ∈ Finset.univ.filter (fun i => adj 66 66 p x i && adj 66 66 p y i) := by
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _,?_⟩
      simp only [Bool.and_eq_true]
      exact ⟨hxb,hyb⟩
    exact False.elim (hab (Finset.card_le_one.mp hbnd a ha b hb))
  | orbit r s sw =>
    exact ⟨r,s,sw,by simpa only [check,hc] using h⟩
end UPrototype
#print axioms UPrototype.covered
