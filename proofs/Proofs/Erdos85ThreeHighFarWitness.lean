import Proofs.Erdos85ThreeHighRootRowPruning

namespace Erdos85

/-- A row of size at least two, with at most one near entry, has a far entry. -/
theorem threeHighRootRowGate_far_witness (S : Finset (Fin 8))
    (hS : threeHighRootRowGate S = true) (hs : 2 ≤ S.card) :
    ∃ j ∈ S, 6 ≤ j.val := by
  by_contra h
  have hall : ∀ j ∈ S, j.val < 6 := by
    intro j hj
    by_contra hn
    exact h ⟨j,hj,by omega⟩
  have he : S.filter (fun j => j.val < 6) = S := Finset.filter_eq_self.mpr hall
  unfold threeHighRootRowGate at hS
  simp only [decide_eq_true_eq,he] at hS
  omega

attribute [local irreducible] threeHighCrossDomain

theorem threeHighCrossDomain_low_degree_far
    (UAdj : Fin 15 → Fin 15 → Bool) (RAdj : Fin 8 → Fin 8 → Bool)
    (cross : ThreeHighCross) (hc : cross ∈ threeHighCrossDomain UAdj RAdj)
    (i : Fin 15) (hi : encodedRowDegree (UAdj i) ≤ 2) :
    ∃ j : Fin 8, 6 ≤ j.val ∧ cross i j = true := by
  have hC4 := ((mem_threeHighCrossDomain_iff UAdj RAdj cross).mp hc).1
  have hr := threeHighRootRowGate_of_c4 UAdj RAdj cross hC4 i
  have hm := (threeHighCrossDomain_margins UAdj RAdj cross hc).1 i
  have hs : 2 ≤ (threeHighCrossRows cross i).card := by
    change 2 ≤ encodedRowDegree (cross i)
    omega
  obtain ⟨j,hj,hfar⟩ := threeHighRootRowGate_far_witness _ hr hs
  exact ⟨j,hfar,by simpa [threeHighCrossRows] using hj⟩

end Erdos85
#print axioms Erdos85.threeHighRootRowGate_far_witness
#print axioms Erdos85.threeHighCrossDomain_low_degree_far
