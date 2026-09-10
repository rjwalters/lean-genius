import Mathlib

/-! Full empty-support adjacency in retained coordinates U0..14, R15..22, root23. -/
namespace Erdos85
open SimpleGraph

def threeHighEmptyUIndex (i : Fin 15) : Fin 24 := Fin.castAdd 1 (Fin.castAdd 8 i)
def threeHighEmptyRIndex (j : Fin 8) : Fin 24 := Fin.castAdd 1 (Fin.natAdd 15 j)

def threeHighEmptySplit (p : Fin 24) : (Fin 15 ⊕ Fin 8) ⊕ Fin 1 :=
  (Equiv.sumCongr (@finSumFinEquiv 15 8).symm (Equiv.refl (Fin 1)))
    ((@finSumFinEquiv 23 1).symm p)

@[simp] theorem threeHighEmptySplit_u (i : Fin 15) :
    threeHighEmptySplit (threeHighEmptyUIndex i) = Sum.inl (Sum.inl i) := by
  change Sum.map ((@finSumFinEquiv 15 8).symm) (id : Fin 1 → Fin 1) ((@finSumFinEquiv 23 1).symm (Fin.castAdd 1 (Fin.castAdd 8 i))) = _
  rw [finSumFinEquiv_symm_apply_castAdd]
  change Sum.inl ((@finSumFinEquiv 15 8).symm (Fin.castAdd 8 i)) = _
  rw [finSumFinEquiv_symm_apply_castAdd]
@[simp] theorem threeHighEmptySplit_r (j : Fin 8) :
    threeHighEmptySplit (threeHighEmptyRIndex j) = Sum.inl (Sum.inr j) := by
  change Sum.map ((@finSumFinEquiv 15 8).symm) (id : Fin 1 → Fin 1) ((@finSumFinEquiv 23 1).symm (Fin.castAdd 1 (Fin.natAdd 15 j))) = _
  rw [finSumFinEquiv_symm_apply_castAdd]
  change Sum.inl ((@finSumFinEquiv 15 8).symm (Fin.natAdd 15 j)) = _
  rw [finSumFinEquiv_symm_apply_natAdd]
@[simp] theorem threeHighEmptySplit_root : threeHighEmptySplit 23 = Sum.inr 0 := by
  change Sum.map ((@finSumFinEquiv 15 8).symm) (id : Fin 1 → Fin 1) ((@finSumFinEquiv 23 1).symm (Fin.natAdd 23 (0 : Fin 1))) = _
  rw [finSumFinEquiv_symm_apply_natAdd]
  rfl

def threeHighEmptyAdj (UAdj : Fin 15 → Fin 15 → Bool) (RAdj : Fin 8 → Fin 8 → Bool)
    (cross : Fin 15 → Fin 8 → Bool) (p q : Fin 24) : Bool :=
  match threeHighEmptySplit p, threeHighEmptySplit q with
  | Sum.inl (Sum.inl i), Sum.inl (Sum.inl j) => UAdj i j
  | Sum.inl (Sum.inr i), Sum.inl (Sum.inr j) => RAdj i j
  | Sum.inl (Sum.inl i), Sum.inl (Sum.inr j) => cross i j
  | Sum.inl (Sum.inr j), Sum.inl (Sum.inl i) => cross i j
  | Sum.inr _, Sum.inl (Sum.inr j) => decide (j.val < 6)
  | Sum.inl (Sum.inr j), Sum.inr _ => decide (j.val < 6)
  | _, _ => false

private theorem empty_index_cases (P : Fin 24 → Prop)
    (hU : ∀ i, P (threeHighEmptyUIndex i))
    (hR : ∀ j, P (threeHighEmptyRIndex j)) (hroot : P 23) : ∀ p, P p := by
  intro p
  refine Fin.addCases (m := 23) (n := 1) (fun k => ?_) (fun k => ?_) p
  · exact Fin.addCases (m := 15) (n := 8) hU hR k
  · have hk : k = 0 := Subsingleton.elim _ _
    subst k
    exact hroot

theorem threeHighEmptyAdj_eq_graph
    (H : SimpleGraph (Fin 24)) [DecidableRel H.Adj]
    (UAdj : Fin 15 → Fin 15 → Bool) (RAdj : Fin 8 → Fin 8 → Bool)
    (hU : ∀ i j, decide (H.Adj (threeHighEmptyUIndex i) (threeHighEmptyUIndex j)) = UAdj i j)
    (hR : ∀ i j, decide (H.Adj (threeHighEmptyRIndex i) (threeHighEmptyRIndex j)) = RAdj i j)
    (huU : ∀ i, ¬ H.Adj 23 (threeHighEmptyUIndex i))
    (huR : ∀ j, H.Adj 23 (threeHighEmptyRIndex j) ↔ j.val < 6) :
    ∀ p q, decide (H.Adj p q) = threeHighEmptyAdj UAdj RAdj
      (fun i j => decide (H.Adj (threeHighEmptyUIndex i) (threeHighEmptyRIndex j))) p q := by
  apply empty_index_cases
  · intro i
    apply empty_index_cases
    · intro j
      simpa [threeHighEmptyAdj] using hU i j
    · intro j
      simp [threeHighEmptyAdj]
    · have hn : ¬ H.Adj (threeHighEmptyUIndex i) 23 := fun h => huU i h.symm
      simp [threeHighEmptyAdj, hn]
  · intro i
    apply empty_index_cases
    · intro j
      simp [threeHighEmptyAdj, H.adj_comm]
    · intro j
      simpa [threeHighEmptyAdj] using hR i j
    · simpa [threeHighEmptyAdj] using Bool.decide_congr ((H.adj_comm _ _).trans (huR i))
  · apply empty_index_cases
    · intro j
      simp [threeHighEmptyAdj, huU j]
    · intro j
      simpa [threeHighEmptyAdj] using Bool.decide_congr (huR j)
    · simp [threeHighEmptyAdj]

end Erdos85
#print axioms Erdos85.threeHighEmptyAdj_eq_graph
