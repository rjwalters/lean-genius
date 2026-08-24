import Proofs.Erdos85ThreeSeparatorPositiveSpikePacking

/-!
# The endpoint three-separator shore is a clique

At the positive-spike endpoint, the small shore has `q-2` vertices.  Each
vertex uses exactly two of its `q-1` defect edges on the separator and has no
other external defect edge.  The remaining `q-3` edges therefore saturate
all other vertices of the shore.  This is equation (B11).
-/

open Finset SimpleGraph

namespace Erdos85

/-- Generic saturation form of B11: a `(q-2)`-vertex shore with total defect
degree `q-1` and exactly two separator attachments is a defect clique. -/
theorem shore_pairwise_adj_of_degree_pred_and_two_attachments
    {V : Type*} [Fintype V] [DecidableEq V]
    (D : SimpleGraph V) [DecidableRel D.Adj]
    (X W : Finset V) (q : ℕ) (hq : 3 ≤ q)
    (hXcard : X.card = q - 2) (hXW : Disjoint X W)
    (hdeg : ∀ x ∈ X, D.degree x = q - 1)
    (hattach : ∀ x ∈ X, (D.neighborFinset x ∩ W).card = 2)
    (hclosed : ∀ x ∈ X, D.neighborFinset x ⊆ X ∪ W) :
    (X : Set V).Pairwise D.Adj := by
  have hinter (x : V) (hx : x ∈ X) :
      D.neighborFinset x ∩ X = X.erase x := by
    have hsplit : D.neighborFinset x =
        (D.neighborFinset x ∩ X) ∪ (D.neighborFinset x ∩ W) := by
      ext z
      simp only [Finset.mem_inter, Finset.mem_union]
      constructor
      · intro hz
        rcases Finset.mem_union.mp (hclosed x hx hz) with hzX | hzW
        · exact Or.inl ⟨hz, hzX⟩
        · exact Or.inr ⟨hz, hzW⟩
      · rintro (⟨hz, -⟩ | ⟨hz, -⟩) <;> exact hz
    have hparts : Disjoint (D.neighborFinset x ∩ X)
        (D.neighborFinset x ∩ W) := by
      apply Finset.disjoint_left.mpr
      intro z hzX hzW
      exact Finset.disjoint_left.mp hXW
        (Finset.mem_inter.mp hzX).2 (Finset.mem_inter.mp hzW).2
    have hcardSplit : D.degree x =
        (D.neighborFinset x ∩ X).card + (D.neighborFinset x ∩ W).card := by
      calc
        D.degree x = (D.neighborFinset x).card :=
          (D.card_neighborFinset_eq_degree x).symm
        _ = ((D.neighborFinset x ∩ X) ∪
            (D.neighborFinset x ∩ W)).card := congrArg Finset.card hsplit
        _ = _ := Finset.card_union_of_disjoint hparts
    have hinterCard : (D.neighborFinset x ∩ X).card = X.card - 1 := by
      rw [hdeg x hx, hattach x hx] at hcardSplit
      rw [hXcard]
      omega
    have hsub : D.neighborFinset x ∩ X ⊆ X.erase x := by
      intro z hz
      have hzN := Finset.mem_inter.mp hz
      exact Finset.mem_erase.mpr
        ⟨D.ne_of_adj ((D.mem_neighborFinset x z).mp hzN.1).symm, hzN.2⟩
    have heraseCard : (X.erase x).card = X.card - 1 := Finset.card_erase_of_mem hx
    exact Finset.eq_of_subset_of_card_le hsub (by omega)
  intro x hx y hy hxy
  have hyErase : y ∈ X.erase x := Finset.mem_erase.mpr ⟨hxy.symm, hy⟩
  have hyInter : y ∈ D.neighborFinset x ∩ X := by
    rw [hinter x hx]
    exact hyErase
  exact (D.mem_neighborFinset x y).mp (Finset.mem_inter.mp hyInter).1

#print axioms shore_pairwise_adj_of_degree_pred_and_two_attachments

end Erdos85
