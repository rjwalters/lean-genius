import Proofs.Erdos85PlateauSlideNormalForm

/-!
# Packing the terminal edges of slide certificates

The penultimate vertex in a deleted-edge slide certificate determines the
donor neighbor uniquely.  Otherwise it and the donor center would have two
distinct common neighbors, producing a four-cycle.
-/

open SimpleGraph

namespace Erdos85

/-- Donor neighbors to which the edge `xz` can genuinely be slid toward
`y`: the terminal is neither `y` nor already adjacent to `y`. -/
def eligibleDonorNeighbors
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (x y : V) : Finset V :=
  (G.neighborFinset x).filter fun z ↦ z ≠ y ∧ ¬ G.Adj y z

/-- For a fixed donor center `x`, surviving terminal edges `b-z` and `b-z'`
from the corresponding deleted-edge graphs force `z=z'`. -/
theorem deletedDonor_terminal_unique
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G) {x b z z' : V}
    (hxz : G.Adj x z) (hxz' : G.Adj x z')
    (hbz : (G.deleteEdges {s(x,z)}).Adj b z)
    (hbz' : (G.deleteEdges {s(x,z')}).Adj b z') :
    z = z' := by
  have hbzG : G.Adj b z := (SimpleGraph.deleteEdges_adj.mp hbz).1
  have hbzG' : G.Adj b z' := (SimpleGraph.deleteEdges_adj.mp hbz').1
  have hxb : x ≠ b := by
    intro h
    subst b
    exact (SimpleGraph.deleteEdges_adj.mp hbz).2 (by simp)
  have hzmem : z ∈ G.neighborFinset x ∩ G.neighborFinset b := by
    simp only [Finset.mem_inter, SimpleGraph.mem_neighborFinset]
    exact ⟨hxz, hbzG⟩
  have hzmem' : z' ∈ G.neighborFinset x ∩ G.neighborFinset b := by
    simp only [Finset.mem_inter, SimpleGraph.mem_neighborFinset]
    exact ⟨hxz', hbzG'⟩
  exact Finset.card_le_one.mp
    (common_le_one_of_not_containsC4 hfree x b hxb) z hzmem z' hzmem'

/-- The terminal endpoint of a deleted-edge three-walk certificate is
injective as a function of its penultimate vertex, for fixed donor center. -/
theorem deletedThreeWalk_penultimate_injective
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G) {x y z z' a a' b : V}
    (hxz : G.Adj x z) (hxz' : G.Adj x z')
    (hwalk : (G.deleteEdges {s(x,z)}).Adj y a ∧
      (G.deleteEdges {s(x,z)}).Adj a b ∧
      (G.deleteEdges {s(x,z)}).Adj b z)
    (hwalk' : (G.deleteEdges {s(x,z')}).Adj y a' ∧
      (G.deleteEdges {s(x,z')}).Adj a' b ∧
      (G.deleteEdges {s(x,z')}).Adj b z') :
    z = z' :=
  deletedDonor_terminal_unique G hfree hxz hxz' hwalk.2.2 hwalk'.2.2

/-- **Slide-certificate packing.**  If every eligible donor edge has a
deleted-edge three-walk certificate from `y`, then its penultimate vertices
inject the eligible donor neighbors into the common neighborhood of `x` and
`y` in the common-neighbor conflict graph. -/
theorem card_eligibleDonorNeighbors_le_conflict_common
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G) (x y : V)
    (hsat : ∀ z, z ≠ y → G.Adj x z → ¬ G.Adj y z →
      HasThreeEdgeWalk (G.deleteEdges {s(x,z)}) y z) :
    (eligibleDonorNeighbors G x y).card ≤
      ((commonNeighborConflict G).neighborFinset x ∩
        (commonNeighborConflict G).neighborFinset y).card := by
  classical
  have hw : ∀ z ∈ eligibleDonorNeighbors G x y,
      ∃ a b,
        (G.deleteEdges {s(x,z)}).Adj y a ∧
        (G.deleteEdges {s(x,z)}).Adj a b ∧
        (G.deleteEdges {s(x,z)}).Adj b z := by
    intro z hz
    rw [eligibleDonorNeighbors, Finset.mem_filter] at hz
    exact hsat z hz.2.1 ((G.mem_neighborFinset x z).mp hz.1) hz.2.2
  choose a b hya hab hbz using hw
  let f : V → V := fun z ↦
    if hz : z ∈ eligibleDonorNeighbors G x y then b z hz else x
  apply Finset.card_le_card_of_injOn f
  · intro z hz
    change f z ∈
      (commonNeighborConflict G).neighborFinset x ∩
        (commonNeighborConflict G).neighborFinset y
    have hzfin : z ∈ eligibleDonorNeighbors G x y := hz
    have hzdata := hzfin
    simp only [eligibleDonorNeighbors, Finset.mem_filter] at hzdata
    have hxz : G.Adj x z := (G.mem_neighborFinset x z).mp hzdata.1
    have hyz : ¬ G.Adj y z := hzdata.2.2
    have hyaG : G.Adj y (a z hzfin) :=
      G.deleteEdges_le _ (hya z hzfin)
    have habG : G.Adj (a z hzfin) (b z hzfin) :=
      G.deleteEdges_le _ (hab z hzfin)
    have hbzG : G.Adj (b z hzfin) z :=
      G.deleteEdges_le _ (hbz z hzfin)
    have hxb : x ≠ b z hzfin := by
      intro h
      have hterminal := hbz z hzfin
      rw [← h] at hterminal
      exact (SimpleGraph.deleteEdges_adj.mp hterminal).2 (by simp)
    have hyb : y ≠ b z hzfin := by
      intro h
      apply hyz
      simpa [h] using hbzG
    have hxbConflict : (commonNeighborConflict G).Adj x (b z hzfin) :=
      ⟨hxb, ⟨z, Finset.mem_inter.mpr
        ⟨(G.mem_neighborFinset x z).mpr hxz,
          (G.mem_neighborFinset (b z hzfin) z).mpr hbzG⟩⟩⟩
    have hybConflict : (commonNeighborConflict G).Adj y (b z hzfin) :=
      ⟨hyb, ⟨a z hzfin, Finset.mem_inter.mpr
        ⟨(G.mem_neighborFinset y (a z hzfin)).mpr hyaG,
          (G.mem_neighborFinset (b z hzfin) (a z hzfin)).mpr habG.symm⟩⟩⟩
    simpa only [f, dif_pos hzfin] using
      (show b z hzfin ∈
          (commonNeighborConflict G).neighborFinset x ∩
            (commonNeighborConflict G).neighborFinset y from
        Finset.mem_inter.mpr
          ⟨((commonNeighborConflict G).mem_neighborFinset x _).mpr hxbConflict,
            ((commonNeighborConflict G).mem_neighborFinset y _).mpr hybConflict⟩)
  · intro z hz z' hz' heq
    have hzfin : z ∈ eligibleDonorNeighbors G x y := hz
    have hz'fin : z' ∈ eligibleDonorNeighbors G x y := hz'
    have hzdata := hzfin
    have hz'data := hz'fin
    simp only [eligibleDonorNeighbors, Finset.mem_filter] at hzdata hz'data
    have heqb : b z hzfin = b z' hz'fin := by
      simpa only [f, dif_pos hzfin, dif_pos hz'fin] using heq
    apply deletedDonor_terminal_unique G hfree
      ((G.mem_neighborFinset x z).mp hzdata.1)
      ((G.mem_neighborFinset x z').mp hz'data.1)
      (hbz z hzfin)
    simpa [heqb] using hbz z' hz'fin

/-- C4-freeness discards at most two donor neighbors from eligibility: `y`
itself, and at most one common neighbor of the distinct vertices `x,y`. -/
theorem degree_le_card_eligibleDonorNeighbors_add_two
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G) {x y : V} (hxy : x ≠ y) :
    G.degree x ≤ (eligibleDonorNeighbors G x y).card + 2 := by
  classical
  let bad := (G.neighborFinset x).filter fun z ↦ z = y ∨ G.Adj y z
  have hpartition : G.neighborFinset x =
      eligibleDonorNeighbors G x y ∪ bad := by
    ext z
    simp only [eligibleDonorNeighbors, bad, Finset.mem_union,
      Finset.mem_filter]
    constructor
    · intro hz
      by_cases hzy : z = y
      · exact Or.inr ⟨hz, Or.inl hzy⟩
      by_cases hyz : G.Adj y z
      · exact Or.inr ⟨hz, Or.inr hyz⟩
      · exact Or.inl ⟨hz, hzy, hyz⟩
    · rintro (⟨hz, _, _⟩ | ⟨hz, _⟩) <;> exact hz
  have hdisj : Disjoint (eligibleDonorNeighbors G x y) bad := by
    rw [Finset.disjoint_left]
    intro z hz hzb
    simp only [eligibleDonorNeighbors, Finset.mem_filter] at hz
    simp only [bad, Finset.mem_filter] at hzb
    exact hzb.2.elim hz.2.1 hz.2.2
  have hbadSub : bad ⊆ insert y
      (G.neighborFinset x ∩ G.neighborFinset y) := by
    intro z hz
    simp only [bad, Finset.mem_filter] at hz
    rcases hz.2 with rfl | hyz
    · simp
    · simp only [Finset.mem_insert, Finset.mem_inter]
      exact Or.inr ⟨hz.1, (G.mem_neighborFinset y z).mpr hyz⟩
  have hcommon : (G.neighborFinset x ∩ G.neighborFinset y).card ≤ 1 :=
    common_le_one_of_not_containsC4 hfree x y hxy
  have hbad : bad.card ≤ 2 := by
    calc
      bad.card ≤ (insert y
          (G.neighborFinset x ∩ G.neighborFinset y)).card :=
        Finset.card_le_card hbadSub
      _ ≤ (G.neighborFinset x ∩ G.neighborFinset y).card + 1 :=
        Finset.card_insert_le y _
      _ ≤ 2 := by omega
  rw [← SimpleGraph.card_neighborFinset_eq_degree, hpartition,
    Finset.card_union_of_disjoint hdisj]
  omega

/-- The numerical slide-packing inequality obtained by combining saturation
with the C4-free eligibility bound. -/
theorem degree_le_conflict_common_add_two_of_slideSaturated
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G) {x y : V} (hxy : x ≠ y)
    (hsat : ∀ z, z ≠ y → G.Adj x z → ¬ G.Adj y z →
      HasThreeEdgeWalk (G.deleteEdges {s(x,z)}) y z) :
    G.degree x ≤
      ((commonNeighborConflict G).neighborFinset x ∩
        (commonNeighborConflict G).neighborFinset y).card + 2 := by
  exact (degree_le_card_eligibleDonorNeighbors_add_two G hfree hxy).trans
    (Nat.add_le_add_right
      (card_eligibleDonorNeighbors_le_conflict_common G hfree x y hsat) 2)

end Erdos85
