import Proofs.Erdos85DegreeExcessStratification
import Proofs.Erdos85LocalTriangleParity

/-! A seven-vertex C4-free graph of maximum degree three has at most nine edges. -/
namespace Erdos85
open SimpleGraph Finset
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- A cubic root cannot have three cubic neighbors at order seven. -/
theorem sevenVertex_not_cubic_root_with_cubic_neighbors
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G) (hcard : Fintype.card V = 7)
    (x : V) (hx : G.degree x = 3)
    (hneighbors : ∀ y, G.Adj x y → G.degree y = 3) : False := by
  classical
  have hconf : (commonNeighborConflict G).degree x = 6 := by
    rw [degree_commonNeighborConflict_eq_sum_neighbor_degree_sub_one G hfree x]
    have heach : ∀ y : G.neighborSet x, G.degree y.1 - 1 = 2 := by
      intro y
      rw [hneighbors y.1 y.2]
    simp_rw [heach]
    have hN : Fintype.card {z : V // G.Adj x z} = 3 := by
      change Fintype.card (G.neighborSet x) = 3
      rw [G.card_neighborSet_eq_degree, hx]
    simp [hN]
  have hzero : (secondOrderDefectGraph G).degree x = 0 := by
    have heq : (secondOrderDefectGraph G).degree x = ((commonNeighborConflict G)ᶜ).degree x := by
      rw [← (secondOrderDefectGraph G).card_neighborFinset_eq_degree,
        ← ((commonNeighborConflict G)ᶜ).card_neighborFinset_eq_degree]
      apply congrArg Finset.card
      ext y
      simp only [SimpleGraph.mem_neighborFinset]
      rw [commonNeighborConflict_compl_eq_secondOrderDefectGraph G hfree]
    rw [heq, SimpleGraph.degree_compl, hcard, hconf]
  have hpositive := triangleFreeNeighbors_nonempty_of_odd_degree G hfree
    (x := x) (by rw [hx]; decide)
  have hle : (triangleFreeNeighbors G x).card ≤ (secondOrderDefectGraph G).degree x := by
    rw [← (secondOrderDefectGraph G).card_neighborFinset_eq_degree,
      secondOrderDefectGraph_neighborFinset]
    exact Finset.card_le_card Finset.subset_union_right
  have hp := Finset.card_pos.mpr hpositive
  omega

/-- Maximum degree three and ten edges force one degree-two vertex and
six degree-three vertices. -/
theorem sevenVertex_subcubic_ten_edges_degree_profile
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hcard : Fintype.card V = 7) (hmax : ∀ x, G.degree x ≤ 3)
    (hedges : G.edgeFinset.card = 10) :
    ∃ v, G.degree v = 2 ∧ ∀ x, x ≠ v → G.degree x = 3 := by
  classical
  let f := fun x => 3 - G.degree x
  have hsdeg := G.sum_degrees_eq_twice_card_edges
  rw [hedges] at hsdeg
  have hs : ∑ x : V, f x = 1 := by
    have heach : ∀ x, f x + G.degree x = 3 := by
      intro x
      have := hmax x
      dsimp [f]
      omega
    have hsum : (∑ x : V, f x) + ∑ x : V, G.degree x = 21 := by
      rw [← Finset.sum_add_distrib]
      simp_rw [heach]
      simp [hcard]
    omega
  obtain ⟨v, _, hv⟩ := Finset.sum_pos_iff.mp (show 0 < ∑ x : V, f x by omega)
  have hvle : f v ≤ 1 := by
    have hh := Finset.single_le_sum (f := f) (fun x _ => Nat.zero_le (f x)) (Finset.mem_univ v)
    omega
  have hvone : f v = 1 := by omega
  refine ⟨v, ?_, ?_⟩
  · have := hmax v
    dsimp [f] at hvone
    omega
  · intro x hx
    have hsum := Finset.sum_erase_add (s := Finset.univ) f (Finset.mem_univ v)
    have hzero : ∑ y ∈ Finset.univ.erase v, f y = 0 := by omega
    have hle := Finset.single_le_sum (f := f) (fun y _ => Nat.zero_le (f y))
      (show x ∈ Finset.univ.erase v by simp [hx])
    have hh := hmax x
    rw [hzero] at hle
    change 3 - G.degree x ≤ 0 at hle
    omega

/-- A C4-free seven-vertex graph with maximum degree three has at most nine edges. -/
theorem sevenVertex_subcubic_card_edges_le_nine
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G) (hcard : Fintype.card V = 7)
    (hmax : ∀ x, G.degree x ≤ 3) : G.edgeFinset.card ≤ 9 := by
  classical
  have hsum : (∑ x : V, G.degree x) ≤ 21 := by
    calc
      _ ≤ ∑ _x : V, 3 := Finset.sum_le_sum (fun x _ => hmax x)
      _ = 21 := by simp [hcard]
  have hhand := G.sum_degrees_eq_twice_card_edges
  by_contra hn
  have he : G.edgeFinset.card = 10 := by omega
  obtain ⟨v, hv, hothers⟩ := sevenVertex_subcubic_ten_edges_degree_profile G hcard hmax he
  have hsmall : (insert v (G.neighborFinset v)).card < (Finset.univ : Finset V).card := by
    have hh := Finset.card_insert_le v (G.neighborFinset v)
    rw [G.card_neighborFinset_eq_degree, hv] at hh
    simpa only [Finset.card_univ, hcard] using (show (insert v (G.neighborFinset v)).card < 7 by omega)
  obtain ⟨x, _, hx⟩ := Finset.exists_mem_notMem_of_card_lt_card hsmall
  have hxne : x ≠ v := by intro heq; exact hx (by simp [heq])
  have hxnot : ¬ G.Adj v x := by
    intro ha
    exact hx (Finset.mem_insert_of_mem ((G.mem_neighborFinset v x).mpr ha))
  apply sevenVertex_not_cubic_root_with_cubic_neighbors G hfree hcard x (hothers x hxne)
  intro y hxy
  apply hothers y
  intro heq
  subst y
  exact hxnot hxy.symm
end Erdos85
