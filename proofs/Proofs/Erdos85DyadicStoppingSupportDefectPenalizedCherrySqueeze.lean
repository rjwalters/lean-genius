import Proofs.Erdos85DyadicStoppingSupportCombinedCherrySqueeze
import Proofs.Erdos85C4FreeSubsetForbiddenCherryBound
import Proofs.Erdos85BinarySquareDyadicSignedTerminal

/-!
# Defect-penalized dyadic cherry squeeze

A pair joined in the second-order defect graph has no common neighbor in the
original graph.  Such pairs inside the stopping support can therefore be
removed from its C4 cherry budget.  This couples the quantitative stopping
inequality to the actual location of the support in the defect geometry.
-/

open Finset SimpleGraph

namespace Erdos85

noncomputable section

/-- Canonical two-subsets of `B` which form second-order-defect edges. -/
def secondOrderDefectPairs
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (B : Finset V) : Finset (Finset V) :=
  (B.powersetCard 2).filter fun T =>
    ∀ u ∈ T, ∀ v ∈ T, u ≠ v → (secondOrderDefectGraph G).Adj u v

theorem secondOrderDefectPairs_subset_powersetCard
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (B : Finset V) :
    secondOrderDefectPairs G B ⊆ B.powersetCard 2 := by
  exact Finset.filter_subset _ _

/-- A canonical defect pair has no common ambient neighbor. -/
theorem secondOrderDefectPairs_forbidden_commonNeighbor
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) (B : Finset V) :
    ∀ T ∈ secondOrderDefectPairs G B, ∀ x : V,
      ¬ T ⊆ G.neighborFinset x := by
  intro T hT x hsub
  have hTdata := Finset.mem_filter.mp hT
  have hcard : T.card = 2 := (Finset.mem_powersetCard.mp hTdata.1).2
  obtain ⟨u, v, huv, rfl⟩ := Finset.card_eq_two.mp hcard
  have hu : u ∈ ({u, v} : Finset V) := by simp
  have hv : v ∈ ({u, v} : Finset V) := by simp
  have hD := hTdata.2 u hu v hv huv
  have hux : G.Adj u x :=
    ((G.mem_neighborFinset x u).mp (hsub hu)).symm
  have hvx : G.Adj v x :=
    ((G.mem_neighborFinset x v).mp (hsub hv)).symm
  exact (commonNeighbor_not_secondOrderDefect_adj
    G hfree huv hux hvx) hD

/-- Disjoint service populations consume the C4 pair budget after every
internal second-order-defect pair of `B` is removed. -/
theorem c4Free_disjoint_subset_service_defectPenalized_cherry_le
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G)
    (S T B : Finset V) (L M : ℕ)
    (hdisj : Disjoint S T)
    (hserviceS : ∀ p ∈ S, L ≤ (G.neighborFinset p ∩ B).card)
    (hserviceT : ∀ p ∈ T, M ≤ (G.neighborFinset p ∩ B).card) :
    S.card * L.choose 2 + T.card * M.choose 2 ≤
      B.card.choose 2 - (secondOrderDefectPairs G B).card := by
  have hS : S.card * L.choose 2 ≤
      ∑ p ∈ S, ((G.neighborFinset p ∩ B).card).choose 2 := by
    calc
      S.card * L.choose 2 = ∑ _p ∈ S, L.choose 2 := by simp
      _ ≤ ∑ p ∈ S, ((G.neighborFinset p ∩ B).card).choose 2 := by
        apply Finset.sum_le_sum
        intro p hp
        exact Nat.choose_le_choose 2 (hserviceS p hp)
  have hT : T.card * M.choose 2 ≤
      ∑ p ∈ T, ((G.neighborFinset p ∩ B).card).choose 2 := by
    calc
      T.card * M.choose 2 = ∑ _p ∈ T, M.choose 2 := by simp
      _ ≤ ∑ p ∈ T, ((G.neighborFinset p ∩ B).card).choose 2 := by
        apply Finset.sum_le_sum
        intro p hp
        exact Nat.choose_le_choose 2 (hserviceT p hp)
  calc
    S.card * L.choose 2 + T.card * M.choose 2 ≤
        (∑ p ∈ S, ((G.neighborFinset p ∩ B).card).choose 2) +
          ∑ p ∈ T, ((G.neighborFinset p ∩ B).card).choose 2 :=
      Nat.add_le_add hS hT
    _ = ∑ p ∈ S ∪ T, ((G.neighborFinset p ∩ B).card).choose 2 := by
      rw [sum_union hdisj]
    _ ≤ ∑ p : V, ((G.neighborFinset p ∩ B).card).choose 2 :=
      Finset.sum_le_univ_sum_of_nonneg fun _ => Nat.zero_le _
    _ ≤ B.card.choose 2 - (secondOrderDefectPairs G B).card :=
      sum_choose_card_neighbor_inter_le_choose_card_sub_forbidden
        G hfree B (secondOrderDefectPairs G B)
        (secondOrderDefectPairs_subset_powersetCard G B)
        (secondOrderDefectPairs_forbidden_commonNeighbor G hfree B)

/-- The combined stopping-support service cost is bounded by the pair budget
of `B` minus all defect pairs internal to `B`. -/
theorem c4Free_dyadicStoppingSupport_twoShore_defectPenalized_cherry_squeeze
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) {q : ℕ}
    (hreg : ∀ v, G.degree v = q)
    (S : Finset V) (j : ℕ)
    (hdiv : ∀ v, 2 ^ j ∣ (G.neighborFinset v ∩ S).card)
    (hqdiv : 2 ^ (j + 1) ∣ q) :
    S.card * (dyadicStoppingServiceMinimum q S.card j).choose 2 +
        (Sᶜ : Finset V).card *
          (dyadicStoppingServiceMinimum q (Sᶜ : Finset V).card j).choose 2 ≤
      (dyadicOccupancySupport G S j).card.choose 2 -
        (secondOrderDefectPairs G (dyadicOccupancySupport G S j)).card := by
  have hajq : 2 ^ j ∣ q := by
    obtain ⟨u, hu⟩ := hqdiv
    refine ⟨2 * u, ?_⟩
    rw [hu, pow_succ]
    ring
  have hdivc : ∀ v, 2 ^ j ∣
      (G.neighborFinset v ∩ (Sᶜ : Finset V)).card :=
    dvd_complement_occupancy G hreg S (by positivity) hajq hdiv
  have hsupport : dyadicOccupancySupport G (Sᶜ : Finset V) j =
      dyadicOccupancySupport G S j :=
    dyadicOccupancySupport_compl G hreg S j hdiv hqdiv
  apply c4Free_disjoint_subset_service_defectPenalized_cherry_le
    G hfree S (Sᶜ : Finset V) (dyadicOccupancySupport G S j)
    (dyadicStoppingServiceMinimum q S.card j)
    (dyadicStoppingServiceMinimum q (Sᶜ : Finset V).card j)
    (by
      rw [Finset.disjoint_left]
      intro x hxS hxSc
      exact (Finset.mem_compl.mp hxSc) hxS)
  · intro p hp
    exact c4Free_dyadicStoppingSupport_degree_ge_serviceMinimum
      G hfree hreg S j hdiv p hp
  · intro p hp
    rw [← hsupport]
    exact c4Free_dyadicStoppingSupport_degree_ge_serviceMinimum
      G hfree hreg (Sᶜ : Finset V) j hdivc p hp

end

end Erdos85

#print axioms Erdos85.secondOrderDefectPairs_forbidden_commonNeighbor
#print axioms Erdos85.c4Free_disjoint_subset_service_defectPenalized_cherry_le
#print axioms Erdos85.c4Free_dyadicStoppingSupport_twoShore_defectPenalized_cherry_squeeze
