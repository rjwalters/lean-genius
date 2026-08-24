import Proofs.Erdos85DyadicStoppingSupportCherrySqueeze

/-!
# Combined two-shore cherry squeeze

The shore and its complement partition all possible cherry centers.  Their
service lower bounds therefore add before the single global C4 pair budget
is applied.  This is stronger than applying that budget independently to
the two shores.
-/

open Finset SimpleGraph

namespace Erdos85

noncomputable section

/-- Two disjoint center sets with separate uniform service minima share one
global C4 cherry budget. -/
theorem c4Free_disjoint_subset_service_combined_cherry_le
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G)
    (S T B : Finset V) (L M : ℕ)
    (hdisj : Disjoint S T)
    (hserviceS : ∀ p ∈ S, L ≤ (G.neighborFinset p ∩ B).card)
    (hserviceT : ∀ p ∈ T, M ≤ (G.neighborFinset p ∩ B).card) :
    S.card * L.choose 2 + T.card * M.choose 2 ≤ B.card.choose 2 := by
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
    _ ≤ B.card.choose 2 :=
      sum_choose_card_neighbor_inter_le_choose_card_of_not_containsC4
        G hfree B

/-- **Combined two-shore stopping-support squeeze.**  Both complementary
shore service costs consume the same C4 pair budget. -/
theorem c4Free_dyadicStoppingSupport_twoShore_combined_cherry_squeeze
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G) {q : ℕ}
    (hreg : ∀ v, G.degree v = q)
    (S : Finset V) (j : ℕ)
    (hdiv : ∀ v, 2 ^ j ∣ (G.neighborFinset v ∩ S).card)
    (hqdiv : 2 ^ (j + 1) ∣ q) :
    S.card * (dyadicStoppingServiceMinimum q S.card j).choose 2 +
        (Sᶜ : Finset V).card *
          (dyadicStoppingServiceMinimum q (Sᶜ : Finset V).card j).choose 2 ≤
      (dyadicOccupancySupport G S j).card.choose 2 := by
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
  apply c4Free_disjoint_subset_service_combined_cherry_le
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

#print axioms Erdos85.c4Free_disjoint_subset_service_combined_cherry_le
#print axioms Erdos85.c4Free_dyadicStoppingSupport_twoShore_combined_cherry_squeeze
