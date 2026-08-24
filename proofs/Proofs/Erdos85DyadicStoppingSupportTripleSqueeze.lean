import Proofs.Erdos85DyadicStoppingSupportCombinedCherrySqueeze

/-!
# Higher-order stopping-support service squeeze

C4-freeness makes the map from a serviced target subset of any fixed size
at least two to its center injective.  Thus the usual cherry budget extends
to every higher subset size.  The triple specialization supplies a genuinely
new constraint when the stopping service minimum is at least three.
-/

open Finset SimpleGraph

namespace Erdos85

noncomputable section

/-- A C4-free graph has at most one center for every `r`-subset of `B`, for
every `r ≥ 2`. -/
theorem sum_choose_card_neighbor_inter_le_choose_card_of_two_le
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G) (B : Finset V) {r : ℕ} (hr : 2 ≤ r) :
    (∑ x : V, ((G.neighborFinset x ∩ B).card).choose r) ≤
      B.card.choose r := by
  classical
  let P : Finset (Σ _x : V, Finset V) :=
    Finset.univ.sigma fun x ↦ (G.neighborFinset x ∩ B).powersetCard r
  let Q : Finset (Finset V) := B.powersetCard r
  have hcardP : P.card =
      ∑ x : V, ((G.neighborFinset x ∩ B).card).choose r := by
    dsimp only [P]
    rw [Finset.card_sigma]
    apply Finset.sum_congr rfl
    intro x _
    simp
  have hcardQ : Q.card = B.card.choose r := by simp [Q]
  rw [← hcardP, ← hcardQ]
  apply Finset.card_le_card_of_injOn
    (fun p : (Σ _x : V, Finset V) ↦ p.2)
  · rintro ⟨x, T⟩ hp
    change T ∈ Q
    change ⟨x, T⟩ ∈ Finset.univ.sigma (fun x ↦
      (G.neighborFinset x ∩ B).powersetCard r) at hp
    have hp' := (Finset.mem_sigma.mp hp).2
    rw [Finset.mem_powersetCard] at hp'
    change T ∈ B.powersetCard r
    rw [Finset.mem_powersetCard]
    exact ⟨hp'.1.trans Finset.inter_subset_right, hp'.2⟩
  · rintro ⟨x, T⟩ hp ⟨y, U⟩ hq hTU
    change T = U at hTU
    subst U
    have hxy : x = y := by
      by_contra hne
      change ⟨x, T⟩ ∈ Finset.univ.sigma (fun x ↦
        (G.neighborFinset x ∩ B).powersetCard r) at hp
      change ⟨y, T⟩ ∈ Finset.univ.sigma (fun x ↦
        (G.neighborFinset x ∩ B).powersetCard r) at hq
      have hp' : T ⊆ G.neighborFinset x ∩ B ∧ T.card = r := by
        simpa only [Finset.mem_powersetCard] using (Finset.mem_sigma.mp hp).2
      have hq' : T ⊆ G.neighborFinset y ∩ B ∧ T.card = r := by
        simpa only [Finset.mem_powersetCard] using (Finset.mem_sigma.mp hq).2
      have hsub : T ⊆ G.neighborFinset x ∩ G.neighborFinset y := by
        intro z hz
        exact Finset.mem_inter.mpr
          ⟨(Finset.mem_inter.mp (hp'.1 hz)).1,
            (Finset.mem_inter.mp (hq'.1 hz)).1⟩
      have hle := Finset.card_le_card hsub
      have hone := common_le_one_of_not_containsC4 hfree x y hne
      omega
    subst y
    rfl

/-- Two disjoint center populations with service minima `L,M` consume the
single global `r`-subset budget of `B`. -/
theorem c4Free_disjoint_subset_service_choose_le
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G)
    (S T B : Finset V) (L M r : ℕ) (hr : 2 ≤ r)
    (hdisj : Disjoint S T)
    (hserviceS : ∀ p ∈ S, L ≤ (G.neighborFinset p ∩ B).card)
    (hserviceT : ∀ p ∈ T, M ≤ (G.neighborFinset p ∩ B).card) :
    S.card * L.choose r + T.card * M.choose r ≤ B.card.choose r := by
  have hS : S.card * L.choose r ≤
      ∑ p ∈ S, ((G.neighborFinset p ∩ B).card).choose r := by
    calc
      S.card * L.choose r = ∑ _p ∈ S, L.choose r := by simp
      _ ≤ ∑ p ∈ S, ((G.neighborFinset p ∩ B).card).choose r := by
        apply Finset.sum_le_sum
        intro p hp
        exact Nat.choose_le_choose r (hserviceS p hp)
  have hT : T.card * M.choose r ≤
      ∑ p ∈ T, ((G.neighborFinset p ∩ B).card).choose r := by
    calc
      T.card * M.choose r = ∑ _p ∈ T, M.choose r := by simp
      _ ≤ ∑ p ∈ T, ((G.neighborFinset p ∩ B).card).choose r := by
        apply Finset.sum_le_sum
        intro p hp
        exact Nat.choose_le_choose r (hserviceT p hp)
  calc
    S.card * L.choose r + T.card * M.choose r ≤
        (∑ p ∈ S, ((G.neighborFinset p ∩ B).card).choose r) +
          ∑ p ∈ T, ((G.neighborFinset p ∩ B).card).choose r :=
      Nat.add_le_add hS hT
    _ = ∑ p ∈ S ∪ T, ((G.neighborFinset p ∩ B).card).choose r := by
      rw [sum_union hdisj]
    _ ≤ ∑ p : V, ((G.neighborFinset p ∩ B).card).choose r :=
      Finset.sum_le_univ_sum_of_nonneg fun _ => Nat.zero_le _
    _ ≤ B.card.choose r :=
      sum_choose_card_neighbor_inter_le_choose_card_of_two_le G hfree B hr

/-- The triple-budget specialization for the two shores of a dyadic
stopping support. -/
theorem c4Free_dyadicStoppingSupport_twoShore_triple_squeeze
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G) {q : ℕ}
    (hreg : ∀ v, G.degree v = q)
    (S : Finset V) (j : ℕ)
    (hdiv : ∀ v, 2 ^ j ∣ (G.neighborFinset v ∩ S).card)
    (hqdiv : 2 ^ (j + 1) ∣ q) :
    S.card * (dyadicStoppingServiceMinimum q S.card j).choose 3 +
        (Sᶜ : Finset V).card *
          (dyadicStoppingServiceMinimum q (Sᶜ : Finset V).card j).choose 3 ≤
      (dyadicOccupancySupport G S j).card.choose 3 := by
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
  apply c4Free_disjoint_subset_service_choose_le
    G hfree S (Sᶜ : Finset V) (dyadicOccupancySupport G S j)
    (dyadicStoppingServiceMinimum q S.card j)
    (dyadicStoppingServiceMinimum q (Sᶜ : Finset V).card j) 3 (by omega)
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

#print axioms Erdos85.sum_choose_card_neighbor_inter_le_choose_card_of_two_le
#print axioms Erdos85.c4Free_dyadicStoppingSupport_twoShore_triple_squeeze
