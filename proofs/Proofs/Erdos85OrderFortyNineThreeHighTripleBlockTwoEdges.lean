import Proofs.Erdos85OrderFortyNineThreeHighTripleSecondaryCapacity
import Proofs.Erdos85SquareOrderTwoHighTerminal

/-! Actual degree incidences force two internal edges in every special block. -/
namespace Erdos85
open SimpleGraph
noncomputable section

private theorem internal_incidence_twice_edges
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (B : Finset V) :
    (∑ x ∈ B, (G.neighborFinset x ∩ B).card) =
      2 * (G.induce (↑B : Set V)).edgeFinset.card := by
  classical
  have hs : (∑ x ∈ B, (G.neighborFinset x ∩ B).card) =
      ∑ x : (↑B : Set V), (G.induce (↑B : Set V)).degree x := by
    simp only [degree_induce_finset_eq_card_inter]
    exact Finset.sum_subtype B (fun _ => Iff.rfl) _
  rw [hs, SimpleGraph.sum_degrees_eq_twice_card_edges]

noncomputable def threeHighTripleBlockCrossMass
    (G : SimpleGraph (Fin 49)) [DecidableRel G.Adj] (z s : Fin 49) : ℕ := by
  classical
  exact ∑ t ∈ (threeHighTripleSpecialSet G z).erase s,
    ∑ x ∈ G.neighborFinset t ∩ threeHighTripleEmptySet G,
      (G.neighborFinset x ∩ (G.neighborFinset s ∩ threeHighTripleEmptySet G)).card

theorem threeHigh_triple_special_incidence_decomposition
    (G : SimpleGraph (Fin 49)) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 (Fin 49) G)
    (hmin : ∀ x : Fin 49, 7 ≤ G.degree x)
    (hHigh : (orderFortyNineHighVertices G).card = 3)
    (hone : orderFortyNineHighIncidenceCount G 3 = 1)
    (z : Fin 49) (hz : (orderFortyNineHighSupport G z).card = 3)
    {u : Fin 49} (hu : u ∈ threeHighTripleEmptySet G) (huz : G.Adj u z)
    {s : Fin 49} (hs : s ∈ threeHighTripleSpecialSet G z) :
    let B := G.neighborFinset s ∩ threeHighTripleEmptySet G
    let R := threeHighTripleEmptySet G \ insert u (threeHighTripleSpecialUnion G z)
    20 = 2 * (G.induce (↑B : Set (Fin 49))).edgeFinset.card +
      threeHighTripleBlockCrossMass G z s +
      ∑ x ∈ R, (G.neighborFinset x ∩ B).card := by
  classical
  let E := threeHighTripleEmptySet G
  let S := threeHighTripleSpecialSet G z
  let block := fun t => G.neighborFinset t ∩ E
  let U := threeHighTripleSpecialUnion G z
  let R := E \ insert u U
  let B := block s
  change 20 = 2 * (G.induce (↑B : Set (Fin 49))).edgeFinset.card +
    (∑ t ∈ S.erase s, ∑ x ∈ block t, (G.neighborFinset x ∩ B).card) +
    ∑ x ∈ R, (G.neighborFinset x ∩ B).card
  have hs1 : (orderFortyNineHighSupport G s).card = 1 := (Finset.mem_filter.mp hs).2
  have hsz : G.Adj s z := ((G.mem_neighborFinset _ _).mp (Finset.mem_filter.mp hs).1).symm
  have hBc : B.card = 5 := threeHigh_triple_special_empty_count G hfree hmin hHigh hone z hz hs1 hsz
  have hSc : S.card = 3 := threeHigh_triple_special_singleton_count G hfree hmin hHigh z hz
  have hp := threeHigh_triple_secondary_partition G hfree hmin hHigh hone z hz hu huz
  have hBU : B ⊆ U := by
    intro x hx
    exact Finset.mem_biUnion.mpr ⟨s, hs, hx⟩
  have hUE : U ⊆ E := by
    intro x hx
    obtain ⟨t, ht, hxt⟩ := Finset.mem_biUnion.mp hx
    exact (Finset.mem_inter.mp hxt).2
  have hd4 (x : Fin 49) (hx : x ∈ B) : (G.neighborFinset x ∩ E).card = 4 := by
    have hxE := (Finset.mem_inter.mp hx).2
    have hx0 := (Finset.mem_filter.mp hxE).2
    have hx7 : G.degree x = 7 := by
      rcases orderFortyNine_degree_eq_seven_or_eight G hfree hmin (Fintype.card_fin 49) x with h | h
      · exact h
      · exact ((Finset.mem_sdiff.mp (Finset.mem_filter.mp hxE).1).2
          (by simp [orderFortyNineHighVertices, h])).elim
    have hxz : ¬ G.Adj x z := by
      intro h
      exact threeHigh_triple_root_empty_outside_special_union G hfree hmin hHigh hone z hz hxE h (hBU hx)
    have hh := threeHigh_triple_empty_neighbor_degree G hfree hmin hHigh hone z hz hx7
    simpa only [E, threeHighTripleEmptySet, hx0, Nat.add_zero, if_neg hxz, mul_zero] using hh
  have hmass : (∑ x ∈ B, (G.neighborFinset x ∩ E).card) = 20 := by
    calc
      _ = ∑ _x ∈ B, 4 := Finset.sum_congr rfl (fun x hx => hd4 x hx)
      _ = 20 := by simp [hBc]
  have hpart : E = insert u (U ∪ R) := by
    ext x
    simp only [R, Finset.mem_insert, Finset.mem_union, Finset.mem_sdiff]
    constructor
    · intro hx
      by_cases hxu : x = u
      · exact Or.inl hxu
      · by_cases hxU : x ∈ U
        · exact Or.inr (Or.inl hxU)
        · exact Or.inr (Or.inr ⟨hx, by simp [hxu, hxU]⟩)
    · rintro (rfl | hxU | hxR)
      · exact hu
      · exact hUE hxU
      · exact hxR.1
  have huUR : u ∉ U ∪ R := by
    intro hm
    rcases Finset.mem_union.mp hm with hm | hm
    · exact hp.2.1 hm
    · exact (Finset.mem_sdiff.mp hm).2 (Finset.mem_insert_self _ _)
  have hUR : Disjoint U R := by
    apply Finset.disjoint_left.mpr
    intro x hx hy
    exact (Finset.mem_sdiff.mp hy).2 (Finset.mem_insert_of_mem hx)
  have huB0 : (G.neighborFinset u ∩ B).card = 0 := by
    apply Finset.card_eq_zero.mpr
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro x hx
    exact threeHigh_triple_root_empty_no_special_union_edge G hfree hmin hHigh hone z hz hu huz
      (hBU (Finset.mem_inter.mp hx).2) ((G.mem_neighborFinset _ _).mp (Finset.mem_inter.mp hx).1)
  have hsplit : (∑ x ∈ B, (G.neighborFinset x ∩ E).card) =
      (∑ x ∈ U, (G.neighborFinset x ∩ B).card) +
      ∑ x ∈ R, (G.neighborFinset x ∩ B).card := by
    rw [sum_card_neighbor_inter_comm G B E]
    conv_lhs => rw [hpart, Finset.sum_insert huUR, Finset.sum_union hUR, huB0, Nat.zero_add]
  have hblocks : (↑S : Set (Fin 49)).Pairwise (fun t v => Disjoint (block t) (block v)) := by
    intro t ht v hv htv
    exact threeHigh_triple_special_empty_blocks_disjoint G hfree hmin hHigh z hz htv
      (((G.mem_neighborFinset _ _).mp (Finset.mem_filter.mp ht).1).symm)
      (((G.mem_neighborFinset _ _).mp (Finset.mem_filter.mp hv).1).symm)
  have hUnion : (∑ x ∈ U, (G.neighborFinset x ∩ B).card) =
      ∑ t ∈ S, ∑ x ∈ block t, (G.neighborFinset x ∩ B).card := by
    exact Finset.sum_biUnion hblocks
  have hself := Finset.sum_erase_add S (fun t => ∑ x ∈ block t, (G.neighborFinset x ∩ B).card) hs
  have hhand : (∑ x ∈ block s, (G.neighborFinset x ∩ B).card) =
      2 * (G.induce (↑B : Set (Fin 49))).edgeFinset.card := internal_incidence_twice_edges G B
  rw [hUnion] at hsplit
  rw [hhand] at hself
  omega

private theorem special_cross_mass_le_ten
    (G : SimpleGraph (Fin 49)) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 (Fin 49) G)
    (hmin : ∀ x : Fin 49, 7 ≤ G.degree x)
    (hHigh : (orderFortyNineHighVertices G).card = 3)
    (hone : orderFortyNineHighIncidenceCount G 3 = 1)
    (z : Fin 49) (hz : (orderFortyNineHighSupport G z).card = 3)
    {s : Fin 49} (hs : s ∈ threeHighTripleSpecialSet G z) :
    threeHighTripleBlockCrossMass G z s ≤ 10 := by
  classical
  let E := threeHighTripleEmptySet G
  let S := threeHighTripleSpecialSet G z
  let block := fun t => G.neighborFinset t ∩ E
  let B := block s
  have hs1 : (orderFortyNineHighSupport G s).card = 1 := (Finset.mem_filter.mp hs).2
  have hSc : S.card = 3 := threeHigh_triple_special_singleton_count G hfree hmin hHigh z hz
  have hother : (∑ t ∈ S.erase s, ∑ x ∈ block t, (G.neighborFinset x ∩ B).card) ≤ 10 := by
    calc
      _ ≤ ∑ _t ∈ S.erase s, 5 := Finset.sum_le_sum (by
        intro t ht
        have htS := Finset.mem_of_mem_erase ht
        exact threeHigh_triple_special_cross_incidence_le_five G hfree hmin hHigh hone z hz s t hs1
          (Finset.mem_filter.mp htS).2
          (((G.mem_neighborFinset _ _).mp (Finset.mem_filter.mp htS).1).symm))
      _ = 10 := by rw [Finset.sum_const, Finset.card_erase_of_mem hs, hSc]; decide
  exact hother

theorem threeHigh_triple_special_internal_edges_eq_two
    (G : SimpleGraph (Fin 49)) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 (Fin 49) G)
    (hmin : ∀ x : Fin 49, 7 ≤ G.degree x)
    (hHigh : (orderFortyNineHighVertices G).card = 3)
    (hone : orderFortyNineHighIncidenceCount G 3 = 1)
    (z : Fin 49) (hz : (orderFortyNineHighSupport G z).card = 3)
    {u : Fin 49} (hu : u ∈ threeHighTripleEmptySet G) (huz : G.Adj u z)
    {s : Fin 49} (hs : s ∈ threeHighTripleSpecialSet G z) :
    let B := G.neighborFinset s ∩ threeHighTripleEmptySet G
    (G.induce (↑B : Set (Fin 49))).edgeFinset.card = 2 := by
  classical
  let B := G.neighborFinset s ∩ threeHighTripleEmptySet G
  let R := threeHighTripleEmptySet G \ insert u (threeHighTripleSpecialUnion G z)
  change (G.induce (↑B : Set (Fin 49))).edgeFinset.card = 2
  have heq := threeHigh_triple_special_incidence_decomposition G hfree hmin hHigh hone z hz hu huz hs
  have hcross := special_cross_mass_le_ten G hfree hmin hHigh hone z hz hs
  have hR : (∑ x ∈ R, (G.neighborFinset x ∩ B).card) ≤ 7 := by
    rw [← sum_card_neighbor_inter_comm G B R]
    exact threeHigh_triple_special_secondary_incidence_le_seven G hfree hmin hHigh hone z hz hu huz hs
  have hs1 := (Finset.mem_filter.mp hs).2
  have hsz := ((G.mem_neighborFinset _ _).mp (Finset.mem_filter.mp hs).1).symm
  have hle : (G.induce (↑B : Set (Fin 49))).edgeFinset.card ≤ 2 :=
    threeHigh_triple_special_internal_edges_le_two G hfree hmin hHigh hone z hz hs1 hsz
  simp only [B, R] at hR hle ⊢
  omega

theorem threeHigh_triple_special_cross_mass_bounds
    (G : SimpleGraph (Fin 49)) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 (Fin 49) G)
    (hmin : ∀ x : Fin 49, 7 ≤ G.degree x)
    (hHigh : (orderFortyNineHighVertices G).card = 3)
    (hone : orderFortyNineHighIncidenceCount G 3 = 1)
    (z : Fin 49) (hz : (orderFortyNineHighSupport G z).card = 3)
    {u : Fin 49} (hu : u ∈ threeHighTripleEmptySet G) (huz : G.Adj u z)
    {s : Fin 49} (hs : s ∈ threeHighTripleSpecialSet G z) :
    9 ≤ threeHighTripleBlockCrossMass G z s ∧ threeHighTripleBlockCrossMass G z s ≤ 10 := by
  classical
  let B := G.neighborFinset s ∩ threeHighTripleEmptySet G
  let R := threeHighTripleEmptySet G \ insert u (threeHighTripleSpecialUnion G z)
  have heq := threeHigh_triple_special_incidence_decomposition G hfree hmin hHigh hone z hz hu huz hs
  have hai := threeHigh_triple_special_internal_edges_eq_two G hfree hmin hHigh hone z hz hu huz hs
  have hR : (∑ x ∈ R, (G.neighborFinset x ∩ B).card) ≤ 7 := by
    rw [← sum_card_neighbor_inter_comm G B R]
    exact threeHigh_triple_special_secondary_incidence_le_seven G hfree hmin hHigh hone z hz hu huz hs
  have hc := special_cross_mass_le_ten G hfree hmin hHigh hone z hz hs
  simp only [B, R] at hR
  omega

end
end Erdos85
#print axioms Erdos85.threeHigh_triple_special_incidence_decomposition
#print axioms Erdos85.threeHigh_triple_special_internal_edges_eq_two
#print axioms Erdos85.threeHigh_triple_special_cross_mass_bounds
