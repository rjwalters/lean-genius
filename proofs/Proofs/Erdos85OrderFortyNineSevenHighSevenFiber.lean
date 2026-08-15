import Proofs.Erdos85OrderFortyNineSevenHighSixFiber

/-! # Fiber census for the seven-block Fano triple system -/

namespace Erdos85

open SimpleGraph

noncomputable section

def sevenHighT7TripleSet (_index : Nat) : Finset (Finset (Fin 7)) :=
  {{0, 1, 2}, {0, 3, 4}, {0, 5, 6}, {1, 3, 5}, {1, 4, 6},
    {2, 3, 6}, {2, 4, 5}}

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem extend_six_linear_triples_canonical
    (oldIndex : Nat) (hOldIndex : oldIndex < 1)
    (E : SevenHighTriple)
    (hnew : E.1 ∉ sevenHighT6TripleSet oldIndex)
    (hlinear : (sevenHighT6TripleSet oldIndex).filter
      (fun T => (E.1 ∩ T).card ≤ 1) = sevenHighT6TripleSet oldIndex) :
    ∃ σ : Equiv.Perm (Fin 7),
      insert (E.1.map σ.toEmbedding)
        ((sevenHighT6TripleSet oldIndex).image
          (fun T => T.map σ.toEmbedding)) = sevenHighT7TripleSet 0 := by
  interval_cases oldIndex <;> native_decide +revert

theorem seven_linear_triple_system_canonical
    (S : Finset (Finset (Fin 7)))
    (hcard : S.card = 7)
    (htriple : ∀ T ∈ S, T.card = 3)
    (hlinear : ∀ A ∈ S, ∀ B ∈ S, A ≠ B → (A ∩ B).card ≤ 1) :
    ∃ index : Nat, index < 1 ∧ ∃ σ : Equiv.Perm (Fin 7),
      S.image (fun T => T.map σ.toEmbedding) = sevenHighT7TripleSet index := by
  obtain ⟨E, R, hER, rfl, hRcard⟩ :=
    Finset.card_eq_succ.mp (show S.card = 6 + 1 by omega)
  have hRtriple : ∀ T ∈ R, T.card = 3 := by
    intro T hT; exact htriple T (by simp [hT])
  have hRlinear : ∀ A ∈ R, ∀ B ∈ R, A ≠ B → (A ∩ B).card ≤ 1 := by
    intro A hA B hB hAB
    exact hlinear A (by simp [hA]) B (by simp [hB]) hAB
  obtain ⟨oldIndex, hOldIndex, σ0, hsix⟩ :=
    six_linear_triple_system_canonical R hRcard hRtriple hRlinear
  let E0 : SevenHighTriple :=
    ⟨E.map σ0.toEmbedding, by simp [htriple E (by simp)]⟩
  have hnew : E0.1 ∉ sevenHighT6TripleSet oldIndex := by
    intro hmem
    rw [← hsix] at hmem
    obtain ⟨T, hTR, hTE⟩ := Finset.mem_image.mp hmem
    have hTE' : T = E := Finset.map_injective σ0.toEmbedding hTE
    subst T
    exact hER hTR
  have hlinearE0 : (sevenHighT6TripleSet oldIndex).filter
      (fun T => (E0.1 ∩ T).card ≤ 1) = sevenHighT6TripleSet oldIndex := by
    apply Finset.filter_eq_self.mpr
    intro T hT
    rw [← hsix] at hT
    obtain ⟨U, hUR, rfl⟩ := Finset.mem_image.mp hT
    rw [show E0.1 = E.map σ0.toEmbedding by rfl,
      ← Finset.map_inter, Finset.card_map]
    exact hlinear E (by simp) U (by simp [hUR]) (by
      intro hEU; subst U; exact hER hUR)
  obtain ⟨τ, hseven⟩ :=
    extend_six_linear_triples_canonical oldIndex hOldIndex E0 hnew hlinearE0
  refine ⟨0, by omega, σ0.trans τ, ?_⟩
  rw [Finset.image_insert]
  have hRcomp : R.image (fun T => T.map (σ0.trans τ).toEmbedding) =
      (R.image (fun T => T.map σ0.toEmbedding)).image
        (fun T => T.map τ.toEmbedding) := by
    rw [Finset.image_image]
    congr 1
    funext T
    simp [Finset.map_map]
  rw [hRcomp, hsix]
  simpa [E0, Finset.map_map] using hseven

theorem sevenHigh_t7_exists_normalized_labeling
    (G : SimpleGraph (Fin 49)) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 (Fin 49) G)
    (hmin : ∀ x : Fin 49, 7 ≤ G.degree x)
    (hHigh : (orderFortyNineHighVertices G).card = 7)
    (hseven : orderFortyNineHighIncidenceCount G 3 = 7) :
    ∃ index : Nat, index < 1 ∧
      ∃ e : {v // v ∈ orderFortyNineHighVertices G} ≃ Fin 7,
      ∃ s : Finset (Fin 49),
        s.image (sevenHighLabeledSupport G e) = sevenHighT7TripleSet index ∧
        (∀ q ∈ s, (sevenHighLabeledSupport G e q).card = 3) ∧
        ∀ q : Fin 49, (sevenHighLabeledSupport G e q).card = 3 → q ∈ s := by
  let s : Finset (Fin 49) := (orderFortyNineLowVertices G).filter fun q =>
    (orderFortyNineHighSupport G q).card = 3
  have hscard : s.card = 7 := hseven
  let e0 : {v // v ∈ orderFortyNineHighVertices G} ≃ Fin 7 :=
    Fintype.equivFinOfCardEq (by simpa using hHigh)
  let f : Fin 49 → Finset (Fin 7) := sevenHighLabeledSupport G e0
  have hmember0 : ∀ q ∈ s, (f q).card = 3 := by
    intro q hq
    rw [sevenHighLabeledSupport_card]
    exact (Finset.mem_filter.mp hq).2
  have hinj : Set.InjOn f ↑s := by
    intro a ha b hb hab
    exact sevenHighLabeledSupport_injective_of_two_le G hfree e0
      (by change 2 ≤ (f a).card; rw [hmember0 a ha]; omega) hab
  let S := s.image f
  have hScard : S.card = 7 := by
    rw [show S = s.image f by rfl, Finset.card_image_iff.mpr hinj, hscard]
  have hStriple : ∀ T ∈ S, T.card = 3 := by
    intro T hT
    obtain ⟨q, hqs, rfl⟩ := Finset.mem_image.mp hT
    exact hmember0 q hqs
  have hSlinear : ∀ A ∈ S, ∀ B ∈ S, A ≠ B → (A ∩ B).card ≤ 1 := by
    intro A hA B hB hAB
    obtain ⟨a, has, rfl⟩ := Finset.mem_image.mp hA
    obtain ⟨b, hbs, rfl⟩ := Finset.mem_image.mp hB
    have hab : a ≠ b := by intro h; subst b; exact hAB rfl
    rw [sevenHighLabeledSupport_inter_card]
    exact orderFortyNine_card_inter_highSupport_le_one G hfree hab
  obtain ⟨index, hindex, σ, hcanon⟩ :=
    seven_linear_triple_system_canonical S hScard hStriple hSlinear
  let e := e0.trans σ
  have heSupport (q : Fin 49) : sevenHighLabeledSupport G e q =
      (sevenHighLabeledSupport G e0 q).map σ.toEmbedding := by
    simp [sevenHighLabeledSupport, e, Finset.map_map]
  refine ⟨index, hindex, e, s, ?_, ?_, ?_⟩
  · rw [show s.image (sevenHighLabeledSupport G e) =
        S.image (fun T => T.map σ.toEmbedding) by
      rw [Finset.image_image]
      congr 1
      funext q
      exact heSupport q]
    exact hcanon
  · intro q hqs
    rw [heSupport, Finset.card_map]
    exact hmember0 q hqs
  · intro q hq3
    apply Finset.mem_filter.mpr
    have hqOrig3 : (orderFortyNineHighSupport G q).card = 3 := by
      rw [← sevenHighLabeledSupport_card G e q]
      exact hq3
    refine ⟨?_, hqOrig3⟩
    apply Finset.mem_sdiff.mpr
    refine ⟨Finset.mem_univ q, ?_⟩
    intro hqHigh
    have hq0 := orderFortyNine_highNeighborCount_eq_zero_of_high
      G hfree hmin (Fintype.card_fin 49) hqHigh
    change (orderFortyNineHighSupport G q).card = 0 at hq0
    omega

theorem sevenHighT7TripleSet_member_card
    (index : Nat) (hindex : index < 1)
    {T : Finset (Fin 7)} (hT : T ∈ sevenHighT7TripleSet index) :
    T.card = 3 := by
  interval_cases index <;> native_decide +revert

theorem sevenHigh_t7_local_triple_card
    (G : SimpleGraph (Fin 49)) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 (Fin 49) G)
    (index : Nat) (hindex : index < 1)
    (e : {v // v ∈ orderFortyNineHighVertices G} ≃ Fin 7)
    (s : Finset (Fin 49))
    (hmap : s.image (sevenHighLabeledSupport G e) =
      sevenHighT7TripleSet index)
    (hmember : ∀ q ∈ s, (sevenHighLabeledSupport G e q).card = 3)
    (huniq : ∀ q : Fin 49,
      (sevenHighLabeledSupport G e q).card = 3 → q ∈ s)
    (w : Fin 7) :
    ((G.neighborFinset (e.symm w).1).filter fun q =>
      (orderFortyNineHighSupport G q).card = 3).card =
      ((sevenHighT7TripleSet index).filter fun T => w ∈ T).card := by
  let f : Fin 49 → Finset (Fin 7) := sevenHighLabeledSupport G e
  have hinj : Set.InjOn f ↑s := by
    intro a ha b hb hab
    exact sevenHighLabeledSupport_injective_of_two_le G hfree e
      (by have := hmember a ha; omega) hab
  have hgraphSet : ((G.neighborFinset (e.symm w).1).filter fun q =>
      (orderFortyNineHighSupport G q).card = 3) =
      s.filter fun q => w ∈ f q := by
    ext q
    constructor
    · intro hq
      have hq3 : (f q).card = 3 := by
        rw [sevenHighLabeledSupport_card]
        exact (Finset.mem_filter.mp hq).2
      refine Finset.mem_filter.mpr ⟨huniq q hq3, ?_⟩
      apply (mem_sevenHighLabeledSupport_iff G e q w).mpr
      simpa [SimpleGraph.mem_neighborFinset, G.adj_comm] using
        (Finset.mem_filter.mp hq).1
    · intro hq
      refine Finset.mem_filter.mpr ⟨?_, ?_⟩
      · simpa [SimpleGraph.mem_neighborFinset, G.adj_comm] using
          (mem_sevenHighLabeledSupport_iff G e q w).mp
            (Finset.mem_filter.mp hq).2
      · rw [← sevenHighLabeledSupport_card G e q]
        exact hmember q (Finset.mem_filter.mp hq).1
  rw [hgraphSet, ← hmap, Finset.filter_image]
  symm
  exact Finset.card_image_iff.mpr (hinj.mono (Finset.filter_subset _ _))

theorem sevenHigh_t7_singleton_fiber_card
    (G : SimpleGraph (Fin 49)) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 (Fin 49) G)
    (hmin : ∀ x : Fin 49, 7 ≤ G.degree x)
    (hHigh : (orderFortyNineHighVertices G).card = 7)
    (index : Nat) (hindex : index < 1)
    (e : {v // v ∈ orderFortyNineHighVertices G} ≃ Fin 7)
    (s : Finset (Fin 49))
    (hmap : s.image (sevenHighLabeledSupport G e) =
      sevenHighT7TripleSet index)
    (hmember : ∀ q ∈ s, (sevenHighLabeledSupport G e q).card = 3)
    (huniq : ∀ q : Fin 49,
      (sevenHighLabeledSupport G e q).card = 3 → q ∈ s)
    (w : Fin 7) :
    Fintype.card {q : Fin 49 // sevenHighLabeledSupport G e q = {w}} =
      ((sevenHighT7TripleSet index).filter fun T => w ∈ T).card + 2 := by
  rw [sevenHigh_singleton_fiber_card_eq_local G e w]
  have hp := orderFortyNine_highNeighborhood_profile_of_seven_high
    G hfree hmin (Fintype.card_fin 49) hHigh
      (Finset.mem_filter.mp (e.symm w).2).2
  dsimp only at hp
  rw [sevenHigh_t7_local_triple_card G hfree index hindex e s
    hmap hmember huniq w] at hp
  omega

theorem sevenHigh_t7_exists_triple_superset_iff
    (G : SimpleGraph (Fin 49)) [DecidableRel G.Adj]
    (index : Nat)
    (e : {v // v ∈ orderFortyNineHighVertices G} ≃ Fin 7)
    (s : Finset (Fin 49))
    (hmap : s.image (sevenHighLabeledSupport G e) =
      sevenHighT7TripleSet index)
    (hmember : ∀ q ∈ s, (sevenHighLabeledSupport G e q).card = 3)
    (huniq : ∀ q : Fin 49,
      (sevenHighLabeledSupport G e q).card = 3 → q ∈ s)
    (P : Finset (Fin 7)) :
    (∃ q : Fin 49,
      (sevenHighLabeledSupport G e q).card = 3 ∧
      P ⊆ sevenHighLabeledSupport G e q) ↔
      ∃ T ∈ sevenHighT7TripleSet index, P ⊆ T := by
  constructor
  · rintro ⟨q, hq3, hPq⟩
    refine ⟨sevenHighLabeledSupport G e q, ?_, hPq⟩
    rw [← hmap]
    exact Finset.mem_image.mpr ⟨q, huniq q hq3, rfl⟩
  · rintro ⟨T, hT, hPT⟩
    rw [← hmap] at hT
    obtain ⟨q, hqs, hqT⟩ := Finset.mem_image.mp hT
    refine ⟨q, hmember q hqs, ?_⟩
    simpa [hqT] using hPT

theorem sevenHigh_t7_triple_fiber_card
    (G : SimpleGraph (Fin 49)) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 (Fin 49) G)
    (index : Nat)
    (e : {v // v ∈ orderFortyNineHighVertices G} ≃ Fin 7)
    (s : Finset (Fin 49))
    (hmap : s.image (sevenHighLabeledSupport G e) =
      sevenHighT7TripleSet index)
    (hmember : ∀ q ∈ s, (sevenHighLabeledSupport G e q).card = 3)
    (huniq : ∀ q : Fin 49,
      (sevenHighLabeledSupport G e q).card = 3 → q ∈ s)
    (S : Finset (Fin 7)) (hS3 : S.card = 3) :
    Fintype.card {q : Fin 49 // sevenHighLabeledSupport G e q = S} =
      if S ∈ sevenHighT7TripleSet index then 1 else 0 := by
  by_cases hS : S ∈ sevenHighT7TripleSet index
  · rw [if_pos hS]
    rw [← hmap] at hS
    obtain ⟨q, hqs, hqS⟩ := Finset.mem_image.mp hS
    have hone := sevenHighLabeledSupport_fiber_card_eq_one
      G hfree e q (by have := hmember q hqs; omega)
    simpa [hqS] using hone
  · rw [if_neg hS, Fintype.card_subtype, Finset.card_eq_zero]
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro q hq
    have hqEq := (Finset.mem_filter.mp hq).2
    apply hS
    rw [← hmap]
    exact Finset.mem_image.mpr ⟨q, huniq q (by simpa [hqEq] using hS3), hqEq⟩

def sevenHighT7KeyMultiplicity
    (index : Nat) (key : Option (Fin 7) × Finset (Fin 7)) : Nat :=
  match key.1 with
  | some _ => if key.2 = ∅ then 1 else 0
  | none =>
      if key.2.card = 0 then 0
      else if key.2.card = 1 then
        ((sevenHighT7TripleSet index).filter fun T => key.2 ⊆ T).card + 2
      else if key.2.card = 2 then
        if ∃ T ∈ sevenHighT7TripleSet index, key.2 ⊆ T then 0 else 1
      else if key.2 ∈ sevenHighT7TripleSet index then 1 else 0

theorem sevenHigh_t7_mask_key_fiber_card
    (index : Nat) (hindex : index < 1)
    (key : Option (Fin 7) × Finset (Fin 7)) :
    Fintype.card {i : Fin 49 //
      sevenHighMaskAlignedKey
        (OrderFortyNineSevenHighCensus.representativeMasks 7 index) i = key} =
      sevenHighT7KeyMultiplicity index key := by
  interval_cases index <;> native_decide +revert

theorem sevenHigh_t7_alignedLow_other_fiber_card_eq_zero
    (G : SimpleGraph (Fin 49)) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 (Fin 49) G)
    (hmin : ∀ x : Fin 49, 7 ≤ G.degree x)
    (index : Nat)
    (e : {v // v ∈ orderFortyNineHighVertices G} ≃ Fin 7)
    (s : Finset (Fin 49))
    (hmap : s.image (sevenHighLabeledSupport G e) =
      sevenHighT7TripleSet index)
    (huniq : ∀ q : Fin 49,
      (sevenHighLabeledSupport G e q).card = 3 → q ∈ s)
    (S : Finset (Fin 7))
    (h0 : S.card ≠ 0) (h1 : S.card ≠ 1) (h2 : S.card ≠ 2)
    (hcanonical : S ∉ sevenHighT7TripleSet index) :
    Fintype.card {q : Fin 49 //
      sevenHighGraphAlignedKey G e q = (none, S)} = 0 := by
  rw [Fintype.card_subtype, Finset.card_eq_zero]
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro q hq
  have hkey := (Finset.mem_filter.mp hq).2
  have hfirst := congrArg Prod.fst hkey
  have hsupp : sevenHighLabeledSupport G e q = S := by
    simpa [sevenHighGraphAlignedKey] using congrArg Prod.snd hkey
  have hqNotHigh : q ∉ orderFortyNineHighVertices G := by
    intro hqHigh
    simp [sevenHighGraphAlignedKey, hqHigh] at hfirst
  have hq7 : G.degree q = 7 := by
    rcases orderFortyNine_degree_eq_seven_or_eight
      G hfree hmin (Fintype.card_fin 49) q with hq7 | hq8
    · exact hq7
    · exact False.elim (hqNotHigh
        (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hq8⟩))
  have hle : S.card ≤ 3 := by
    rw [← hsupp, sevenHighLabeledSupport_card]
    simpa [orderFortyNineHighSupport] using
      orderFortyNine_highNeighborCount_le_three
        G hfree hmin (Fintype.card_fin 49) hq7
  have hS3 : S.card = 3 := by omega
  apply hcanonical
  rw [← hmap]
  exact Finset.mem_image.mpr ⟨q, huniq q (by simpa [hsupp] using hS3), hsupp⟩

theorem sevenHigh_t7_graph_key_fiber_card
    (G : SimpleGraph (Fin 49)) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 (Fin 49) G)
    (hmin : ∀ x : Fin 49, 7 ≤ G.degree x)
    (hHigh : (orderFortyNineHighVertices G).card = 7)
    (hseven : orderFortyNineHighIncidenceCount G 3 = 7)
    (index : Nat) (hindex : index < 1)
    (e : {v // v ∈ orderFortyNineHighVertices G} ≃ Fin 7)
    (s : Finset (Fin 49))
    (hmap : s.image (sevenHighLabeledSupport G e) =
      sevenHighT7TripleSet index)
    (hmember : ∀ q ∈ s, (sevenHighLabeledSupport G e q).card = 3)
    (huniq : ∀ q : Fin 49,
      (sevenHighLabeledSupport G e q).card = 3 → q ∈ s)
    (key : Option (Fin 7) × Finset (Fin 7)) :
    Fintype.card {q : Fin 49 // sevenHighGraphAlignedKey G e q = key} =
      sevenHighT7KeyMultiplicity index key := by
  rcases key with ⟨label, S⟩
  cases label with
  | some w =>
      by_cases hS0 : S = ∅
      · subst S
        simpa [sevenHighT7KeyMultiplicity] using
          sevenHigh_alignedHigh_fiber_card_eq_one G hfree hmin e w
      · have hSne : S.Nonempty := Finset.nonempty_iff_ne_empty.mpr hS0
        simpa [sevenHighT7KeyMultiplicity, hS0] using
          sevenHigh_alignedHigh_nonemptySupport_fiber_card_eq_zero
            G hfree hmin e w S hSne
  | none =>
      by_cases h0 : S.card = 0
      · have hS0 : S = ∅ := Finset.card_eq_zero.mp h0
        subst S
        have hp := orderFortyNine_highIncidence_profile_of_seven_high
          G hfree hmin (Fintype.card_fin 49) hHigh
        dsimp only at hp
        have hn0 : orderFortyNineHighIncidenceCount G 0 = 0 := by omega
        simpa [sevenHighT7KeyMultiplicity, hn0] using
          sevenHigh_aligned_emptyLow_fiber_card G e
      · by_cases h1 : S.card = 1
        · obtain ⟨w, rfl⟩ := Finset.card_eq_one.mp h1
          rw [sevenHigh_nonempty_alignedLowFiber_card G hfree hmin e {w}
            (by simp)]
          rw [sevenHigh_t7_singleton_fiber_card G hfree hmin hHigh
            index hindex e s hmap hmember huniq w]
          simp only [sevenHighT7KeyMultiplicity, Finset.card_singleton,
            ↓reduceIte]
          congr 2
          ext T
          simp
        · by_cases h2 : S.card = 2
          · obtain ⟨a, b, hab, rfl⟩ := Finset.card_eq_two.mp h2
            rw [sevenHigh_nonempty_alignedLowFiber_card G hfree hmin e {a, b}
              (by simp)]
            rw [sevenHigh_pair_fiber_card G hfree hmin e a b hab]
            have hiff := sevenHigh_t7_exists_triple_superset_iff
              G index e s hmap hmember huniq {a, b}
            by_cases hex : ∃ q : Fin 49,
                (sevenHighLabeledSupport G e q).card = 3 ∧
                ({a, b} : Finset (Fin 7)) ⊆ sevenHighLabeledSupport G e q
            · have hrep := hiff.mp hex
              simp [sevenHighT7KeyMultiplicity, hab, hex, hrep]
            · have hrep := (not_congr hiff).mp hex
              simp [sevenHighT7KeyMultiplicity, hab, hex, hrep]
          · by_cases hcanonical : S ∈ sevenHighT7TripleSet index
            · have hS3 := sevenHighT7TripleSet_member_card
                index hindex hcanonical
              rw [sevenHigh_nonempty_alignedLowFiber_card G hfree hmin e S
                (Finset.card_pos.mp (by omega))]
              rw [sevenHigh_t7_triple_fiber_card G hfree index e s
                hmap hmember huniq S hS3]
              simp [sevenHighT7KeyMultiplicity, h0, h1, h2, hcanonical]
            · simpa [sevenHighT7KeyMultiplicity, h0, h1, h2, hcanonical] using
                sevenHigh_t7_alignedLow_other_fiber_card_eq_zero
                  G hfree hmin index e s hmap huniq
                    S h0 h1 h2 hcanonical

theorem sevenHighCanonicalFiberCover_seven :
    SevenHighCanonicalFiberCover 7 := by
  intro G _ _ _ hfree hmin hHigh hseven
  obtain ⟨index, hindex, e, s, hmap, hmember, huniq⟩ :=
    sevenHigh_t7_exists_normalized_labeling G hfree hmin hHigh hseven
  refine ⟨index, by interval_cases index <;> native_decide,
    e, by interval_cases index <;> native_decide, ?_⟩
  intro key
  rw [sevenHigh_t7_graph_key_fiber_card G hfree hmin hHigh hseven
      index hindex e s hmap hmember huniq key,
    sevenHigh_t7_mask_key_fiber_card index hindex key]

theorem sevenHighCanonicalGraphCover_seven :
    SevenHighCanonicalGraphCover 7 :=
  sevenHighCanonicalGraphCover_of_labelingCover
    (sevenHighCanonicalLabelingCover_of_fiberCover
      sevenHighCanonicalFiberCover_seven)

end

end Erdos85
