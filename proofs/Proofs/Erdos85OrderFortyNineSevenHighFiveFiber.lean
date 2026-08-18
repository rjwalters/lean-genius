import Proofs.Erdos85OrderFortyNineSevenHighFourFiber

/-!
# Fiber census for the five-block seven-high triple systems

The classification is bootstrapped from the four-block theorem: normalize
any four blocks first, then finite-check the possible fifth block.  This keeps
the trusted finite search small and scales to the final two strata.
-/

namespace Erdos85

open SimpleGraph

noncomputable section

def sevenHighT5TripleSet (index : Nat) : Finset (Finset (Fin 7)) :=
  match index with
  | 0 => {{0, 1, 2}, {0, 3, 4}, {0, 5, 6}, {1, 3, 5}, {1, 4, 6}}
  | _ => {{0, 1, 2}, {0, 3, 4}, {0, 5, 6}, {1, 3, 5}, {2, 4, 6}}

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem extend_four_linear_triples_canonical
    (oldIndex : Nat) (hOldIndex : oldIndex < 3)
    (E : SevenHighTriple)
    (hnew : E.1 ∉ sevenHighT4TripleSet oldIndex)
    (hlinear : (sevenHighT4TripleSet oldIndex).filter
      (fun T => (E.1 ∩ T).card ≤ 1) = sevenHighT4TripleSet oldIndex) :
    ∃ index : Nat, index < 2 ∧ ∃ σ : Equiv.Perm (Fin 7),
      insert (E.1.map σ.toEmbedding)
        ((sevenHighT4TripleSet oldIndex).image
          (fun T => T.map σ.toEmbedding)) = sevenHighT5TripleSet index := by
  interval_cases oldIndex <;> native_decide +revert

theorem five_linear_triple_system_canonical
    (S : Finset (Finset (Fin 7)))
    (hcard : S.card = 5)
    (htriple : ∀ T ∈ S, T.card = 3)
    (hlinear : ∀ A ∈ S, ∀ B ∈ S, A ≠ B → (A ∩ B).card ≤ 1) :
    ∃ index : Nat, index < 2 ∧ ∃ σ : Equiv.Perm (Fin 7),
      S.image (fun T => T.map σ.toEmbedding) = sevenHighT5TripleSet index := by
  obtain ⟨E, R, hER, rfl, hRcard⟩ :=
    Finset.card_eq_succ.mp (show S.card = 4 + 1 by omega)
  obtain ⟨A, B, C, D, hAB, hAC, hAD, hBC, hBD, hCD, hR⟩ :=
    Finset.card_eq_four.mp hRcard
  have hAE : A ≠ E := by
    intro h; subst A; exact hER (by simp [hR])
  have hBE : B ≠ E := by
    intro h; subst B; exact hER (by simp [hR])
  have hCE : C ≠ E := by
    intro h; subst C; exact hER (by simp [hR])
  have hDE : D ≠ E := by
    intro h; subst D; exact hER (by simp [hR])
  let A3 : SevenHighTriple := ⟨A, htriple A (by simp [hR])⟩
  let B3 : SevenHighTriple := ⟨B, htriple B (by simp [hR])⟩
  let C3 : SevenHighTriple := ⟨C, htriple C (by simp [hR])⟩
  let D3 : SevenHighTriple := ⟨D, htriple D (by simp [hR])⟩
  have sub_ne {P Q : SevenHighTriple} (h : P.1 ≠ Q.1) : P ≠ Q := by
    intro heq; exact h (congrArg Subtype.val heq)
  obtain ⟨oldIndex, hOldIndex, σ0, hfour⟩ :=
    four_linear_triples_canonical A3 B3 C3 D3
      (sub_ne hAB) (sub_ne hAC) (sub_ne hAD)
      (sub_ne hBC) (sub_ne hBD) (sub_ne hCD)
      (hlinear A (by simp [hR]) B (by simp [hR]) hAB)
      (hlinear A (by simp [hR]) C (by simp [hR]) hAC)
      (hlinear A (by simp [hR]) D (by simp [hR]) hAD)
      (hlinear B (by simp [hR]) C (by simp [hR]) hBC)
      (hlinear B (by simp [hR]) D (by simp [hR]) hBD)
      (hlinear C (by simp [hR]) D (by simp [hR]) hCD)
  let E0 : SevenHighTriple :=
    ⟨E.map σ0.toEmbedding, by simp [htriple E (by simp)]⟩
  have hnew : E0.1 ∉ sevenHighT4TripleSet oldIndex := by
    intro hmem
    rw [← hfour] at hmem
    simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
    rcases hmem with h | h | h | h <;>
      first
      | exact hAE (Finset.map_injective σ0.toEmbedding h.symm)
      | exact hBE (Finset.map_injective σ0.toEmbedding h.symm)
      | exact hCE (Finset.map_injective σ0.toEmbedding h.symm)
      | exact hDE (Finset.map_injective σ0.toEmbedding h.symm)
  have hlinearE0 : (sevenHighT4TripleSet oldIndex).filter
      (fun T => (E0.1 ∩ T).card ≤ 1) = sevenHighT4TripleSet oldIndex := by
    apply Finset.filter_eq_self.mpr
    intro T hT
    rw [← hfour] at hT
    simp only [Finset.mem_insert, Finset.mem_singleton] at hT
    rcases hT with rfl | rfl | rfl | rfl
    · simpa [E0, ← Finset.map_inter, Finset.card_map] using
        hlinear E (by simp) A (by simp [hR]) (Ne.symm hAE)
    · simpa [E0, ← Finset.map_inter, Finset.card_map] using
        hlinear E (by simp) B (by simp [hR]) (Ne.symm hBE)
    · simpa [E0, ← Finset.map_inter, Finset.card_map] using
        hlinear E (by simp) C (by simp [hR]) (Ne.symm hCE)
    · simpa [E0, ← Finset.map_inter, Finset.card_map] using
        hlinear E (by simp) D (by simp [hR]) (Ne.symm hDE)
  obtain ⟨index, hindex, τ, hfive⟩ :=
    extend_four_linear_triples_canonical oldIndex hOldIndex E0 hnew hlinearE0
  refine ⟨index, hindex, σ0.trans τ, ?_⟩
  rw [Finset.image_insert]
  have hRimage : R.image (fun T => T.map σ0.toEmbedding) =
      sevenHighT4TripleSet oldIndex := by
    simpa [hR] using hfour
  have hRcomp : R.image (fun T => T.map (σ0.trans τ).toEmbedding) =
      (R.image (fun T => T.map σ0.toEmbedding)).image
        (fun T => T.map τ.toEmbedding) := by
    rw [Finset.image_image]
    congr 1
    funext T
    simp [Finset.map_map]
  rw [hRcomp, hRimage]
  simpa [E0, Finset.map_map] using hfive

theorem sevenHigh_t5_exists_normalized_labeling
    (G : SimpleGraph (Fin 49)) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 (Fin 49) G)
    (hmin : ∀ x : Fin 49, 7 ≤ G.degree x)
    (hHigh : (orderFortyNineHighVertices G).card = 7)
    (hfive : orderFortyNineHighIncidenceCount G 3 = 5) :
    ∃ index : Nat, index < 2 ∧
      ∃ e : {v // v ∈ orderFortyNineHighVertices G} ≃ Fin 7,
      ∃ s : Finset (Fin 49),
        s.image (sevenHighLabeledSupport G e) = sevenHighT5TripleSet index ∧
        (∀ q ∈ s, (sevenHighLabeledSupport G e q).card = 3) ∧
        ∀ q : Fin 49, (sevenHighLabeledSupport G e q).card = 3 → q ∈ s := by
  let s : Finset (Fin 49) := (orderFortyNineLowVertices G).filter fun q =>
    (orderFortyNineHighSupport G q).card = 3
  have hscard : s.card = 5 := hfive
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
  have hScard : S.card = 5 := by
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
    five_linear_triple_system_canonical S hScard hStriple hSlinear
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

theorem sevenHighT5TripleSet_member_card
    (index : Nat) (hindex : index < 2)
    {T : Finset (Fin 7)} (hT : T ∈ sevenHighT5TripleSet index) :
    T.card = 3 := by
  interval_cases index <;> native_decide +revert

theorem sevenHigh_t5_local_triple_card
    (G : SimpleGraph (Fin 49)) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 (Fin 49) G)
    (index : Nat) (hindex : index < 2)
    (e : {v // v ∈ orderFortyNineHighVertices G} ≃ Fin 7)
    (s : Finset (Fin 49))
    (hmap : s.image (sevenHighLabeledSupport G e) =
      sevenHighT5TripleSet index)
    (hmember : ∀ q ∈ s, (sevenHighLabeledSupport G e q).card = 3)
    (huniq : ∀ q : Fin 49,
      (sevenHighLabeledSupport G e q).card = 3 → q ∈ s)
    (w : Fin 7) :
    ((G.neighborFinset (e.symm w).1).filter fun q =>
      (orderFortyNineHighSupport G q).card = 3).card =
      ((sevenHighT5TripleSet index).filter fun T => w ∈ T).card := by
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

theorem sevenHigh_t5_singleton_fiber_card
    (G : SimpleGraph (Fin 49)) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 (Fin 49) G)
    (hmin : ∀ x : Fin 49, 7 ≤ G.degree x)
    (hHigh : (orderFortyNineHighVertices G).card = 7)
    (index : Nat) (hindex : index < 2)
    (e : {v // v ∈ orderFortyNineHighVertices G} ≃ Fin 7)
    (s : Finset (Fin 49))
    (hmap : s.image (sevenHighLabeledSupport G e) =
      sevenHighT5TripleSet index)
    (hmember : ∀ q ∈ s, (sevenHighLabeledSupport G e q).card = 3)
    (huniq : ∀ q : Fin 49,
      (sevenHighLabeledSupport G e q).card = 3 → q ∈ s)
    (w : Fin 7) :
    Fintype.card {q : Fin 49 // sevenHighLabeledSupport G e q = {w}} =
      ((sevenHighT5TripleSet index).filter fun T => w ∈ T).card + 2 := by
  rw [sevenHigh_singleton_fiber_card_eq_local G e w]
  have hp := orderFortyNine_highNeighborhood_profile_of_seven_high
    G hfree hmin (Fintype.card_fin 49) hHigh
      (Finset.mem_filter.mp (e.symm w).2).2
  dsimp only at hp
  rw [sevenHigh_t5_local_triple_card G hfree index hindex e s
    hmap hmember huniq w] at hp
  omega

theorem sevenHigh_t5_exists_triple_superset_iff
    (G : SimpleGraph (Fin 49)) [DecidableRel G.Adj]
    (index : Nat)
    (e : {v // v ∈ orderFortyNineHighVertices G} ≃ Fin 7)
    (s : Finset (Fin 49))
    (hmap : s.image (sevenHighLabeledSupport G e) =
      sevenHighT5TripleSet index)
    (hmember : ∀ q ∈ s, (sevenHighLabeledSupport G e q).card = 3)
    (huniq : ∀ q : Fin 49,
      (sevenHighLabeledSupport G e q).card = 3 → q ∈ s)
    (P : Finset (Fin 7)) :
    (∃ q : Fin 49,
      (sevenHighLabeledSupport G e q).card = 3 ∧
      P ⊆ sevenHighLabeledSupport G e q) ↔
      ∃ T ∈ sevenHighT5TripleSet index, P ⊆ T := by
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

theorem sevenHigh_t5_triple_fiber_card
    (G : SimpleGraph (Fin 49)) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 (Fin 49) G)
    (index : Nat)
    (e : {v // v ∈ orderFortyNineHighVertices G} ≃ Fin 7)
    (s : Finset (Fin 49))
    (hmap : s.image (sevenHighLabeledSupport G e) =
      sevenHighT5TripleSet index)
    (hmember : ∀ q ∈ s, (sevenHighLabeledSupport G e q).card = 3)
    (huniq : ∀ q : Fin 49,
      (sevenHighLabeledSupport G e q).card = 3 → q ∈ s)
    (S : Finset (Fin 7)) (hS3 : S.card = 3) :
    Fintype.card {q : Fin 49 // sevenHighLabeledSupport G e q = S} =
      if S ∈ sevenHighT5TripleSet index then 1 else 0 := by
  by_cases hS : S ∈ sevenHighT5TripleSet index
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

def sevenHighT5KeyMultiplicity
    (index : Nat) (key : Option (Fin 7) × Finset (Fin 7)) : Nat :=
  match key.1 with
  | some _ => if key.2 = ∅ then 1 else 0
  | none =>
      if key.2.card = 0 then 2
      else if key.2.card = 1 then
        ((sevenHighT5TripleSet index).filter fun T => key.2 ⊆ T).card + 2
      else if key.2.card = 2 then
        if ∃ T ∈ sevenHighT5TripleSet index, key.2 ⊆ T then 0 else 1
      else if key.2 ∈ sevenHighT5TripleSet index then 1 else 0

theorem sevenHigh_t5_mask_key_fiber_card
    (index : Nat) (hindex : index < 2)
    (key : Option (Fin 7) × Finset (Fin 7)) :
    Fintype.card {i : Fin 49 //
      sevenHighMaskAlignedKey
        (OrderFortyNineSevenHighCensus.representativeMasks 5 index) i = key} =
      sevenHighT5KeyMultiplicity index key := by
  interval_cases index <;> native_decide +revert

theorem sevenHigh_t5_alignedLow_other_fiber_card_eq_zero
    (G : SimpleGraph (Fin 49)) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 (Fin 49) G)
    (hmin : ∀ x : Fin 49, 7 ≤ G.degree x)
    (index : Nat)
    (e : {v // v ∈ orderFortyNineHighVertices G} ≃ Fin 7)
    (s : Finset (Fin 49))
    (hmap : s.image (sevenHighLabeledSupport G e) =
      sevenHighT5TripleSet index)
    (huniq : ∀ q : Fin 49,
      (sevenHighLabeledSupport G e q).card = 3 → q ∈ s)
    (S : Finset (Fin 7))
    (h0 : S.card ≠ 0) (h1 : S.card ≠ 1) (h2 : S.card ≠ 2)
    (hcanonical : S ∉ sevenHighT5TripleSet index) :
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

theorem sevenHigh_t5_graph_key_fiber_card
    (G : SimpleGraph (Fin 49)) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 (Fin 49) G)
    (hmin : ∀ x : Fin 49, 7 ≤ G.degree x)
    (hHigh : (orderFortyNineHighVertices G).card = 7)
    (hfive : orderFortyNineHighIncidenceCount G 3 = 5)
    (index : Nat) (hindex : index < 2)
    (e : {v // v ∈ orderFortyNineHighVertices G} ≃ Fin 7)
    (s : Finset (Fin 49))
    (hmap : s.image (sevenHighLabeledSupport G e) =
      sevenHighT5TripleSet index)
    (hmember : ∀ q ∈ s, (sevenHighLabeledSupport G e q).card = 3)
    (huniq : ∀ q : Fin 49,
      (sevenHighLabeledSupport G e q).card = 3 → q ∈ s)
    (key : Option (Fin 7) × Finset (Fin 7)) :
    Fintype.card {q : Fin 49 // sevenHighGraphAlignedKey G e q = key} =
      sevenHighT5KeyMultiplicity index key := by
  rcases key with ⟨label, S⟩
  cases label with
  | some w =>
      by_cases hS0 : S = ∅
      · subst S
        simpa [sevenHighT5KeyMultiplicity] using
          sevenHigh_alignedHigh_fiber_card_eq_one G hfree hmin e w
      · have hSne : S.Nonempty := Finset.nonempty_iff_ne_empty.mpr hS0
        simpa [sevenHighT5KeyMultiplicity, hS0] using
          sevenHigh_alignedHigh_nonemptySupport_fiber_card_eq_zero
            G hfree hmin e w S hSne
  | none =>
      by_cases h0 : S.card = 0
      · have hS0 : S = ∅ := Finset.card_eq_zero.mp h0
        subst S
        have hp := orderFortyNine_highIncidence_profile_of_seven_high
          G hfree hmin (Fintype.card_fin 49) hHigh
        dsimp only at hp
        have hn0 : orderFortyNineHighIncidenceCount G 0 = 2 := by omega
        simpa [sevenHighT5KeyMultiplicity, hn0] using
          sevenHigh_aligned_emptyLow_fiber_card G e
      · by_cases h1 : S.card = 1
        · obtain ⟨w, rfl⟩ := Finset.card_eq_one.mp h1
          rw [sevenHigh_nonempty_alignedLowFiber_card G hfree hmin e {w}
            (by simp)]
          rw [sevenHigh_t5_singleton_fiber_card G hfree hmin hHigh
            index hindex e s hmap hmember huniq w]
          simp only [sevenHighT5KeyMultiplicity, Finset.card_singleton,
            ↓reduceIte]
          congr 2
          ext T
          simp
        · by_cases h2 : S.card = 2
          · obtain ⟨a, b, hab, rfl⟩ := Finset.card_eq_two.mp h2
            rw [sevenHigh_nonempty_alignedLowFiber_card G hfree hmin e {a, b}
              (by simp)]
            rw [sevenHigh_pair_fiber_card G hfree hmin e a b hab]
            have hiff := sevenHigh_t5_exists_triple_superset_iff
              G index e s hmap hmember huniq {a, b}
            by_cases hex : ∃ q : Fin 49,
                (sevenHighLabeledSupport G e q).card = 3 ∧
                ({a, b} : Finset (Fin 7)) ⊆ sevenHighLabeledSupport G e q
            · have hrep := hiff.mp hex
              simp [sevenHighT5KeyMultiplicity, hab, hex, hrep]
            · have hrep := (not_congr hiff).mp hex
              simp [sevenHighT5KeyMultiplicity, hab, hex, hrep]
          · by_cases hcanonical : S ∈ sevenHighT5TripleSet index
            · have hS3 := sevenHighT5TripleSet_member_card
                index hindex hcanonical
              rw [sevenHigh_nonempty_alignedLowFiber_card G hfree hmin e S
                (Finset.card_pos.mp (by omega))]
              rw [sevenHigh_t5_triple_fiber_card G hfree index e s
                hmap hmember huniq S hS3]
              simp [sevenHighT5KeyMultiplicity, h0, h1, h2, hcanonical]
            · simpa [sevenHighT5KeyMultiplicity, h0, h1, h2, hcanonical] using
                sevenHigh_t5_alignedLow_other_fiber_card_eq_zero
                  G hfree hmin index e s hmap huniq
                    S h0 h1 h2 hcanonical

theorem sevenHighCanonicalFiberCover_five :
    SevenHighCanonicalFiberCover 5 := by
  intro G _ _ _ hfree hmin hHigh hfive
  obtain ⟨index, hindex, e, s, hmap, hmember, huniq⟩ :=
    sevenHigh_t5_exists_normalized_labeling G hfree hmin hHigh hfive
  refine ⟨index, by interval_cases index <;> native_decide,
    e, by interval_cases index <;> native_decide, ?_⟩
  intro key
  rw [sevenHigh_t5_graph_key_fiber_card G hfree hmin hHigh hfive
      index hindex e s hmap hmember huniq key,
    sevenHigh_t5_mask_key_fiber_card index hindex key]

theorem sevenHighCanonicalGraphCover_five :
    SevenHighCanonicalGraphCover 5 :=
  sevenHighCanonicalGraphCover_of_labelingCover
    (sevenHighCanonicalLabelingCover_of_fiberCover
      sevenHighCanonicalFiberCover_five)

end

end Erdos85
