import Proofs.Erdos85OrderFortyNineFiveHighTripleNormalization

/-!
# Canonical fiber covers for the five-high cells

This file packages the graph-side fiber census in a form shared by all three
canonical triple systems.
-/

namespace Erdos85

open SimpleGraph

noncomputable section

theorem fiveHigh_alignedHigh_fiber_card_eq_one
    (G : SimpleGraph (Fin 49)) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 (Fin 49) G)
    (hmin : ∀ x : Fin 49, 7 ≤ G.degree x)
    (e : {v // v ∈ orderFortyNineHighVertices G} ≃ Fin 5)
    (w : Fin 5) :
    Fintype.card {x : Fin 49 //
      fiveHighGraphAlignedKey G e x = (some w, ∅)} = 1 := by
  rw [Fintype.card_subtype]
  let v : Fin 49 := (e.symm w).1
  have hv : v ∈ orderFortyNineHighVertices G := (e.symm w).2
  have hset : (Finset.univ.filter fun x : Fin 49 =>
      fiveHighGraphAlignedKey G e x = (some w, ∅)) = {v} := by
    ext x
    constructor
    · intro hx
      have hkey := (Finset.mem_filter.mp hx).2
      have hfirst := congrArg Prod.fst hkey
      have hxHigh : x ∈ orderFortyNineHighVertices G := by
        by_contra hxNot
        simp [fiveHighGraphAlignedKey, hxNot] at hfirst
      have heq : e ⟨x, hxHigh⟩ = w := by
        simpa [fiveHighGraphAlignedKey, hxHigh] using hfirst
      have hxv : x = v := by
        have hsub : (⟨x, hxHigh⟩ : {u // u ∈
            orderFortyNineHighVertices G}) = e.symm w := by
          apply e.injective
          simpa using heq
        exact congrArg Subtype.val hsub
      simp [hxv]
    · intro hx
      have hxv : x = v := by simpa using hx
      subst x
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ v, ?_⟩
      have hz := orderFortyNine_highNeighborCount_eq_zero_of_high
        G hfree hmin (Fintype.card_fin 49) hv
      have hs : fiveHighLabeledSupport G e v = ∅ :=
        Finset.card_eq_zero.mp (by
          rw [fiveHighLabeledSupport_card]
          exact hz)
      simp [fiveHighGraphAlignedKey, hv, v, hs]
  rw [hset]
  simp

theorem fiveHigh_alignedHigh_nonemptySupport_fiber_card_eq_zero
    (G : SimpleGraph (Fin 49)) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 (Fin 49) G)
    (hmin : ∀ x : Fin 49, 7 ≤ G.degree x)
    (e : {v // v ∈ orderFortyNineHighVertices G} ≃ Fin 5)
    (w : Fin 5) (S : Finset (Fin 5)) (hS : S.Nonempty) :
    Fintype.card {x : Fin 49 //
      fiveHighGraphAlignedKey G e x = (some w, S)} = 0 := by
  rw [Fintype.card_subtype, Finset.card_eq_zero]
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro x hx
  have hkey := (Finset.mem_filter.mp hx).2
  have hfirst := congrArg Prod.fst hkey
  have hsupp := congrArg Prod.snd hkey
  have hxHigh : x ∈ orderFortyNineHighVertices G := by
    by_contra hxNot
    simp [fiveHighGraphAlignedKey, hxNot] at hfirst
  have hz := orderFortyNine_highNeighborCount_eq_zero_of_high
    G hfree hmin (Fintype.card_fin 49) hxHigh
  have hcard : (fiveHighLabeledSupport G e x).card = 0 := by
    rw [fiveHighLabeledSupport_card]
    exact hz
  have hs : fiveHighLabeledSupport G e x = S := by
    simpa [fiveHighGraphAlignedKey] using hsupp
  rw [hs] at hcard
  exact hS.ne_empty (Finset.card_eq_zero.mp hcard)

theorem fiveHigh_nonempty_alignedLowFiber_card
    (G : SimpleGraph (Fin 49)) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 (Fin 49) G)
    (hmin : ∀ x : Fin 49, 7 ≤ G.degree x)
    (e : {v // v ∈ orderFortyNineHighVertices G} ≃ Fin 5)
    (S : Finset (Fin 5)) (hS : S.Nonempty) :
    Fintype.card {x : Fin 49 //
      fiveHighGraphAlignedKey G e x = (none, S)} =
      Fintype.card {x : Fin 49 // fiveHighLabeledSupport G e x = S} := by
  apply Fintype.card_congr
  let f : {x : Fin 49 // fiveHighGraphAlignedKey G e x = (none, S)} →
      {x : Fin 49 // fiveHighLabeledSupport G e x = S} := fun x =>
    ⟨x.1, by
      have hs := congrArg Prod.snd x.2
      simpa [fiveHighGraphAlignedKey] using hs⟩
  refine Equiv.ofBijective f ⟨?_, ?_⟩
  · intro x y hxy
    exact Subtype.ext (congrArg (fun z => z.1) hxy)
  · intro y
    have hyNotHigh : y.1 ∉ orderFortyNineHighVertices G := by
      intro hyHigh
      have hz := orderFortyNine_highNeighborCount_eq_zero_of_high
        G hfree hmin (Fintype.card_fin 49) hyHigh
      have hcard : (fiveHighLabeledSupport G e y.1).card = 0 := by
        rw [fiveHighLabeledSupport_card]
        exact hz
      rw [y.2] at hcard
      exact hS.ne_empty (Finset.card_eq_zero.mp hcard)
    refine ⟨⟨y.1, ?_⟩, rfl⟩
    simp [fiveHighGraphAlignedKey, hyNotHigh, y.2]

theorem fiveHigh_alignedLow_support_card_gt_three_fiber_card_eq_zero
    (G : SimpleGraph (Fin 49)) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 (Fin 49) G)
    (hmin : ∀ x : Fin 49, 7 ≤ G.degree x)
    (e : {v // v ∈ orderFortyNineHighVertices G} ≃ Fin 5)
    (S : Finset (Fin 5)) (hS : 3 < S.card) :
    Fintype.card {x : Fin 49 //
      fiveHighGraphAlignedKey G e x = (none, S)} = 0 := by
  rw [Fintype.card_subtype, Finset.card_eq_zero]
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro x hx
  have hkey := (Finset.mem_filter.mp hx).2
  have hfirst := congrArg Prod.fst hkey
  have hsupp : fiveHighLabeledSupport G e x = S := by
    simpa [fiveHighGraphAlignedKey] using congrArg Prod.snd hkey
  have hxNotHigh : x ∉ orderFortyNineHighVertices G := by
    intro hxHigh
    simp [fiveHighGraphAlignedKey, hxHigh] at hfirst
  have hx7 : G.degree x = 7 := by
    rcases orderFortyNine_degree_eq_seven_or_eight
      G hfree hmin (Fintype.card_fin 49) x with hx7 | hx8
    · exact hx7
    · exact False.elim (hxNotHigh
        (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hx8⟩))
  have hle : S.card ≤ 3 := by
    rw [← hsupp, fiveHighLabeledSupport_card]
    simpa [orderFortyNineHighSupport] using
      orderFortyNine_highNeighborCount_le_three
        G hfree hmin (Fintype.card_fin 49) hx7
  omega

def fiveHighCanonicalTripleSystem (t : Fin 3) : Finset (Finset (Fin 5)) :=
  match t with
  | 0 => ∅
  | 1 => ({({0, 1, 2} : Finset (Fin 5))} : Finset (Finset (Fin 5)))
  | 2 => ({({0, 1, 2} : Finset (Fin 5)),
      ({0, 3, 4} : Finset (Fin 5))} : Finset (Finset (Fin 5)))

def fiveHighCanonicalKeyMultiplicity
    (t : Fin 3) (key : Option (Fin 5) × Finset (Fin 5)) : Nat :=
  match key.1 with
  | some _ => if key.2 = ∅ then 1 else 0
  | none =>
      if key.2.card = 0 then 14 - t.val
      else if key.2.card = 1 then
        ((fiveHighCanonicalTripleSystem t).filter fun Q =>
          key.2 ⊆ Q).card + 4
      else if key.2.card = 2 then
        if ∃ Q ∈ fiveHighCanonicalTripleSystem t, key.2 ⊆ Q then 0 else 1
      else if key.2.card = 3 then
        if key.2 ∈ fiveHighCanonicalTripleSystem t then 1 else 0
      else 0

theorem fiveHigh_t0_mask_key_fiber_card
    (key : Option (Fin 5) × Finset (Fin 5)) :
    Fintype.card {i : Fin 49 //
      fiveHighMaskAlignedKey orderFortyNineFiveHighT0Masks i = key} =
      fiveHighCanonicalKeyMultiplicity 0 key := by
  native_decide +revert

theorem fiveHigh_t1_mask_key_fiber_card
    (key : Option (Fin 5) × Finset (Fin 5)) :
    Fintype.card {i : Fin 49 //
      fiveHighMaskAlignedKey orderFortyNineFiveHighT1Masks i = key} =
      fiveHighCanonicalKeyMultiplicity 1 key := by
  native_decide +revert

theorem fiveHigh_t2_mask_key_fiber_card
    (key : Option (Fin 5) × Finset (Fin 5)) :
    Fintype.card {i : Fin 49 //
      fiveHighMaskAlignedKey orderFortyNineFiveHighT2Masks i = key} =
      fiveHighCanonicalKeyMultiplicity 2 key := by
  native_decide +revert

theorem fiveHigh_graph_key_fiber_card_of_canonical_census
    (G : SimpleGraph (Fin 49)) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 (Fin 49) G)
    (hmin : ∀ x : Fin 49, 7 ≤ G.degree x)
    (hHigh : (orderFortyNineHighVertices G).card = 5)
    (t : Fin 3)
    (ht : orderFortyNineHighIncidenceCount G 3 = t.val)
    (e : {v // v ∈ orderFortyNineHighVertices G} ≃ Fin 5)
    (hsingle : ∀ w : Fin 5,
      Fintype.card {x : Fin 49 // fiveHighLabeledSupport G e x = {w}} =
        ((fiveHighCanonicalTripleSystem t).filter fun Q => w ∈ Q).card + 4)
    (hpair : ∀ (a b : Fin 5), (a ≠ b) →
      ((∃ q : Fin 49, (fiveHighLabeledSupport G e q).card = 3 ∧
          ({a, b} : Finset (Fin 5)) ⊆ fiveHighLabeledSupport G e q) ↔
        ∃ Q ∈ fiveHighCanonicalTripleSystem t,
          ({a, b} : Finset (Fin 5)) ⊆ Q))
    (htriple : ∀ S : Finset (Fin 5), S.card = 3 →
      Fintype.card {x : Fin 49 // fiveHighLabeledSupport G e x = S} =
        if S ∈ fiveHighCanonicalTripleSystem t then 1 else 0)
    (key : Option (Fin 5) × Finset (Fin 5)) :
    Fintype.card {x : Fin 49 // fiveHighGraphAlignedKey G e x = key} =
      fiveHighCanonicalKeyMultiplicity t key := by
  rcases key with ⟨label, S⟩
  cases label with
  | some w =>
      by_cases hS0 : S = ∅
      · subst S
        simpa [fiveHighCanonicalKeyMultiplicity] using
          fiveHigh_alignedHigh_fiber_card_eq_one G hfree hmin e w
      · have hSne : S.Nonempty := Finset.nonempty_iff_ne_empty.mpr hS0
        simpa [fiveHighCanonicalKeyMultiplicity, hS0] using
          fiveHigh_alignedHigh_nonemptySupport_fiber_card_eq_zero
            G hfree hmin e w S hSne
  | none =>
      by_cases h0 : S.card = 0
      · have hS0 : S = ∅ := Finset.card_eq_zero.mp h0
        subst S
        simpa [fiveHighCanonicalKeyMultiplicity] using
          fiveHigh_emptyLow_fiber_card_eq_fourteen_sub_triples
            G hfree hmin hHigh e t.val ht
      · by_cases h1 : S.card = 1
        · obtain ⟨w, rfl⟩ := Finset.card_eq_one.mp h1
          have hfilter :
              ((fiveHighCanonicalTripleSystem t).filter fun Q =>
                ({w} : Finset (Fin 5)) ⊆ Q) =
              (fiveHighCanonicalTripleSystem t).filter fun Q => w ∈ Q := by
            ext Q
            simp
          simpa [fiveHighCanonicalKeyMultiplicity, hfilter] using
            (fiveHigh_nonempty_alignedLowFiber_card G hfree hmin e {w}
              (by simp)).trans (hsingle w)
        · by_cases h2 : S.card = 2
          · obtain ⟨a, b, hab, rfl⟩ := Finset.card_eq_two.mp h2
            rw [fiveHigh_nonempty_alignedLowFiber_card
              G hfree hmin e {a, b} (by simp)]
            rw [fiveHigh_pair_fiber_card G hfree hmin e a b hab]
            simp [fiveHighCanonicalKeyMultiplicity, hab, hpair a b hab]
          · by_cases h3 : S.card = 3
            · rw [fiveHigh_nonempty_alignedLowFiber_card
                G hfree hmin e S (Finset.card_pos.mp (by omega))]
              simpa [fiveHighCanonicalKeyMultiplicity, h0, h1, h2, h3] using
                htriple S h3
            · have hgt : 3 < S.card := by
                have hle : S.card ≤ 5 := Finset.card_le_univ S
                omega
              simpa [fiveHighCanonicalKeyMultiplicity, h0, h1, h2, h3] using
                fiveHigh_alignedLow_support_card_gt_three_fiber_card_eq_zero
                  G hfree hmin e S hgt

theorem fiveHigh_no_triple_of_incidence_zero
    (G : SimpleGraph (Fin 49)) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 (Fin 49) G)
    (hmin : ∀ x : Fin 49, 7 ≤ G.degree x)
    (hzero : orderFortyNineHighIncidenceCount G 3 = 0)
    (e : {v // v ∈ orderFortyNineHighVertices G} ≃ Fin 5)
    (x : Fin 49) : (fiveHighLabeledSupport G e x).card ≠ 3 := by
  intro hx3
  have hxOrig3 : (orderFortyNineHighSupport G x).card = 3 := by
    rw [← fiveHighLabeledSupport_card G e x]
    exact hx3
  have hxLow : x ∈ orderFortyNineLowVertices G := by
    apply Finset.mem_sdiff.mpr
    refine ⟨Finset.mem_univ x, ?_⟩
    intro hxHigh
    have hx0 := orderFortyNine_highNeighborCount_eq_zero_of_high
      G hfree hmin (Fintype.card_fin 49) hxHigh
    change (orderFortyNineHighSupport G x).card = 0 at hx0
    omega
  have hxMem : x ∈ (orderFortyNineLowVertices G).filter fun z =>
      (orderFortyNineHighSupport G z).card = 3 :=
    Finset.mem_filter.mpr ⟨hxLow, hxOrig3⟩
  have hempty : ((orderFortyNineLowVertices G).filter fun z =>
      (orderFortyNineHighSupport G z).card = 3) = ∅ :=
    Finset.card_eq_zero.mp hzero
  rw [hempty] at hxMem
  simp at hxMem

theorem fiveHighCanonicalFiberCover_zero :
    FiveHighCanonicalFiberCover 0 orderFortyNineFiveHighT0Masks := by
  intro G _ _ _ hfree hmin hHigh hzero
  let e : {v // v ∈ orderFortyNineHighVertices G} ≃ Fin 5 :=
    Fintype.equivFinOfCardEq (by simpa using hHigh)
  refine ⟨e, orderFortyNineFiveHighT0Masks_size, ?_⟩
  intro key
  rw [fiveHigh_graph_key_fiber_card_of_canonical_census
      G hfree hmin hHigh 0 hzero e]
  · exact (fiveHigh_t0_mask_key_fiber_card key).symm
  · intro w
    have hp := fiveHigh_singleton_fiber_card_eq_triple_incidence_add_four
      G hfree hmin hHigh e w
    have hempty : ((G.neighborFinset (e.symm w).1).filter fun x =>
        (orderFortyNineHighSupport G x).card = 3) = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro x hx
      have hx3 := (Finset.mem_filter.mp hx).2
      exact fiveHigh_no_triple_of_incidence_zero G hfree hmin hzero e x
        (by simpa [fiveHighLabeledSupport_card] using hx3)
    rw [hempty] at hp
    simpa [fiveHighCanonicalTripleSystem] using hp
  · intro a b hab
    constructor
    · rintro ⟨q, hq3, -⟩
      exact False.elim
        (fiveHigh_no_triple_of_incidence_zero G hfree hmin hzero e q hq3)
    · simp [fiveHighCanonicalTripleSystem]
  · intro S hS3
    have hcard : Fintype.card {x : Fin 49 //
        fiveHighLabeledSupport G e x = S} = 0 := by
      rw [Fintype.card_subtype, Finset.card_eq_zero]
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro x hx
      have hxEq := (Finset.mem_filter.mp hx).2
      exact fiveHigh_no_triple_of_incidence_zero G hfree hmin hzero e x
        (by rw [hxEq]; exact hS3)
    simpa [fiveHighCanonicalTripleSystem] using hcard

theorem fiveHighCanonicalLabelingCover_zero :
    FiveHighCanonicalLabelingCover 0 orderFortyNineFiveHighT0Masks :=
  fiveHighCanonicalLabelingCover_of_fiberCover
    fiveHighCanonicalFiberCover_zero

end

end Erdos85
