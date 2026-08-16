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

theorem fiveHigh_t1_local_triple_card
    (G : SimpleGraph (Fin 49)) [DecidableRel G.Adj]
    (e : {v // v ∈ orderFortyNineHighVertices G} ≃ Fin 5)
    (x : Fin 49)
    (hxSupport : fiveHighLabeledSupport G e x = {0, 1, 2})
    (huniq : ∀ y : Fin 49,
      (fiveHighLabeledSupport G e y).card = 3 → y = x)
    (w : Fin 5) :
    ((G.neighborFinset (e.symm w).1).filter fun y =>
      (orderFortyNineHighSupport G y).card = 3).card =
      if w ∈ ({0, 1, 2} : Finset (Fin 5)) then 1 else 0 := by
  by_cases hw : w ∈ ({0, 1, 2} : Finset (Fin 5))
  · rw [if_pos hw]
    have hset : ((G.neighborFinset (e.symm w).1).filter fun y =>
        (orderFortyNineHighSupport G y).card = 3) = {x} := by
      ext y
      constructor
      · intro hy
        have hy3 : (fiveHighLabeledSupport G e y).card = 3 := by
          rw [fiveHighLabeledSupport_card]
          exact (Finset.mem_filter.mp hy).2
        simp [huniq y hy3]
      · intro hy
        have hyx : y = x := by simpa using hy
        subst y
        apply Finset.mem_filter.mpr
        constructor
        · simpa [SimpleGraph.mem_neighborFinset, G.adj_comm] using
            (mem_fiveHighLabeledSupport_iff G e x w).mp
              (by simpa [hxSupport] using hw)
        · rw [← fiveHighLabeledSupport_card G e x, hxSupport]
          decide
    rw [hset]
    simp
  · rw [if_neg hw, Finset.card_eq_zero]
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro y hy
    have hy3 : (fiveHighLabeledSupport G e y).card = 3 := by
      rw [fiveHighLabeledSupport_card]
      exact (Finset.mem_filter.mp hy).2
    have hyx := huniq y hy3
    have hwMem : w ∈ fiveHighLabeledSupport G e y :=
      (mem_fiveHighLabeledSupport_iff G e y w).mpr (by
        simpa [SimpleGraph.mem_neighborFinset, G.adj_comm] using
          (Finset.mem_filter.mp hy).1)
    rw [hyx, hxSupport] at hwMem
    exact hw hwMem

theorem fiveHigh_t1_triple_fiber_card
    (G : SimpleGraph (Fin 49)) [DecidableRel G.Adj]
    (e : {v // v ∈ orderFortyNineHighVertices G} ≃ Fin 5)
    (x : Fin 49)
    (hxSupport : fiveHighLabeledSupport G e x = {0, 1, 2})
    (huniq : ∀ y : Fin 49,
      (fiveHighLabeledSupport G e y).card = 3 → y = x)
    (S : Finset (Fin 5)) (hS3 : S.card = 3) :
    Fintype.card {y : Fin 49 // fiveHighLabeledSupport G e y = S} =
      if S = {0, 1, 2} then 1 else 0 := by
  by_cases hS : S = {0, 1, 2}
  · subst S
    rw [if_pos rfl, Fintype.card_subtype]
    have hset : (Finset.univ.filter fun y : Fin 49 =>
        fiveHighLabeledSupport G e y = {0, 1, 2}) = {x} := by
      ext y
      constructor
      · intro hy
        have hyEq := (Finset.mem_filter.mp hy).2
        have hy3 : (fiveHighLabeledSupport G e y).card = 3 := by
          rw [hyEq]
          decide
        simp [huniq y hy3]
      · intro hy
        have hyx : y = x := by simpa using hy
        subst y
        simp [hxSupport]
    rw [hset]
    simp
  · rw [if_neg hS, Fintype.card_subtype, Finset.card_eq_zero]
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro y hy
    have hyEq := (Finset.mem_filter.mp hy).2
    have hy3 : (fiveHighLabeledSupport G e y).card = 3 := by
      rw [hyEq]
      exact hS3
    have hyx := huniq y hy3
    apply hS
    rw [← hyEq, hyx, hxSupport]

theorem fiveHighCanonicalFiberCover_one :
    FiveHighCanonicalFiberCover 1 orderFortyNineFiveHighT1Masks := by
  intro G _ _ _ hfree hmin hHigh hone
  obtain ⟨e, x, hxSupport, huniq⟩ :=
    fiveHigh_t1_exists_normalized_labeling G hfree hmin hHigh hone
  refine ⟨e, orderFortyNineFiveHighT1Masks_size, ?_⟩
  intro key
  rw [fiveHigh_graph_key_fiber_card_of_canonical_census
      G hfree hmin hHigh 1 hone e]
  · exact (fiveHigh_t1_mask_key_fiber_card key).symm
  · intro w
    rw [fiveHigh_singleton_fiber_card_eq_triple_incidence_add_four
      G hfree hmin hHigh e w]
    rw [fiveHigh_t1_local_triple_card G e x hxSupport huniq w]
    fin_cases w <;> native_decide
  · intro a b hab
    constructor
    · rintro ⟨q, hq3, hsub⟩
      have hqx := huniq q hq3
      subst q
      simpa [fiveHighCanonicalTripleSystem, hxSupport] using hsub
    · intro h
      have hsub : ({a, b} : Finset (Fin 5)) ⊆ {0, 1, 2} := by
        simpa [fiveHighCanonicalTripleSystem] using h
      exact ⟨x, by rw [hxSupport]; decide, by simpa [hxSupport] using hsub⟩
  · intro S hS3
    have hf := fiveHigh_t1_triple_fiber_card G e x hxSupport huniq S hS3
    simpa [fiveHighCanonicalTripleSystem] using hf

theorem fiveHighCanonicalLabelingCover_one :
    FiveHighCanonicalLabelingCover 1 orderFortyNineFiveHighT1Masks :=
  fiveHighCanonicalLabelingCover_of_fiberCover
    fiveHighCanonicalFiberCover_one

theorem fiveHigh_t2_local_triple_card
    (G : SimpleGraph (Fin 49)) [DecidableRel G.Adj]
    (e : {v // v ∈ orderFortyNineHighVertices G} ≃ Fin 5)
    (x y : Fin 49)
    (hxSupport : fiveHighLabeledSupport G e x = {0, 1, 2})
    (hySupport : fiveHighLabeledSupport G e y = {0, 3, 4})
    (hxy : x ≠ y)
    (huniq : ∀ z : Fin 49,
      (fiveHighLabeledSupport G e z).card = 3 → z = x ∨ z = y)
    (w : Fin 5) :
    ((G.neighborFinset (e.symm w).1).filter fun z =>
      (orderFortyNineHighSupport G z).card = 3).card =
      ((fiveHighCanonicalTripleSystem 2).filter fun T => w ∈ T).card := by
  have hset : ((G.neighborFinset (e.symm w).1).filter fun z =>
      (orderFortyNineHighSupport G z).card = 3) =
      ({x, y} : Finset (Fin 49)).filter fun z =>
        w ∈ fiveHighLabeledSupport G e z := by
    ext z
    constructor
    · intro hz
      have hz3 : (fiveHighLabeledSupport G e z).card = 3 := by
        rw [fiveHighLabeledSupport_card]
        exact (Finset.mem_filter.mp hz).2
      have hzw : w ∈ fiveHighLabeledSupport G e z :=
        (mem_fiveHighLabeledSupport_iff G e z w).mpr (by
          simpa [SimpleGraph.mem_neighborFinset, G.adj_comm] using
            (Finset.mem_filter.mp hz).1)
      exact Finset.mem_filter.mpr ⟨by simpa using huniq z hz3, hzw⟩
    · intro hz
      have hzxy := (Finset.mem_filter.mp hz).1
      have hzw := (Finset.mem_filter.mp hz).2
      apply Finset.mem_filter.mpr
      constructor
      · simpa [SimpleGraph.mem_neighborFinset, G.adj_comm] using
          (mem_fiveHighLabeledSupport_iff G e z w).mp hzw
      · rcases (by simpa using hzxy : z = x ∨ z = y) with hzx | hzy
        · rw [hzx, ← fiveHighLabeledSupport_card G e x, hxSupport]
          decide
        · rw [hzy, ← fiveHighLabeledSupport_card G e y, hySupport]
          decide
  rw [hset]
  simp only [Finset.filter_insert, Finset.filter_singleton]
  rw [hxSupport, hySupport]
  fin_cases w <;> simp [fiveHighCanonicalTripleSystem, hxy] <;> native_decide

theorem fiveHigh_t2_exists_triple_superset_iff
    (G : SimpleGraph (Fin 49)) [DecidableRel G.Adj]
    (e : {v // v ∈ orderFortyNineHighVertices G} ≃ Fin 5)
    (x y : Fin 49)
    (hxSupport : fiveHighLabeledSupport G e x = {0, 1, 2})
    (hySupport : fiveHighLabeledSupport G e y = {0, 3, 4})
    (huniq : ∀ z : Fin 49,
      (fiveHighLabeledSupport G e z).card = 3 → z = x ∨ z = y)
    (P : Finset (Fin 5)) :
    (∃ q : Fin 49, (fiveHighLabeledSupport G e q).card = 3 ∧
      P ⊆ fiveHighLabeledSupport G e q) ↔
      ∃ T ∈ fiveHighCanonicalTripleSystem 2, P ⊆ T := by
  constructor
  · rintro ⟨q, hq3, hPq⟩
    rcases huniq q hq3 with hqx | hqy
    · refine ⟨{0, 1, 2}, by simp [fiveHighCanonicalTripleSystem], ?_⟩
      simpa [hqx, hxSupport] using hPq
    · refine ⟨{0, 3, 4}, by simp [fiveHighCanonicalTripleSystem], ?_⟩
      simpa [hqy, hySupport] using hPq
  · rintro ⟨T, hT, hPT⟩
    have hcases : T = ({0, 1, 2} : Finset (Fin 5)) ∨
        T = ({0, 3, 4} : Finset (Fin 5)) := by
      simpa [fiveHighCanonicalTripleSystem] using hT
    rcases hcases with rfl | rfl
    · refine ⟨x, by rw [hxSupport]; decide, ?_⟩
      simpa [hxSupport] using hPT
    · refine ⟨y, by rw [hySupport]; decide, ?_⟩
      simpa [hySupport] using hPT

theorem fiveHigh_t2_triple_fiber_card
    (G : SimpleGraph (Fin 49)) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 (Fin 49) G)
    (e : {v // v ∈ orderFortyNineHighVertices G} ≃ Fin 5)
    (x y : Fin 49)
    (hxSupport : fiveHighLabeledSupport G e x = {0, 1, 2})
    (hySupport : fiveHighLabeledSupport G e y = {0, 3, 4})
    (huniq : ∀ z : Fin 49,
      (fiveHighLabeledSupport G e z).card = 3 → z = x ∨ z = y)
    (S : Finset (Fin 5)) (hS3 : S.card = 3) :
    Fintype.card {z : Fin 49 // fiveHighLabeledSupport G e z = S} =
      if S ∈ fiveHighCanonicalTripleSystem 2 then 1 else 0 := by
  by_cases hmem : S ∈ fiveHighCanonicalTripleSystem 2
  · rw [if_pos hmem]
    have hcases : S = ({0, 1, 2} : Finset (Fin 5)) ∨
        S = ({0, 3, 4} : Finset (Fin 5)) := by
      simpa [fiveHighCanonicalTripleSystem] using hmem
    rcases hcases with hS | hS
    · have hone := fiveHighLabeledSupport_fiber_card_eq_one
        G hfree e x (by rw [hxSupport]; decide)
      simpa [hS, hxSupport] using hone
    · have hone := fiveHighLabeledSupport_fiber_card_eq_one
        G hfree e y (by rw [hySupport]; decide)
      simpa [hS, hySupport] using hone
  · rw [if_neg hmem, Fintype.card_subtype, Finset.card_eq_zero]
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro z hz
    have hzEq := (Finset.mem_filter.mp hz).2
    have hz3 : (fiveHighLabeledSupport G e z).card = 3 := by
      rw [hzEq]
      exact hS3
    rcases huniq z hz3 with hzx | hzy
    · apply hmem
      simp [fiveHighCanonicalTripleSystem, ← hzEq, hzx, hxSupport]
    · apply hmem
      simp [fiveHighCanonicalTripleSystem, ← hzEq, hzy, hySupport]

theorem fiveHighCanonicalFiberCover_two :
    FiveHighCanonicalFiberCover 2 orderFortyNineFiveHighT2Masks := by
  intro G _ _ _ hfree hmin hHigh htwo
  obtain ⟨e, x, y, hxSupport, hySupport, hxy, huniq⟩ :=
    fiveHigh_t2_exists_normalized_labeling G hfree hmin hHigh htwo
  refine ⟨e, orderFortyNineFiveHighT2Masks_size, ?_⟩
  intro key
  rw [fiveHigh_graph_key_fiber_card_of_canonical_census
      G hfree hmin hHigh 2 htwo e]
  · exact (fiveHigh_t2_mask_key_fiber_card key).symm
  · intro w
    rw [fiveHigh_singleton_fiber_card_eq_triple_incidence_add_four
      G hfree hmin hHigh e w]
    exact congrArg (fun n => n + 4)
      (fiveHigh_t2_local_triple_card G e x y hxSupport hySupport
        hxy huniq w)
  · intro a b _
    exact fiveHigh_t2_exists_triple_superset_iff
      G e x y hxSupport hySupport huniq {a, b}
  · intro S hS3
    exact fiveHigh_t2_triple_fiber_card
      G hfree e x y hxSupport hySupport huniq S hS3

theorem fiveHighCanonicalLabelingCover_two :
    FiveHighCanonicalLabelingCover 2 orderFortyNineFiveHighT2Masks :=
  fiveHighCanonicalLabelingCover_of_fiberCover
    fiveHighCanonicalFiberCover_two

end

end Erdos85
