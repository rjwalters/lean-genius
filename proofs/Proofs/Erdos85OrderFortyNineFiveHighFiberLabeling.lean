import Proofs.Erdos85OrderFortyNineFiveHighLabelingBridge

/-!
# Fiber construction for five-high canonical labelings

An exact label of the five high vertices together with the labeled high
support is a complete vertex key.  Equal graph-side and mask-side key-fiber
cardinalities therefore produce the required permutation of all 49 vertices.
-/

namespace Erdos85

open SimpleGraph

noncomputable section

def fiveHighLabeledSupport
    (G : SimpleGraph (Fin 49)) [DecidableRel G.Adj]
    (e : {v // v ∈ orderFortyNineHighVertices G} ≃ Fin 5)
    (x : Fin 49) : Finset (Fin 5) :=
  (finsetInSubtype (orderFortyNineHighVertices G)
    (orderFortyNineHighSupport G x)).map e.toEmbedding

theorem fiveHighLabeledSupport_card
    (G : SimpleGraph (Fin 49)) [DecidableRel G.Adj]
    (e : {v // v ∈ orderFortyNineHighVertices G} ≃ Fin 5)
    (x : Fin 49) :
    (fiveHighLabeledSupport G e x).card =
      (orderFortyNineHighSupport G x).card := by
  simp only [fiveHighLabeledSupport, Finset.card_map]
  apply card_finsetInSubtype_of_subset
  intro v hv
  exact (Finset.mem_inter.mp hv).2

theorem fiveHighLabeledSupport_inter_card
    (G : SimpleGraph (Fin 49)) [DecidableRel G.Adj]
    (e : {v // v ∈ orderFortyNineHighVertices G} ≃ Fin 5)
    (x y : Fin 49) :
    (fiveHighLabeledSupport G e x ∩ fiveHighLabeledSupport G e y).card =
      (orderFortyNineHighSupport G x ∩
        orderFortyNineHighSupport G y).card := by
  simp only [fiveHighLabeledSupport, ← Finset.map_inter,
    Finset.card_map, inter_finsetInSubtype]
  apply card_finsetInSubtype_of_subset
  intro v hv
  exact (Finset.mem_inter.mp (Finset.mem_inter.mp hv).1).2

theorem fiveHighLabeledSupport_injective_of_two_le
    (G : SimpleGraph (Fin 49)) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 (Fin 49) G)
    (e : {v // v ∈ orderFortyNineHighVertices G} ≃ Fin 5)
    {x y : Fin 49} (hx : 2 ≤ (fiveHighLabeledSupport G e x).card)
    (hxy : fiveHighLabeledSupport G e x = fiveHighLabeledSupport G e y) :
    x = y := by
  by_contra hne
  have hle := orderFortyNine_card_inter_highSupport_le_one G hfree hne
  have hinter := fiveHighLabeledSupport_inter_card G e x y
  have hcards := congrArg Finset.card hxy
  rw [hxy, Finset.inter_self] at hinter
  omega

theorem fiveHighLabeledSupport_fiber_card_eq_one
    (G : SimpleGraph (Fin 49)) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 (Fin 49) G)
    (e : {v // v ∈ orderFortyNineHighVertices G} ≃ Fin 5)
    (x : Fin 49) (hx : 2 ≤ (fiveHighLabeledSupport G e x).card) :
    Fintype.card {y : Fin 49 // fiveHighLabeledSupport G e y =
      fiveHighLabeledSupport G e x} = 1 := by
  rw [Fintype.card_subtype]
  have hfilter : (Finset.univ.filter fun y : Fin 49 =>
      fiveHighLabeledSupport G e y = fiveHighLabeledSupport G e x) = {x} := by
    ext y
    simp only [Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_singleton]
    constructor
    · intro hy
      exact (fiveHighLabeledSupport_injective_of_two_le
        G hfree e hx hy.symm).symm
    · rintro rfl
      rfl
  rw [hfilter]
  simp

theorem mem_fiveHighLabeledSupport_iff
    (G : SimpleGraph (Fin 49)) [DecidableRel G.Adj]
    (e : {v // v ∈ orderFortyNineHighVertices G} ≃ Fin 5)
    (x : Fin 49) (w : Fin 5) :
    w ∈ fiveHighLabeledSupport G e x ↔ G.Adj x (e.symm w).1 := by
  constructor
  · intro hw
    obtain ⟨v, hv, hev⟩ := Finset.mem_map.mp hw
    have hvSupport : v.1 ∈ orderFortyNineHighSupport G x :=
      mem_finsetInSubtype_iff.mp hv
    have hve : v = e.symm w := by
      apply e.injective
      simpa using hev
    simpa [hve, SimpleGraph.mem_neighborFinset] using
      (Finset.mem_inter.mp hvSupport).1
  · intro hxw
    apply Finset.mem_map.mpr
    refine ⟨e.symm w, ?_, by simp⟩
    apply mem_finsetInSubtype_iff.mpr
    exact Finset.mem_inter.mpr
      ⟨by simpa [SimpleGraph.mem_neighborFinset] using hxw, (e.symm w).2⟩

def fiveHighMaskSupport (masks : Array Nat) (i : Fin 49) :
    Finset (Fin 5) :=
  Finset.univ.filter fun w =>
    (orderFortyNineSupportMask masks i).getLsbD w.val

def fiveHighGraphAlignedKey
    (G : SimpleGraph (Fin 49)) [DecidableRel G.Adj]
    (e : {v // v ∈ orderFortyNineHighVertices G} ≃ Fin 5)
    (x : Fin 49) : Option (Fin 5) × Finset (Fin 5) :=
  (if hx : x ∈ orderFortyNineHighVertices G then some (e ⟨x, hx⟩) else none,
    fiveHighLabeledSupport G e x)

def fiveHighMaskAlignedKey (masks : Array Nat) (i : Fin 49) :
    Option (Fin 5) × Finset (Fin 5) :=
  (if hi : i.val < 5 then some ⟨i.val, hi⟩ else none,
    fiveHighMaskSupport masks i)

theorem exists_fiveHigh_keyAlignedLabeling_of_fiberCardEq
    (G : SimpleGraph (Fin 49)) [DecidableRel G.Adj]
    (e : {v // v ∈ orderFortyNineHighVertices G} ≃ Fin 5)
    (masks : Array Nat)
    (hcard : ∀ key : Option (Fin 5) × Finset (Fin 5),
      Fintype.card {x : Fin 49 // fiveHighGraphAlignedKey G e x = key} =
      Fintype.card {i : Fin 49 // fiveHighMaskAlignedKey masks i = key}) :
    ∃ E : Equiv.Perm (Fin 49), ∀ x,
      fiveHighMaskAlignedKey masks (E x) =
        fiveHighGraphAlignedKey G e x := by
  let E := equivOfFiberCardEq
    (fiveHighGraphAlignedKey G e) (fiveHighMaskAlignedKey masks) hcard
  exact ⟨E, fun x => equivOfFiberCardEq_map _ _ hcard x⟩

theorem fiveHigh_keyAlignedLabeling_support
    (G : SimpleGraph (Fin 49)) [DecidableRel G.Adj]
    (e : {v // v ∈ orderFortyNineHighVertices G} ≃ Fin 5)
    (masks : Array Nat) (E : Equiv.Perm (Fin 49))
    (hE : ∀ x, fiveHighMaskAlignedKey masks (E x) =
      fiveHighGraphAlignedKey G e x) (x : Fin 49) :
    fiveHighMaskSupport masks (E x) = fiveHighLabeledSupport G e x :=
  congrArg Prod.snd (hE x)

theorem fiveHigh_keyAlignedLabeling_high_iff
    (G : SimpleGraph (Fin 49)) [DecidableRel G.Adj]
    (e : {v // v ∈ orderFortyNineHighVertices G} ≃ Fin 5)
    (masks : Array Nat) (E : Equiv.Perm (Fin 49))
    (hE : ∀ x, fiveHighMaskAlignedKey masks (E x) =
      fiveHighGraphAlignedKey G e x) (x : Fin 49) :
    (E x).val < 5 ↔ x ∈ orderFortyNineHighVertices G := by
  have hfirst := congrArg Prod.fst (hE x)
  by_cases hi : (E x).val < 5 <;>
    by_cases hx : x ∈ orderFortyNineHighVertices G <;>
    simp [fiveHighMaskAlignedKey, fiveHighGraphAlignedKey, hi, hx] at hfirst ⊢

theorem fiveHigh_keyAlignedLabeling_high_image
    (G : SimpleGraph (Fin 49)) [DecidableRel G.Adj]
    (e : {v // v ∈ orderFortyNineHighVertices G} ≃ Fin 5)
    (masks : Array Nat) (E : Equiv.Perm (Fin 49))
    (hE : ∀ x, fiveHighMaskAlignedKey masks (E x) =
      fiveHighGraphAlignedKey G e x) (w : Fin 5) :
    E (e.symm w).1 = ⟨w.val, by omega⟩ := by
  have hfirst := congrArg Prod.fst (hE (e.symm w).1)
  have hsome :
      (if hi : (E (e.symm w).1).val < 5
        then some (⟨(E (e.symm w).1).val, hi⟩ : Fin 5)
        else none) = some w := by
    simpa [fiveHighMaskAlignedKey, fiveHighGraphAlignedKey] using hfirst
  by_cases hi : (E (e.symm w).1).val < 5
  · simp [hi] at hsome
    have hval : (E (e.symm w).1).val = w.val :=
      congrArg Fin.val hsome
    apply Fin.ext
    exact hval
  · exfalso
    simp [hi] at hsome

theorem fiveHigh_keyAlignedLabeling_degree
    (G : SimpleGraph (Fin 49)) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 (Fin 49) G)
    (hmin : ∀ x : Fin 49, 7 ≤ G.degree x)
    (e : {v // v ∈ orderFortyNineHighVertices G} ≃ Fin 5)
    (masks : Array Nat) (E : Equiv.Perm (Fin 49))
    (hE : ∀ x, fiveHighMaskAlignedKey masks (E x) =
      fiveHighGraphAlignedKey G e x) (i : Fin 49) :
    (orderFortyNineRelabeledGraph G E).degree i =
      if i.val < 5 then 8 else 7 := by
  rw [orderFortyNineRelabeledGraph_degree]
  have hhigh := fiveHigh_keyAlignedLabeling_high_iff
    G e masks E hE (E.symm i)
  simp only [E.apply_symm_apply] at hhigh
  by_cases hi : i.val < 5
  · rw [if_pos hi]
    exact (Finset.mem_filter.mp (hhigh.mp hi)).2
  · rw [if_neg hi]
    rcases orderFortyNine_degree_eq_seven_or_eight
      G hfree hmin (Fintype.card_fin 49) (E.symm i) with h7 | h8
    · exact h7
    · exfalso
      exact hi (hhigh.mpr (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h8⟩))

theorem fiveHigh_keyAlignedLabeling_supportBit
    (G : SimpleGraph (Fin 49)) [DecidableRel G.Adj]
    (e : {v // v ∈ orderFortyNineHighVertices G} ≃ Fin 5)
    (masks : Array Nat) (E : Equiv.Perm (Fin 49))
    (hE : ∀ x, fiveHighMaskAlignedKey masks (E x) =
      fiveHighGraphAlignedKey G e x)
    (i : Fin 49) (w : Fin 9) (hw : w.val < 5) :
    decide ((orderFortyNineRelabeledGraph G E).Adj
      i ⟨w.val, by omega⟩) =
      (orderFortyNineSupportMask masks i).getLsbD w.val := by
  let w5 : Fin 5 := ⟨w.val, hw⟩
  let wi : Fin 49 := ⟨w.val, by omega⟩
  have himage : E (e.symm w5).1 = wi :=
    fiveHigh_keyAlignedLabeling_high_image G e masks E hE w5
  have hsymm : E.symm wi = (e.symm w5).1 := by
    apply E.injective
    simp [himage]
  have hs := fiveHigh_keyAlignedLabeling_support
    G e masks E hE (E.symm i)
  have hs' : fiveHighMaskSupport masks i =
      fiveHighLabeledSupport G e (E.symm i) := by simpa using hs
  rw [Bool.eq_iff_iff]
  simp only [decide_eq_true_eq]
  change (orderFortyNineRelabeledGraph G E).Adj i wi ↔ _
  rw [orderFortyNineRelabeledGraph_adj, hsymm]
  rw [← mem_fiveHighLabeledSupport_iff, ← hs']
  simp [fiveHighMaskSupport, w5]

theorem fiveHigh_keyAlignedLabeling_lowPartition
    (G : SimpleGraph (Fin 49)) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 (Fin 49) G)
    (hmin : ∀ x : Fin 49, 7 ≤ G.degree x)
    (e : {v // v ∈ orderFortyNineHighVertices G} ≃ Fin 5)
    (masks : Array Nat) (E : Equiv.Perm (Fin 49))
    (hE : ∀ x, fiveHighMaskAlignedKey masks (E x) =
      fiveHighGraphAlignedKey G e x)
    (i : Fin 49) (hi : 5 ≤ i.val) (w : Fin 9) (hw : w.val < 5) :
    ((orderFortyNineRelabeledGraph G E).neighborFinset i ∩
      orderFortyNineSupportFiber masks w).card = 1 := by
  let H := orderFortyNineRelabeledGraph G E
  let w5 : Fin 5 := ⟨w.val, hw⟩
  have hiNot : ¬ i.val < 5 := by omega
  have hy : G.degree (E.symm i) = 7 := by
    have hd := fiveHigh_keyAlignedLabeling_degree
      G hfree hmin e masks E hE i
    rw [orderFortyNineRelabeledGraph_degree, if_neg hiNot] at hd
    exact hd
  obtain ⟨x, hx, huniq⟩ :=
    orderFortyNine_low_neighborhood_partitions_highs
      G hfree hmin (Fintype.card_fin 49) hy (e.symm w5).2
  have hset : H.neighborFinset i ∩ orderFortyNineSupportFiber masks w =
      {E x} := by
    ext k
    constructor
    · intro hk
      have hkN : H.Adj i k := by
        simpa [SimpleGraph.mem_neighborFinset] using
          (Finset.mem_inter.mp hk).1
      have hkBit :
          (orderFortyNineSupportMask masks k).getLsbD w.val = true := by
        simpa [orderFortyNineSupportFiber] using
          (Finset.mem_inter.mp hk).2
      have hkHigh := fiveHigh_keyAlignedLabeling_supportBit
        G e masks E hE k w hw
      have hkAdjHigh : H.Adj k ⟨w.val, by omega⟩ := by
        apply of_decide_eq_true
        rw [hkHigh]
        exact hkBit
      have hhighImage := fiveHigh_keyAlignedLabeling_high_image
        G e masks E hE w5
      have hhighSymm : E.symm (⟨w.val, by omega⟩ : Fin 49) =
          (e.symm w5).1 := by
        apply E.injective
        simpa using hhighImage.symm
      have hkOrigN : E.symm k ∈ G.neighborFinset (E.symm i) := by
        simpa [H, orderFortyNineRelabeledGraph,
          SimpleGraph.mem_neighborFinset] using hkN
      have hkOrigHigh : G.Adj (E.symm k) (e.symm w5).1 := by
        simpa [H, orderFortyNineRelabeledGraph, hhighSymm] using hkAdjHigh
      have hek : E.symm k = x := huniq (E.symm k) ⟨hkOrigN, hkOrigHigh⟩
      have : k = E x := by
        apply E.symm.injective
        simpa using hek
      simp [this]
    · intro hk
      have hkEq : k = E x := by simpa using hk
      subst k
      apply Finset.mem_inter.mpr
      constructor
      · simpa [H, orderFortyNineRelabeledGraph,
          SimpleGraph.mem_neighborFinset] using hx.1
      · have hmem : w5 ∈ fiveHighLabeledSupport G e x :=
          (mem_fiveHighLabeledSupport_iff G e x w5).mpr hx.2
        have hs := fiveHigh_keyAlignedLabeling_support G e masks E hE x
        have : w5 ∈ fiveHighMaskSupport masks (E x) := by
          rw [hs]
          exact hmem
        simpa [orderFortyNineSupportFiber, fiveHighMaskSupport, w5] using this
  rw [hset]
  simp

theorem fiveHighAlignedLabeling_of_keyAligned
    (G : SimpleGraph (Fin 49)) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 (Fin 49) G)
    (hmin : ∀ x : Fin 49, 7 ≤ G.degree x)
    (e : {v // v ∈ orderFortyNineHighVertices G} ≃ Fin 5)
    (masks : Array Nat) (hsize : masks.size = 49)
    (E : Equiv.Perm (Fin 49))
    (hE : ∀ x, fiveHighMaskAlignedKey masks (E x) =
      fiveHighGraphAlignedKey G e x) :
    FiveHighAlignedLabeling G E masks := by
  refine ⟨hsize, ?_, ?_, ?_⟩
  · exact fiveHigh_keyAlignedLabeling_degree G hfree hmin e masks E hE
  · exact fiveHigh_keyAlignedLabeling_supportBit G e masks E hE
  · exact fiveHigh_keyAlignedLabeling_lowPartition
      G hfree hmin e masks E hE

def FiveHighCanonicalFiberCover (blocks : Nat) (masks : Array Nat) : Prop :=
  ∀ (G : SimpleGraph (Fin 49)) (_ : DecidableRel G.Adj)
    (_ : DecidableRel (antipodalGraph G).Adj)
    (_ : DecidableRel (triangleFreeEdgeGraph G).Adj),
    (¬ containsC4 (Fin 49) G) →
    (∀ x : Fin 49, 7 ≤ G.degree x) →
    (orderFortyNineHighVertices G).card = 5 →
    orderFortyNineHighIncidenceCount G 3 = blocks →
    ∃ e : {v // v ∈ orderFortyNineHighVertices G} ≃ Fin 5,
      masks.size = 49 ∧
      ∀ key : Option (Fin 5) × Finset (Fin 5),
        Fintype.card {x : Fin 49 // fiveHighGraphAlignedKey G e x = key} =
        Fintype.card {i : Fin 49 // fiveHighMaskAlignedKey masks i = key}

theorem fiveHighCanonicalLabelingCover_of_fiberCover
    {blocks : Nat} {masks : Array Nat}
    (hcover : FiveHighCanonicalFiberCover blocks masks) :
    FiveHighCanonicalLabelingCover blocks masks := by
  intro G _ _ _ hfree hmin hhigh hblocks
  obtain ⟨e, hsize, hfibers⟩ :=
    hcover G inferInstance inferInstance inferInstance
      hfree hmin hhigh hblocks
  obtain ⟨E, hE⟩ := exists_fiveHigh_keyAlignedLabeling_of_fiberCardEq
    G e masks hfibers
  refine ⟨E, ?_⟩
  exact fiveHighAlignedLabeling_of_keyAligned
    G hfree hmin e masks hsize E hE

theorem fiveHigh_singleton_fiber_card_eq_local
    (G : SimpleGraph (Fin 49)) [DecidableRel G.Adj]
    (e : {v // v ∈ orderFortyNineHighVertices G} ≃ Fin 5)
    (w : Fin 5) :
    Fintype.card {x : Fin 49 // fiveHighLabeledSupport G e x = {w}} =
      ((G.neighborFinset (e.symm w).1).filter fun x =>
        (orderFortyNineHighSupport G x).card = 1).card := by
  rw [Fintype.card_subtype]
  congr 1
  ext x
  constructor
  · intro hx
    have hs := (Finset.mem_filter.mp hx).2
    apply Finset.mem_filter.mpr
    constructor
    · have hw : w ∈ fiveHighLabeledSupport G e x := by simp [hs]
      simpa [SimpleGraph.mem_neighborFinset, G.adj_comm] using
        (mem_fiveHighLabeledSupport_iff G e x w).mp hw
    · rw [← fiveHighLabeledSupport_card G e x, hs]
      simp
  · intro hx
    have hxN := (Finset.mem_filter.mp hx).1
    have hxCard := (Finset.mem_filter.mp hx).2
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ x, ?_⟩
    have hw : w ∈ fiveHighLabeledSupport G e x := by
      apply (mem_fiveHighLabeledSupport_iff G e x w).mpr
      simpa [SimpleGraph.mem_neighborFinset, G.adj_comm] using hxN
    have hcard : (fiveHighLabeledSupport G e x).card = 1 := by
      rw [fiveHighLabeledSupport_card]
      exact hxCard
    obtain ⟨z, hz⟩ := Finset.card_eq_one.mp hcard
    have hwz : w = z := by
      rw [hz] at hw
      simpa using hw
    simpa [hz, hwz]

/-- At five highs, a singleton support occurs four more times than a triple
support through the same high point. -/
theorem fiveHigh_singleton_fiber_card_eq_triple_incidence_add_four
    (G : SimpleGraph (Fin 49)) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 (Fin 49) G)
    (hmin : ∀ x : Fin 49, 7 ≤ G.degree x)
    (hHigh : (orderFortyNineHighVertices G).card = 5)
    (e : {v // v ∈ orderFortyNineHighVertices G} ≃ Fin 5)
    (w : Fin 5) :
    Fintype.card {x : Fin 49 // fiveHighLabeledSupport G e x = {w}} =
      ((G.neighborFinset (e.symm w).1).filter fun x =>
        (orderFortyNineHighSupport G x).card = 3).card + 4 := by
  rw [fiveHigh_singleton_fiber_card_eq_local]
  have hv8 : G.degree (e.symm w).1 = 8 :=
    (Finset.mem_filter.mp (e.symm w).2).2
  have hp := orderFortyNine_highNeighborhood_general_profile
    G hfree hmin (Fintype.card_fin 49) hv8
  dsimp only at hp
  rw [hHigh] at hp
  omega

theorem fiveHigh_existsUnique_labeled_pairBlock
    (G : SimpleGraph (Fin 49)) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 (Fin 49) G)
    (hmin : ∀ x : Fin 49, 7 ≤ G.degree x)
    (e : {v // v ∈ orderFortyNineHighVertices G} ≃ Fin 5)
    {a b : Fin 5} (hab : a ≠ b) :
    ∃! x : Fin 49, ({a, b} : Finset (Fin 5)) ⊆
        fiveHighLabeledSupport G e x ∧
      ((fiveHighLabeledSupport G e x).card = 2 ∨
       (fiveHighLabeledSupport G e x).card = 3) := by
  have hvab : (e.symm a).1 ≠ (e.symm b).1 := by
    intro h
    apply hab
    apply e.symm.injective
    exact Subtype.ext h
  obtain ⟨x, hx, huniq⟩ := orderFortyNine_existsUnique_pairBlock_of_highs
    G hfree hmin (Fintype.card_fin 49)
      (e.symm a).2 (e.symm b).2 hvab
  refine ⟨x, ?_, ?_⟩
  · refine ⟨?_, ?_⟩
    · intro w hw
      simp only [Finset.mem_insert, Finset.mem_singleton] at hw
      rcases hw with hw | hw
      · rw [hw]
        exact (mem_fiveHighLabeledSupport_iff G e x _).mpr hx.1.symm
      · rw [hw]
        exact (mem_fiveHighLabeledSupport_iff G e x _).mpr hx.2.1.symm
    · simpa [fiveHighLabeledSupport_card] using hx.2.2.2
  · intro y hy
    apply huniq y
    have ha := hy.1 (by simp : a ∈ ({a, b} : Finset (Fin 5)))
    have hb := hy.1 (by simp : b ∈ ({a, b} : Finset (Fin 5)))
    refine ⟨?_, ?_, ?_, ?_⟩
    · simpa [G.adj_comm] using
        (mem_fiveHighLabeledSupport_iff G e y a).mp ha
    · simpa [G.adj_comm] using
        (mem_fiveHighLabeledSupport_iff G e y b).mp hb
    · exact orderFortyNine_neighbor_degree_seven_of_degreeEight
        G hfree hmin (Fintype.card_fin 49)
          (Finset.mem_filter.mp (e.symm a).2).2 (by
            simpa [G.adj_comm] using
              (mem_fiveHighLabeledSupport_iff G e y a).mp ha)
    · simpa [fiveHighLabeledSupport_card] using hy.2

/-- A high pair has one exact pair-block unless it is already covered by a
triple, in which case linearity forces the exact pair fiber to be empty. -/
theorem fiveHigh_pair_fiber_card
    (G : SimpleGraph (Fin 49)) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 (Fin 49) G)
    (hmin : ∀ x : Fin 49, 7 ≤ G.degree x)
    (e : {v // v ∈ orderFortyNineHighVertices G} ≃ Fin 5)
    (a b : Fin 5) (hab : a ≠ b) :
    Fintype.card {z : Fin 49 // fiveHighLabeledSupport G e z = {a, b}} =
      if ∃ q : Fin 49,
          (fiveHighLabeledSupport G e q).card = 3 ∧
          ({a, b} : Finset (Fin 5)) ⊆ fiveHighLabeledSupport G e q
        then 0 else 1 := by
  obtain ⟨z, hz, hzuniq⟩ :=
    fiveHigh_existsUnique_labeled_pairBlock G hfree hmin e hab
  by_cases htriple : ∃ q : Fin 49,
      (fiveHighLabeledSupport G e q).card = 3 ∧
      ({a, b} : Finset (Fin 5)) ⊆ fiveHighLabeledSupport G e q
  · rw [if_pos htriple, Fintype.card_subtype, Finset.card_eq_zero]
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro u hu
    have huEq := (Finset.mem_filter.mp hu).2
    have huQual : ({a, b} : Finset (Fin 5)) ⊆
        fiveHighLabeledSupport G e u ∧
        ((fiveHighLabeledSupport G e u).card = 2 ∨
         (fiveHighLabeledSupport G e u).card = 3) := by
      refine ⟨by rw [huEq], Or.inl ?_⟩
      rw [huEq]
      simp [hab]
    obtain ⟨q, hq3, hqSub⟩ := htriple
    have hqQual : ({a, b} : Finset (Fin 5)) ⊆
        fiveHighLabeledSupport G e q ∧
        ((fiveHighLabeledSupport G e q).card = 2 ∨
         (fiveHighLabeledSupport G e q).card = 3) :=
      ⟨hqSub, Or.inr hq3⟩
    have huq : u = q := (hzuniq u huQual).trans (hzuniq q hqQual).symm
    have := congrArg (fun v => (fiveHighLabeledSupport G e v).card) huq
    rw [huEq] at this
    simp [hab] at this
    omega
  · rw [if_neg htriple]
    have hz2 : (fiveHighLabeledSupport G e z).card = 2 := by
      rcases hz.2 with hz2 | hz3
      · exact hz2
      · exact False.elim (htriple ⟨z, hz3, hz.1⟩)
    have hzEq : fiveHighLabeledSupport G e z = {a, b} :=
      (Finset.eq_of_subset_of_card_le hz.1 (by simp [hab, hz2])).symm
    have hone := fiveHighLabeledSupport_fiber_card_eq_one
      G hfree e z (by omega)
    simpa [hzEq] using hone

theorem fiveHigh_aligned_emptyLow_fiber_card
    (G : SimpleGraph (Fin 49)) [DecidableRel G.Adj]
    (e : {v // v ∈ orderFortyNineHighVertices G} ≃ Fin 5) :
    Fintype.card {x : Fin 49 //
      fiveHighGraphAlignedKey G e x = (none, ∅)} =
      orderFortyNineHighIncidenceCount G 0 := by
  rw [Fintype.card_subtype]
  have hset : (Finset.univ.filter fun x : Fin 49 =>
      fiveHighGraphAlignedKey G e x = (none, ∅)) =
      (orderFortyNineLowVertices G).filter fun x =>
        (orderFortyNineHighSupport G x).card = 0 := by
    ext x
    constructor
    · intro hx
      have hkey := (Finset.mem_filter.mp hx).2
      have hfirst := congrArg Prod.fst hkey
      have hsupp := congrArg Prod.snd hkey
      have hxNotHigh : x ∉ orderFortyNineHighVertices G := by
        intro hxHigh
        simp [fiveHighGraphAlignedKey, hxHigh] at hfirst
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_sdiff.mpr ⟨Finset.mem_univ x, hxNotHigh⟩, ?_⟩
      have : fiveHighLabeledSupport G e x = ∅ := by
        simpa [fiveHighGraphAlignedKey] using hsupp
      rw [← fiveHighLabeledSupport_card G e x, this]
      simp
    · intro hx
      have hxLow := (Finset.mem_filter.mp hx).1
      have hx0 := (Finset.mem_filter.mp hx).2
      have hxNotHigh := (Finset.mem_sdiff.mp hxLow).2
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ x, ?_⟩
      have hs : fiveHighLabeledSupport G e x = ∅ :=
        Finset.card_eq_zero.mp (by
          rw [fiveHighLabeledSupport_card]
          exact hx0)
      simp [fiveHighGraphAlignedKey, hxNotHigh, hs]
  rw [hset]
  rfl

theorem fiveHigh_emptyLow_fiber_card_eq_fourteen_sub_triples
    (G : SimpleGraph (Fin 49)) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 (Fin 49) G)
    (hmin : ∀ x : Fin 49, 7 ≤ G.degree x)
    (hHigh : (orderFortyNineHighVertices G).card = 5)
    (e : {v // v ∈ orderFortyNineHighVertices G} ≃ Fin 5)
    (t : Nat) (ht : orderFortyNineHighIncidenceCount G 3 = t) :
    Fintype.card {x : Fin 49 //
      fiveHighGraphAlignedKey G e x = (none, ∅)} = 14 - t := by
  rw [fiveHigh_aligned_emptyLow_fiber_card]
  have hp := orderFortyNine_highIncidence_general_profile
    G hfree hmin (Fintype.card_fin 49)
  dsimp only at hp
  rw [hHigh, ht] at hp
  omega

end

end Erdos85
