import Proofs.Erdos85OrderFortyNineSmallHighLabelingBridge

/-!
# Fiber construction for small-high canonical labelings

An exact high label together with the labeled high-support set is a complete
vertex key.  Equality of all graph-side and mask-side key-fiber cardinalities
therefore constructs the required permutation of all 49 vertices.  The core
argument is uniform in the high count `h`; the final definitions specialize
it to the canonical h=3 and h=5 mask arrays.
-/

namespace Erdos85

open SimpleGraph
open OrderFortyNineSmallHighCensus

noncomputable section

def smallHighLabeledSupport
    (G : SimpleGraph (Fin 49)) [DecidableRel G.Adj]
    (e : {v // v ∈ orderFortyNineHighVertices G} ≃ Fin h)
    (x : Fin 49) : Finset (Fin h) :=
  (finsetInSubtype (orderFortyNineHighVertices G)
    (orderFortyNineHighSupport G x)).map e.toEmbedding

theorem smallHighLabeledSupport_card
    (G : SimpleGraph (Fin 49)) [DecidableRel G.Adj]
    (e : {v // v ∈ orderFortyNineHighVertices G} ≃ Fin h)
    (x : Fin 49) :
    (smallHighLabeledSupport G e x).card =
      (orderFortyNineHighSupport G x).card := by
  simp only [smallHighLabeledSupport, Finset.card_map]
  apply card_finsetInSubtype_of_subset
  intro v hv
  exact (Finset.mem_inter.mp hv).2

theorem smallHighLabeledSupport_inter_card
    (G : SimpleGraph (Fin 49)) [DecidableRel G.Adj]
    (e : {v // v ∈ orderFortyNineHighVertices G} ≃ Fin h)
    (x y : Fin 49) :
    (smallHighLabeledSupport G e x ∩ smallHighLabeledSupport G e y).card =
      (orderFortyNineHighSupport G x ∩
        orderFortyNineHighSupport G y).card := by
  simp only [smallHighLabeledSupport, ← Finset.map_inter,
    Finset.card_map, inter_finsetInSubtype]
  apply card_finsetInSubtype_of_subset
  intro v hv
  exact (Finset.mem_inter.mp (Finset.mem_inter.mp hv).1).2

theorem smallHighLabeledSupport_injective_of_two_le
    (G : SimpleGraph (Fin 49)) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 (Fin 49) G)
    (e : {v // v ∈ orderFortyNineHighVertices G} ≃ Fin h)
    {x y : Fin 49} (hx : 2 ≤ (smallHighLabeledSupport G e x).card)
    (hxy : smallHighLabeledSupport G e x =
      smallHighLabeledSupport G e y) : x = y := by
  by_contra hne
  have hle := orderFortyNine_card_inter_highSupport_le_one G hfree hne
  have hinter := smallHighLabeledSupport_inter_card G e x y
  have hcards := congrArg Finset.card hxy
  rw [hxy, Finset.inter_self] at hinter
  omega

theorem smallHighLabeledSupport_fiber_card_eq_one
    (G : SimpleGraph (Fin 49)) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 (Fin 49) G)
    (e : {v // v ∈ orderFortyNineHighVertices G} ≃ Fin h)
    (x : Fin 49) (hx : 2 ≤ (smallHighLabeledSupport G e x).card) :
    Fintype.card {y : Fin 49 // smallHighLabeledSupport G e y =
      smallHighLabeledSupport G e x} = 1 := by
  rw [Fintype.card_subtype]
  have hfilter : (Finset.univ.filter fun y : Fin 49 =>
      smallHighLabeledSupport G e y = smallHighLabeledSupport G e x) =
      {x} := by
    ext y
    simp only [Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_singleton]
    constructor
    · intro hy
      exact (smallHighLabeledSupport_injective_of_two_le
        G hfree e hx hy.symm).symm
    · rintro rfl
      rfl
  rw [hfilter]
  simp

theorem mem_smallHighLabeledSupport_iff
    (G : SimpleGraph (Fin 49)) [DecidableRel G.Adj]
    (e : {v // v ∈ orderFortyNineHighVertices G} ≃ Fin h)
    (x : Fin 49) (w : Fin h) :
    w ∈ smallHighLabeledSupport G e x ↔ G.Adj x (e.symm w).1 := by
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

def smallHighMaskSupport (masks : Array Nat) (i : Fin 49) :
    Finset (Fin h) :=
  Finset.univ.filter fun w =>
    (orderFortyNineSupportMask masks i).getLsbD w.val

def smallHighGraphAlignedKey
    (G : SimpleGraph (Fin 49)) [DecidableRel G.Adj]
    (e : {v // v ∈ orderFortyNineHighVertices G} ≃ Fin h)
    (x : Fin 49) : Option (Fin h) × Finset (Fin h) :=
  (if hx : x ∈ orderFortyNineHighVertices G then some (e ⟨x, hx⟩) else none,
    smallHighLabeledSupport G e x)

def smallHighMaskAlignedKey (masks : Array Nat) (i : Fin 49) :
    Option (Fin h) × Finset (Fin h) :=
  (if hi : i.val < h then some ⟨i.val, hi⟩ else none,
    smallHighMaskSupport masks i)

theorem exists_smallHigh_keyAlignedLabeling_of_fiberCardEq
    (G : SimpleGraph (Fin 49)) [DecidableRel G.Adj]
    (e : {v // v ∈ orderFortyNineHighVertices G} ≃ Fin h)
    (masks : Array Nat)
    (hcard : ∀ key : Option (Fin h) × Finset (Fin h),
      Fintype.card {x : Fin 49 // smallHighGraphAlignedKey G e x = key} =
      Fintype.card {i : Fin 49 // smallHighMaskAlignedKey masks i = key}) :
    ∃ E : Equiv.Perm (Fin 49), ∀ x,
      smallHighMaskAlignedKey masks (E x) =
        smallHighGraphAlignedKey G e x := by
  let E := equivOfFiberCardEq
    (smallHighGraphAlignedKey G e) (smallHighMaskAlignedKey masks) hcard
  exact ⟨E, fun x => equivOfFiberCardEq_map _ _ hcard x⟩

theorem smallHigh_keyAlignedLabeling_support
    (G : SimpleGraph (Fin 49)) [DecidableRel G.Adj]
    (e : {v // v ∈ orderFortyNineHighVertices G} ≃ Fin h)
    (masks : Array Nat) (E : Equiv.Perm (Fin 49))
    (hE : ∀ x, smallHighMaskAlignedKey masks (E x) =
      smallHighGraphAlignedKey G e x) (x : Fin 49) :
    smallHighMaskSupport masks (E x) = smallHighLabeledSupport G e x := by
  exact congrArg Prod.snd (hE x)

theorem smallHigh_keyAlignedLabeling_high_iff
    (G : SimpleGraph (Fin 49)) [DecidableRel G.Adj]
    (e : {v // v ∈ orderFortyNineHighVertices G} ≃ Fin h)
    (masks : Array Nat) (E : Equiv.Perm (Fin 49))
    (hE : ∀ x, smallHighMaskAlignedKey masks (E x) =
      smallHighGraphAlignedKey G e x) (x : Fin 49) :
    (E x).val < h ↔ x ∈ orderFortyNineHighVertices G := by
  have hfirst := congrArg Prod.fst (hE x)
  by_cases hi : (E x).val < h <;>
    by_cases hx : x ∈ orderFortyNineHighVertices G <;>
    simp [smallHighMaskAlignedKey, smallHighGraphAlignedKey, hi, hx] at hfirst ⊢

theorem smallHigh_keyAlignedLabeling_high_image
    (G : SimpleGraph (Fin 49)) [DecidableRel G.Adj]
    (hh : h ≤ 9)
    (e : {v // v ∈ orderFortyNineHighVertices G} ≃ Fin h)
    (masks : Array Nat) (E : Equiv.Perm (Fin 49))
    (hE : ∀ x, smallHighMaskAlignedKey masks (E x) =
      smallHighGraphAlignedKey G e x) (w : Fin h) :
    E (e.symm w).1 = ⟨w.val, by omega⟩ := by
  have hfirst := congrArg Prod.fst (hE (e.symm w).1)
  have hsome :
      (if hi : (E (e.symm w).1).val < h
        then some (⟨(E (e.symm w).1).val, hi⟩ : Fin h)
        else none) = some w := by
    simpa [smallHighMaskAlignedKey, smallHighGraphAlignedKey] using hfirst
  by_cases hi : (E (e.symm w).1).val < h
  · simp [hi] at hsome
    have hval : (E (e.symm w).1).val = w.val :=
      congrArg Fin.val hsome
    apply Fin.ext
    exact hval
  · exfalso
    simp [hi] at hsome

theorem smallHigh_keyAlignedLabeling_degree
    (G : SimpleGraph (Fin 49)) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 (Fin 49) G)
    (hmin : ∀ x : Fin 49, 7 ≤ G.degree x)
    (e : {v // v ∈ orderFortyNineHighVertices G} ≃ Fin h)
    (masks : Array Nat) (E : Equiv.Perm (Fin 49))
    (hE : ∀ x, smallHighMaskAlignedKey masks (E x) =
      smallHighGraphAlignedKey G e x) (i : Fin 49) :
    (orderFortyNineRelabeledGraph G E).degree i =
      if i.val < h then 8 else 7 := by
  rw [orderFortyNineRelabeledGraph_degree]
  have hhigh := smallHigh_keyAlignedLabeling_high_iff
    G e masks E hE (E.symm i)
  simp only [E.apply_symm_apply] at hhigh
  by_cases hi : i.val < h
  · rw [if_pos hi]
    exact (Finset.mem_filter.mp (hhigh.mp hi)).2
  · rw [if_neg hi]
    rcases orderFortyNine_degree_eq_seven_or_eight
      G hfree hmin (Fintype.card_fin 49) (E.symm i) with h7 | h8
    · exact h7
    · exfalso
      exact hi (hhigh.mpr (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h8⟩))

theorem smallHigh_keyAlignedLabeling_supportBit
    (G : SimpleGraph (Fin 49)) [DecidableRel G.Adj]
    (hh : h ≤ 9)
    (e : {v // v ∈ orderFortyNineHighVertices G} ≃ Fin h)
    (masks : Array Nat) (E : Equiv.Perm (Fin 49))
    (hE : ∀ x, smallHighMaskAlignedKey masks (E x) =
      smallHighGraphAlignedKey G e x)
    (i : Fin 49) (w : Fin 9) (hw : w.val < h) :
    decide ((orderFortyNineRelabeledGraph G E).Adj
      i ⟨w.val, by omega⟩) =
      (orderFortyNineSupportMask masks i).getLsbD w.val := by
  let w7 : Fin h := ⟨w.val, hw⟩
  let wi : Fin 49 := ⟨w.val, by omega⟩
  have himage : E (e.symm w7).1 = wi :=
    smallHigh_keyAlignedLabeling_high_image G hh e masks E hE w7
  have hsymm : E.symm wi = (e.symm w7).1 := by
    apply E.injective
    simp [himage]
  have hs := smallHigh_keyAlignedLabeling_support
    G e masks E hE (E.symm i)
  have hs' : smallHighMaskSupport masks i =
      smallHighLabeledSupport G e (E.symm i) := by simpa using hs
  rw [Bool.eq_iff_iff]
  simp only [decide_eq_true_eq]
  change (orderFortyNineRelabeledGraph G E).Adj i wi ↔ _
  rw [orderFortyNineRelabeledGraph_adj, hsymm]
  rw [← mem_smallHighLabeledSupport_iff, ← hs']
  simp [smallHighMaskSupport, w7]

theorem smallHigh_keyAlignedLabeling_lowPartition
    (G : SimpleGraph (Fin 49)) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 (Fin 49) G)
    (hmin : ∀ x : Fin 49, 7 ≤ G.degree x)
    (hh : h ≤ 9)
    (e : {v // v ∈ orderFortyNineHighVertices G} ≃ Fin h)
    (masks : Array Nat) (E : Equiv.Perm (Fin 49))
    (hE : ∀ x, smallHighMaskAlignedKey masks (E x) =
      smallHighGraphAlignedKey G e x)
    (i : Fin 49) (hi : h ≤ i.val) (w : Fin 9) (hw : w.val < h) :
    ((orderFortyNineRelabeledGraph G E).neighborFinset i ∩
      orderFortyNineSupportFiber masks w).card = 1 := by
  let H := orderFortyNineRelabeledGraph G E
  let w7 : Fin h := ⟨w.val, hw⟩
  have hiNot : ¬ i.val < h := by omega
  have hy : G.degree (E.symm i) = 7 := by
    have hd := smallHigh_keyAlignedLabeling_degree
      G hfree hmin e masks E hE i
    rw [orderFortyNineRelabeledGraph_degree, if_neg hiNot] at hd
    exact hd
  obtain ⟨x, hx, huniq⟩ :=
    orderFortyNine_low_neighborhood_partitions_highs
      G hfree hmin (Fintype.card_fin 49) hy (e.symm w7).2
  have hset : H.neighborFinset i ∩ orderFortyNineSupportFiber masks w =
      {E x} := by
    ext k
    constructor
    · intro hk
      have hkN : H.Adj i k := by
        simpa [SimpleGraph.mem_neighborFinset] using (Finset.mem_inter.mp hk).1
      have hkBit :
          (orderFortyNineSupportMask masks k).getLsbD w.val = true := by
        simpa [orderFortyNineSupportFiber] using (Finset.mem_inter.mp hk).2
      have hkHigh := smallHigh_keyAlignedLabeling_supportBit
        G hh e masks E hE k w hw
      have hkAdjHigh : H.Adj k ⟨w.val, by omega⟩ := by
        apply of_decide_eq_true
        rw [hkHigh]
        exact hkBit
      have hhighImage := smallHigh_keyAlignedLabeling_high_image
        G hh e masks E hE w7
      have hhighSymm : E.symm (⟨w.val, by omega⟩ : Fin 49) =
          (e.symm w7).1 := by
        apply E.injective
        simpa using hhighImage.symm
      have hkOrigN : E.symm k ∈ G.neighborFinset (E.symm i) := by
        simpa [H, orderFortyNineRelabeledGraph,
          SimpleGraph.mem_neighborFinset] using hkN
      have hkOrigHigh : G.Adj (E.symm k) (e.symm w7).1 := by
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
      · have hmem : w7 ∈ smallHighLabeledSupport G e x :=
          (mem_smallHighLabeledSupport_iff G e x w7).mpr hx.2
        have hs := smallHigh_keyAlignedLabeling_support G e masks E hE x
        have : w7 ∈ smallHighMaskSupport masks (E x) := by
          rw [hs]
          exact hmem
        simpa [orderFortyNineSupportFiber, smallHighMaskSupport, w7] using this
  rw [hset]
  simp

theorem smallHighAlignedLabeling_of_keyAligned
    (G : SimpleGraph (Fin 49)) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 (Fin 49) G)
    (hmin : ∀ x : Fin 49, 7 ≤ G.degree x)
    (hh : h ≤ 9)
    (e : {v // v ∈ orderFortyNineHighVertices G} ≃ Fin h)
    (masks : Array Nat) (hsize : masks.size = 49)
    (E : Equiv.Perm (Fin 49))
    (hE : ∀ x, smallHighMaskAlignedKey masks (E x) =
      smallHighGraphAlignedKey G e x) :
    SmallHighAlignedLabeling h G E masks := by
  refine ⟨hsize, ?_, ?_, ?_⟩
  · exact smallHigh_keyAlignedLabeling_degree G hfree hmin e masks E hE
  · exact smallHigh_keyAlignedLabeling_supportBit G hh e masks E hE
  · exact smallHigh_keyAlignedLabeling_lowPartition
      G hfree hmin hh e masks E hE

def SmallHighCanonicalFiberCover
    (h blocks : Nat) (masks : Array Nat) : Prop :=
  ∀ (G : SimpleGraph (Fin 49)) (_ : DecidableRel G.Adj)
    (_ : DecidableRel (antipodalGraph G).Adj)
    (_ : DecidableRel (triangleFreeEdgeGraph G).Adj),
    (¬ containsC4 (Fin 49) G) →
    (∀ x : Fin 49, 7 ≤ G.degree x) →
    (orderFortyNineHighVertices G).card = h →
    orderFortyNineHighIncidenceCount G 3 = blocks →
    ∃ e : {v // v ∈ orderFortyNineHighVertices G} ≃ Fin h,
      masks.size = 49 ∧
      ∀ key : Option (Fin h) × Finset (Fin h),
        Fintype.card {x : Fin 49 // smallHighGraphAlignedKey G e x = key} =
        Fintype.card {i : Fin 49 // smallHighMaskAlignedKey masks i = key}

theorem exists_smallHighAlignedLabeling_of_fiberCover
    {h blocks : Nat} (hh : h ≤ 9) (masks : Array Nat)
    (hcover : SmallHighCanonicalFiberCover h blocks masks) :
    ∀ (G : SimpleGraph (Fin 49)) (_ : DecidableRel G.Adj)
      (_ : DecidableRel (antipodalGraph G).Adj)
      (_ : DecidableRel (triangleFreeEdgeGraph G).Adj),
      (¬ containsC4 (Fin 49) G) →
      (∀ x : Fin 49, 7 ≤ G.degree x) →
      (orderFortyNineHighVertices G).card = h →
      orderFortyNineHighIncidenceCount G 3 = blocks →
      ∃ E : Equiv.Perm (Fin 49), SmallHighAlignedLabeling h G E masks := by
  intro G _ _ _ hfree hmin hhigh hblocks
  obtain ⟨e, hsize, hfibers⟩ :=
    hcover G inferInstance inferInstance inferInstance
      hfree hmin hhigh hblocks
  obtain ⟨E, hE⟩ := exists_smallHigh_keyAlignedLabeling_of_fiberCardEq
    G e masks hfibers
  exact ⟨E, smallHighAlignedLabeling_of_keyAligned
    G hfree hmin hh e masks hsize E hE⟩

def ThreeHighCanonicalFiberCover (blocks : Nat) : Prop :=
  SmallHighCanonicalFiberCover 3 blocks (threeHighRepresentativeMasks blocks)

def FiveHighCanonicalFiberCover (blocks : Nat) : Prop :=
  SmallHighCanonicalFiberCover 5 blocks (fiveHighRepresentativeMasks blocks)

theorem threeHighCanonicalLabelingCover_of_fiberCover
    {blocks : Nat} (hcover : ThreeHighCanonicalFiberCover blocks) :
    ThreeHighCanonicalLabelingCover blocks := by
  exact exists_smallHighAlignedLabeling_of_fiberCover
    (h := 3) (by omega) (threeHighRepresentativeMasks blocks) hcover

theorem fiveHighCanonicalLabelingCover_of_fiberCover
    {blocks : Nat} (hcover : FiveHighCanonicalFiberCover blocks) :
    FiveHighCanonicalLabelingCover blocks := by
  exact exists_smallHighAlignedLabeling_of_fiberCover
    (h := 5) (by omega) (fiveHighRepresentativeMasks blocks) hcover


end

end Erdos85
