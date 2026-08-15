import Proofs.Erdos85OrderFortyNineSevenHighLabelingBridge

/-!
# Fiber construction for seven-high canonical labelings

An exact high label together with the labeled high-support set is a complete
vertex key.  Equality of all graph-side and mask-side key-fiber cardinalities
therefore constructs the required permutation of all 49 vertices.
-/

namespace Erdos85

open SimpleGraph

noncomputable section

def sevenHighLabeledSupport
    (G : SimpleGraph (Fin 49)) [DecidableRel G.Adj]
    (e : {v // v ∈ orderFortyNineHighVertices G} ≃ Fin 7)
    (x : Fin 49) : Finset (Fin 7) :=
  (finsetInSubtype (orderFortyNineHighVertices G)
    (orderFortyNineHighSupport G x)).map e.toEmbedding

theorem sevenHighLabeledSupport_card
    (G : SimpleGraph (Fin 49)) [DecidableRel G.Adj]
    (e : {v // v ∈ orderFortyNineHighVertices G} ≃ Fin 7)
    (x : Fin 49) :
    (sevenHighLabeledSupport G e x).card =
      (orderFortyNineHighSupport G x).card := by
  simp only [sevenHighLabeledSupport, Finset.card_map]
  apply card_finsetInSubtype_of_subset
  intro v hv
  exact (Finset.mem_inter.mp hv).2

theorem mem_sevenHighLabeledSupport_iff
    (G : SimpleGraph (Fin 49)) [DecidableRel G.Adj]
    (e : {v // v ∈ orderFortyNineHighVertices G} ≃ Fin 7)
    (x : Fin 49) (w : Fin 7) :
    w ∈ sevenHighLabeledSupport G e x ↔ G.Adj x (e.symm w).1 := by
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

def sevenHighMaskSupport (masks : Array Nat) (i : Fin 49) :
    Finset (Fin 7) :=
  Finset.univ.filter fun w =>
    (orderFortyNineSupportMask masks i).getLsbD w.val

def sevenHighGraphAlignedKey
    (G : SimpleGraph (Fin 49)) [DecidableRel G.Adj]
    (e : {v // v ∈ orderFortyNineHighVertices G} ≃ Fin 7)
    (x : Fin 49) : Option (Fin 7) × Finset (Fin 7) :=
  (if hx : x ∈ orderFortyNineHighVertices G then some (e ⟨x, hx⟩) else none,
    sevenHighLabeledSupport G e x)

def sevenHighMaskAlignedKey (masks : Array Nat) (i : Fin 49) :
    Option (Fin 7) × Finset (Fin 7) :=
  (if hi : i.val < 7 then some ⟨i.val, hi⟩ else none,
    sevenHighMaskSupport masks i)

theorem exists_sevenHigh_keyAlignedLabeling_of_fiberCardEq
    (G : SimpleGraph (Fin 49)) [DecidableRel G.Adj]
    (e : {v // v ∈ orderFortyNineHighVertices G} ≃ Fin 7)
    (masks : Array Nat)
    (hcard : ∀ key : Option (Fin 7) × Finset (Fin 7),
      Fintype.card {x : Fin 49 // sevenHighGraphAlignedKey G e x = key} =
      Fintype.card {i : Fin 49 // sevenHighMaskAlignedKey masks i = key}) :
    ∃ E : Equiv.Perm (Fin 49), ∀ x,
      sevenHighMaskAlignedKey masks (E x) =
        sevenHighGraphAlignedKey G e x := by
  let E := equivOfFiberCardEq
    (sevenHighGraphAlignedKey G e) (sevenHighMaskAlignedKey masks) hcard
  exact ⟨E, fun x => equivOfFiberCardEq_map _ _ hcard x⟩

theorem sevenHigh_keyAlignedLabeling_support
    (G : SimpleGraph (Fin 49)) [DecidableRel G.Adj]
    (e : {v // v ∈ orderFortyNineHighVertices G} ≃ Fin 7)
    (masks : Array Nat) (E : Equiv.Perm (Fin 49))
    (hE : ∀ x, sevenHighMaskAlignedKey masks (E x) =
      sevenHighGraphAlignedKey G e x) (x : Fin 49) :
    sevenHighMaskSupport masks (E x) = sevenHighLabeledSupport G e x := by
  exact congrArg Prod.snd (hE x)

theorem sevenHigh_keyAlignedLabeling_high_iff
    (G : SimpleGraph (Fin 49)) [DecidableRel G.Adj]
    (e : {v // v ∈ orderFortyNineHighVertices G} ≃ Fin 7)
    (masks : Array Nat) (E : Equiv.Perm (Fin 49))
    (hE : ∀ x, sevenHighMaskAlignedKey masks (E x) =
      sevenHighGraphAlignedKey G e x) (x : Fin 49) :
    (E x).val < 7 ↔ x ∈ orderFortyNineHighVertices G := by
  have hfirst := congrArg Prod.fst (hE x)
  by_cases hi : (E x).val < 7 <;>
    by_cases hx : x ∈ orderFortyNineHighVertices G <;>
    simp [sevenHighMaskAlignedKey, sevenHighGraphAlignedKey, hi, hx] at hfirst ⊢

theorem sevenHigh_keyAlignedLabeling_high_image
    (G : SimpleGraph (Fin 49)) [DecidableRel G.Adj]
    (e : {v // v ∈ orderFortyNineHighVertices G} ≃ Fin 7)
    (masks : Array Nat) (E : Equiv.Perm (Fin 49))
    (hE : ∀ x, sevenHighMaskAlignedKey masks (E x) =
      sevenHighGraphAlignedKey G e x) (w : Fin 7) :
    E (e.symm w).1 = ⟨w.val, by omega⟩ := by
  have hfirst := congrArg Prod.fst (hE (e.symm w).1)
  have hsome :
      (if hi : (E (e.symm w).1).val < 7
        then some (⟨(E (e.symm w).1).val, hi⟩ : Fin 7)
        else none) = some w := by
    simpa [sevenHighMaskAlignedKey, sevenHighGraphAlignedKey] using hfirst
  by_cases hi : (E (e.symm w).1).val < 7
  · simp [hi] at hsome
    have hval : (E (e.symm w).1).val = w.val :=
      congrArg Fin.val hsome
    apply Fin.ext
    exact hval
  · exfalso
    simp [hi] at hsome

theorem sevenHigh_keyAlignedLabeling_degree
    (G : SimpleGraph (Fin 49)) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 (Fin 49) G)
    (hmin : ∀ x : Fin 49, 7 ≤ G.degree x)
    (e : {v // v ∈ orderFortyNineHighVertices G} ≃ Fin 7)
    (masks : Array Nat) (E : Equiv.Perm (Fin 49))
    (hE : ∀ x, sevenHighMaskAlignedKey masks (E x) =
      sevenHighGraphAlignedKey G e x) (i : Fin 49) :
    (orderFortyNineRelabeledGraph G E).degree i =
      if i.val < 7 then 8 else 7 := by
  rw [orderFortyNineRelabeledGraph_degree]
  have hhigh := sevenHigh_keyAlignedLabeling_high_iff
    G e masks E hE (E.symm i)
  simp only [E.apply_symm_apply] at hhigh
  by_cases hi : i.val < 7
  · rw [if_pos hi]
    exact (Finset.mem_filter.mp (hhigh.mp hi)).2
  · rw [if_neg hi]
    rcases orderFortyNine_degree_eq_seven_or_eight
      G hfree hmin (Fintype.card_fin 49) (E.symm i) with h7 | h8
    · exact h7
    · exfalso
      exact hi (hhigh.mpr (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h8⟩))

theorem sevenHigh_keyAlignedLabeling_supportBit
    (G : SimpleGraph (Fin 49)) [DecidableRel G.Adj]
    (e : {v // v ∈ orderFortyNineHighVertices G} ≃ Fin 7)
    (masks : Array Nat) (E : Equiv.Perm (Fin 49))
    (hE : ∀ x, sevenHighMaskAlignedKey masks (E x) =
      sevenHighGraphAlignedKey G e x)
    (i : Fin 49) (w : Fin 9) (hw : w.val < 7) :
    decide ((orderFortyNineRelabeledGraph G E).Adj
      i ⟨w.val, by omega⟩) =
      (orderFortyNineSupportMask masks i).getLsbD w.val := by
  let w7 : Fin 7 := ⟨w.val, hw⟩
  let wi : Fin 49 := ⟨w.val, by omega⟩
  have himage : E (e.symm w7).1 = wi :=
    sevenHigh_keyAlignedLabeling_high_image G e masks E hE w7
  have hsymm : E.symm wi = (e.symm w7).1 := by
    apply E.injective
    simp [himage]
  have hs := sevenHigh_keyAlignedLabeling_support
    G e masks E hE (E.symm i)
  have hs' : sevenHighMaskSupport masks i =
      sevenHighLabeledSupport G e (E.symm i) := by simpa using hs
  rw [Bool.eq_iff_iff]
  simp only [decide_eq_true_eq]
  change (orderFortyNineRelabeledGraph G E).Adj i wi ↔ _
  rw [orderFortyNineRelabeledGraph_adj, hsymm]
  rw [← mem_sevenHighLabeledSupport_iff, ← hs']
  simp [sevenHighMaskSupport, w7]

theorem sevenHigh_keyAlignedLabeling_lowPartition
    (G : SimpleGraph (Fin 49)) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 (Fin 49) G)
    (hmin : ∀ x : Fin 49, 7 ≤ G.degree x)
    (e : {v // v ∈ orderFortyNineHighVertices G} ≃ Fin 7)
    (masks : Array Nat) (E : Equiv.Perm (Fin 49))
    (hE : ∀ x, sevenHighMaskAlignedKey masks (E x) =
      sevenHighGraphAlignedKey G e x)
    (i : Fin 49) (hi : 7 ≤ i.val) (w : Fin 9) (hw : w.val < 7) :
    ((orderFortyNineRelabeledGraph G E).neighborFinset i ∩
      orderFortyNineSupportFiber masks w).card = 1 := by
  let H := orderFortyNineRelabeledGraph G E
  let w7 : Fin 7 := ⟨w.val, hw⟩
  have hiNot : ¬ i.val < 7 := by omega
  have hy : G.degree (E.symm i) = 7 := by
    have hd := sevenHigh_keyAlignedLabeling_degree
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
      have hkHigh := sevenHigh_keyAlignedLabeling_supportBit
        G e masks E hE k w hw
      have hkAdjHigh : H.Adj k ⟨w.val, by omega⟩ := by
        apply of_decide_eq_true
        rw [hkHigh]
        exact hkBit
      have hhighImage := sevenHigh_keyAlignedLabeling_high_image
        G e masks E hE w7
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
      · have hmem : w7 ∈ sevenHighLabeledSupport G e x :=
          (mem_sevenHighLabeledSupport_iff G e x w7).mpr hx.2
        have hs := sevenHigh_keyAlignedLabeling_support G e masks E hE x
        have : w7 ∈ sevenHighMaskSupport masks (E x) := by
          rw [hs]
          exact hmem
        simpa [orderFortyNineSupportFiber, sevenHighMaskSupport, w7] using this
  rw [hset]
  simp

theorem sevenHighAlignedLabeling_of_keyAligned
    (G : SimpleGraph (Fin 49)) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 (Fin 49) G)
    (hmin : ∀ x : Fin 49, 7 ≤ G.degree x)
    (e : {v // v ∈ orderFortyNineHighVertices G} ≃ Fin 7)
    (masks : Array Nat) (hsize : masks.size = 49)
    (E : Equiv.Perm (Fin 49))
    (hE : ∀ x, sevenHighMaskAlignedKey masks (E x) =
      sevenHighGraphAlignedKey G e x) :
    SevenHighAlignedLabeling G E masks := by
  refine ⟨hsize, ?_, ?_, ?_⟩
  · exact sevenHigh_keyAlignedLabeling_degree G hfree hmin e masks E hE
  · exact sevenHigh_keyAlignedLabeling_supportBit G e masks E hE
  · exact sevenHigh_keyAlignedLabeling_lowPartition
      G hfree hmin e masks E hE

def SevenHighCanonicalFiberCover (blocks : Nat) : Prop :=
  ∀ (G : SimpleGraph (Fin 49)) (_ : DecidableRel G.Adj)
    (_ : DecidableRel (antipodalGraph G).Adj)
    (_ : DecidableRel (triangleFreeEdgeGraph G).Adj),
    (¬ containsC4 (Fin 49) G) →
    (∀ x : Fin 49, 7 ≤ G.degree x) →
    (orderFortyNineHighVertices G).card = 7 →
    orderFortyNineHighIncidenceCount G 3 = blocks →
    ∃ index, index < (OrderFortyNineSevenHighCensus.reps blocks).length ∧
      ∃ e : {v // v ∈ orderFortyNineHighVertices G} ≃ Fin 7,
      let masks := OrderFortyNineSevenHighCensus.representativeMasks blocks index
      masks.size = 49 ∧
      ∀ key : Option (Fin 7) × Finset (Fin 7),
        Fintype.card {x : Fin 49 // sevenHighGraphAlignedKey G e x = key} =
        Fintype.card {i : Fin 49 // sevenHighMaskAlignedKey masks i = key}

/-- The entire graph-normalization obligation is reduced to equality of the
finite aligned-key fiber cardinalities. -/
theorem sevenHighCanonicalLabelingCover_of_fiberCover
    {blocks : Nat} (hcover : SevenHighCanonicalFiberCover blocks) :
    SevenHighCanonicalLabelingCover blocks := by
  intro G _ _ _ hfree hmin hhigh hblocks
  obtain ⟨index, hindex, e, hsize, hfibers⟩ :=
    hcover G inferInstance inferInstance inferInstance
      hfree hmin hhigh hblocks
  obtain ⟨E, hE⟩ := exists_sevenHigh_keyAlignedLabeling_of_fiberCardEq
    G e (OrderFortyNineSevenHighCensus.representativeMasks blocks index)
      hfibers
  refine ⟨index, hindex, E, ?_⟩
  exact sevenHighAlignedLabeling_of_keyAligned
    G hfree hmin e
      (OrderFortyNineSevenHighCensus.representativeMasks blocks index)
      hsize E hE

end

end Erdos85
