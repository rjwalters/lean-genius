import Proofs.Erdos85OrderFortyNineThreeHighZeroFiber

/-!
# Fiber census for the one-block three-high triple system

When `t=1`, the unique size-three high support can be sent to `012`.
This file begins the corresponding exact aligned-fiber normalization.
-/

namespace Erdos85

open SimpleGraph

noncomputable section

theorem threeHigh_t1_global_incidence
    (G : SimpleGraph (Fin 49)) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 (Fin 49) G)
    (hmin : ∀ x : Fin 49, 7 ≤ G.degree x)
    (hHigh : (orderFortyNineHighVertices G).card = 3)
    (hone : orderFortyNineHighIncidenceCount G 3 = 1) :
    orderFortyNineHighIncidenceCount G 0 = 24 ∧
    orderFortyNineHighIncidenceCount G 1 = 21 ∧
    orderFortyNineHighIncidenceCount G 2 = 0 := by
  have hp := orderFortyNine_highIncidence_profile_of_three_high
    G hfree hmin (Fintype.card_fin 49) hHigh
  dsimp only at hp
  omega

theorem threeHigh_t1_exists_unique_triple_support
    (G : SimpleGraph (Fin 49)) [DecidableRel G.Adj]
    (hone : orderFortyNineHighIncidenceCount G 3 = 1) :
    ∃! x : Fin 49, x ∈ orderFortyNineLowVertices G ∧
      (orderFortyNineHighSupport G x).card = 3 := by
  let T := (orderFortyNineLowVertices G).filter fun x =>
    (orderFortyNineHighSupport G x).card = 3
  have hT : T.card = 1 := by exact hone
  obtain ⟨x, hx⟩ := Finset.card_eq_one.mp hT
  refine ⟨x, ?_, ?_⟩
  · have : x ∈ T := by simp [hx]
    exact Finset.mem_filter.mp this
  · intro y hy
    have hyT : y ∈ T := Finset.mem_filter.mpr hy
    simpa [hx] using hyT

theorem threeHigh_t1_exists_normalized_labeling
    (G : SimpleGraph (Fin 49)) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 (Fin 49) G)
    (hmin : ∀ x : Fin 49, 7 ≤ G.degree x)
    (hHigh : (orderFortyNineHighVertices G).card = 3)
    (hone : orderFortyNineHighIncidenceCount G 3 = 1) :
    ∃ e : {v // v ∈ orderFortyNineHighVertices G} ≃ Fin 3,
      ∃ x : Fin 49,
        smallHighLabeledSupport G e x = {0, 1, 2} ∧
        ∀ y : Fin 49, (smallHighLabeledSupport G e y).card = 3 → y = x := by
  let e0 : {v // v ∈ orderFortyNineHighVertices G} ≃ Fin 3 :=
    Fintype.equivFinOfCardEq (by simpa using hHigh)
  obtain ⟨x, hx, huniq⟩ := threeHigh_t1_exists_unique_triple_support G hone
  have hx3 : (smallHighLabeledSupport G e0 x).card = 3 := by
    rw [smallHighLabeledSupport_card]
    exact hx.2
  obtain ⟨a, b, c, hab, hac, hbc, hsupport⟩ :=
    Finset.card_eq_three.mp hx3
  let f : Fin 3 → Fin 3 := ![a, b, c]
  have hf : Function.Injective f := by
    intro i j
    fin_cases i <;> fin_cases j <;> simp [f, hab, hac, hbc, Ne.symm hab,
      Ne.symm hac, Ne.symm hbc]
  obtain ⟨σ, hσ⟩ := Equiv.Perm.exists_extending_pair f
    (Fin.castLE (by omega : 3 ≤ 3)) hf
    (Fin.castLE_injective (by omega : 3 ≤ 3))
  let e := e0.trans σ
  refine ⟨e, x, ?_, ?_⟩
  · have hmap : smallHighLabeledSupport G e x =
        (smallHighLabeledSupport G e0 x).map σ.toEmbedding := by
      simp [smallHighLabeledSupport, e, Finset.map_map]
    rw [hmap, hsupport]
    ext w
    have h0 := hσ (0 : Fin 3)
    have h1 := hσ (1 : Fin 3)
    have h2 := hσ (2 : Fin 3)
    fin_cases w <;> simp_all [f]
  · intro y hy3
    apply huniq y
    refine ⟨?_, ?_⟩
    · apply Finset.mem_sdiff.mpr
      refine ⟨Finset.mem_univ y, ?_⟩
      intro hyHigh
      have hz := orderFortyNine_highNeighborCount_eq_zero_of_high
        G hfree hmin (Fintype.card_fin 49) hyHigh
      have hy0 : (smallHighLabeledSupport G e y).card = 0 := by
        rw [smallHighLabeledSupport_card]
        exact hz
      omega
    · rw [← smallHighLabeledSupport_card G e y]
      exact hy3

theorem threeHigh_singleton_fiber_card_eq_local
    (G : SimpleGraph (Fin 49)) [DecidableRel G.Adj]
    (e : {v // v ∈ orderFortyNineHighVertices G} ≃ Fin 3)
    (w : Fin 3) :
    Fintype.card {x : Fin 49 // smallHighLabeledSupport G e x = {w}} =
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
    · have hw : w ∈ smallHighLabeledSupport G e x := by simp [hs]
      simpa [SimpleGraph.mem_neighborFinset, G.adj_comm] using
        (mem_smallHighLabeledSupport_iff G e x w).mp hw
    · rw [← smallHighLabeledSupport_card G e x, hs]
      simp
  · intro hx
    have hxN := (Finset.mem_filter.mp hx).1
    have hxCard := (Finset.mem_filter.mp hx).2
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ x, ?_⟩
    have hw : w ∈ smallHighLabeledSupport G e x := by
      apply (mem_smallHighLabeledSupport_iff G e x w).mpr
      simpa [SimpleGraph.mem_neighborFinset, G.adj_comm] using hxN
    have hcard : (smallHighLabeledSupport G e x).card = 1 := by
      rw [smallHighLabeledSupport_card]
      exact hxCard
    obtain ⟨z, hz⟩ := Finset.card_eq_one.mp hcard
    have hwz : w = z := by simpa [hz] using hw
    simpa [hz, hwz]

theorem threeHigh_t1_local_triple_card
    (G : SimpleGraph (Fin 49)) [DecidableRel G.Adj]
    (e : {v // v ∈ orderFortyNineHighVertices G} ≃ Fin 3)
    (x : Fin 49)
    (hxSupport : smallHighLabeledSupport G e x = {0, 1, 2})
    (huniq : ∀ y : Fin 49,
      (smallHighLabeledSupport G e y).card = 3 → y = x)
    (w : Fin 3) :
    ((G.neighborFinset (e.symm w).1).filter fun y =>
      (orderFortyNineHighSupport G y).card = 3).card =
      if w ∈ ({0, 1, 2} : Finset (Fin 3)) then 1 else 0 := by
  by_cases hw : w ∈ ({0, 1, 2} : Finset (Fin 3))
  · rw [if_pos hw]
    have hset : ((G.neighborFinset (e.symm w).1).filter fun y =>
        (orderFortyNineHighSupport G y).card = 3) = {x} := by
      ext y
      constructor
      · intro hy
        have hy3 : (smallHighLabeledSupport G e y).card = 3 := by
          rw [smallHighLabeledSupport_card]
          exact (Finset.mem_filter.mp hy).2
        simp [huniq y hy3]
      · intro hy
        have hyx : y = x := by simpa using hy
        subst y
        apply Finset.mem_filter.mpr
        constructor
        · simpa [SimpleGraph.mem_neighborFinset, G.adj_comm] using
            (mem_smallHighLabeledSupport_iff G e x w).mp
              (by simpa [hxSupport] using hw)
        · rw [← smallHighLabeledSupport_card G e x, hxSupport]
          decide
    rw [hset]
    simp
  · rw [if_neg hw, Finset.card_eq_zero]
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro y hy
    have hy3 : (smallHighLabeledSupport G e y).card = 3 := by
      rw [smallHighLabeledSupport_card]
      exact (Finset.mem_filter.mp hy).2
    have hyx := huniq y hy3
    have hwMem : w ∈ smallHighLabeledSupport G e y :=
      (mem_smallHighLabeledSupport_iff G e y w).mpr (by
        simpa [SimpleGraph.mem_neighborFinset, G.adj_comm] using
          (Finset.mem_filter.mp hy).1)
    rw [hyx, hxSupport] at hwMem
    exact hw hwMem

theorem threeHigh_t1_singleton_fiber_card
    (G : SimpleGraph (Fin 49)) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 (Fin 49) G)
    (hmin : ∀ x : Fin 49, 7 ≤ G.degree x)
    (hHigh : (orderFortyNineHighVertices G).card = 3)
    (e : {v // v ∈ orderFortyNineHighVertices G} ≃ Fin 3)
    (x : Fin 49)
    (hxSupport : smallHighLabeledSupport G e x = {0, 1, 2})
    (huniq : ∀ y : Fin 49,
      (smallHighLabeledSupport G e y).card = 3 → y = x)
    (w : Fin 3) :
    Fintype.card {y : Fin 49 // smallHighLabeledSupport G e y = {w}} =
      if w ∈ ({0, 1, 2} : Finset (Fin 3)) then 7 else 6 := by
  rw [threeHigh_singleton_fiber_card_eq_local G e w]
  have hp := orderFortyNine_highNeighborhood_general_profile
    G hfree hmin (Fintype.card_fin 49)
      (Finset.mem_filter.mp (e.symm w).2).2
  dsimp only at hp
  rw [hHigh] at hp
  rw [threeHigh_t1_local_triple_card G e x hxSupport huniq w] at hp
  by_cases hw : w ∈ ({0, 1, 2} : Finset (Fin 3)) <;>
    simp [hw] at hp ⊢ <;> omega

theorem threeHigh_existsUnique_labeled_pairBlock
    (G : SimpleGraph (Fin 49)) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 (Fin 49) G)
    (hmin : ∀ x : Fin 49, 7 ≤ G.degree x)
    (e : {v // v ∈ orderFortyNineHighVertices G} ≃ Fin 3)
    {a b : Fin 3} (hab : a ≠ b) :
    ∃! x : Fin 49, ({a, b} : Finset (Fin 3)) ⊆
        smallHighLabeledSupport G e x ∧
      ((smallHighLabeledSupport G e x).card = 2 ∨
       (smallHighLabeledSupport G e x).card = 3) := by
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
        exact (mem_smallHighLabeledSupport_iff G e x _).mpr hx.1.symm
      · rw [hw]
        exact (mem_smallHighLabeledSupport_iff G e x _).mpr hx.2.1.symm
    · simpa [smallHighLabeledSupport_card] using hx.2.2.2
  · intro y hy
    apply huniq y
    have ha := hy.1 (by simp : a ∈ ({a, b} : Finset (Fin 3)))
    have hb := hy.1 (by simp : b ∈ ({a, b} : Finset (Fin 3)))
    refine ⟨?_, ?_, ?_, ?_⟩
    · simpa [G.adj_comm] using
        (mem_smallHighLabeledSupport_iff G e y a).mp ha
    · simpa [G.adj_comm] using
        (mem_smallHighLabeledSupport_iff G e y b).mp hb
    · exact orderFortyNine_neighbor_degree_seven_of_degreeEight
        G hfree hmin (Fintype.card_fin 49)
          (Finset.mem_filter.mp (e.symm a).2).2 (by
            simpa [G.adj_comm] using
              (mem_smallHighLabeledSupport_iff G e y a).mp ha)
    · simpa [smallHighLabeledSupport_card] using hy.2

theorem threeHigh_t1_pair_fiber_card
    (G : SimpleGraph (Fin 49)) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 (Fin 49) G)
    (hmin : ∀ x : Fin 49, 7 ≤ G.degree x)
    (e : {v // v ∈ orderFortyNineHighVertices G} ≃ Fin 3)
    (x : Fin 49)
    (hxSupport : smallHighLabeledSupport G e x = {0, 1, 2})
    (huniqTriple : ∀ y : Fin 49,
      (smallHighLabeledSupport G e y).card = 3 → y = x)
    (a b : Fin 3) (hab : a ≠ b) :
    Fintype.card {y : Fin 49 // smallHighLabeledSupport G e y = {a, b}} =
      if ({a, b} : Finset (Fin 3)) ⊆ {0, 1, 2} then 0 else 1 := by
  obtain ⟨z, hz, hzuniq⟩ :=
    threeHigh_existsUnique_labeled_pairBlock G hfree hmin e hab
  by_cases hcovered : ({a, b} : Finset (Fin 3)) ⊆ {0, 1, 2}
  · rw [if_pos hcovered, Fintype.card_subtype, Finset.card_eq_zero]
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro y hy
    have hyEq := (Finset.mem_filter.mp hy).2
    have hyQual : ({a, b} : Finset (Fin 3)) ⊆
        smallHighLabeledSupport G e y ∧
        ((smallHighLabeledSupport G e y).card = 2 ∨
         (smallHighLabeledSupport G e y).card = 3) := by
      refine ⟨by rw [hyEq], Or.inl ?_⟩
      rw [hyEq]
      simp [hab]
    have hxQual : ({a, b} : Finset (Fin 3)) ⊆
        smallHighLabeledSupport G e x ∧
        ((smallHighLabeledSupport G e x).card = 2 ∨
         (smallHighLabeledSupport G e x).card = 3) := by
      refine ⟨by simpa [hxSupport] using hcovered, Or.inr ?_⟩
      rw [hxSupport]
      decide
    have hyx : y = x := (hzuniq y hyQual).trans (hzuniq x hxQual).symm
    have := congrArg (fun u => (smallHighLabeledSupport G e u).card) hyx
    rw [hyEq, hxSupport] at this
    simp [hab] at this
  · rw [if_neg hcovered]
    have hz2 : (smallHighLabeledSupport G e z).card = 2 := by
      rcases hz.2 with hz2 | hz3
      · exact hz2
      · have hzx := huniqTriple z hz3
        have : ({a, b} : Finset (Fin 3)) ⊆ {0, 1, 2} := by
          simpa [hzx, hxSupport] using hz.1
        exact False.elim (hcovered this)
    have hzEq : smallHighLabeledSupport G e z = {a, b} :=
      (Finset.eq_of_subset_of_card_le hz.1 (by simp [hab, hz2])).symm
    have hone := smallHighLabeledSupport_fiber_card_eq_one
      G hfree e z (by omega)
    simpa [hzEq] using hone

theorem threeHigh_aligned_emptyLow_fiber_card
    (G : SimpleGraph (Fin 49)) [DecidableRel G.Adj]
    (e : {v // v ∈ orderFortyNineHighVertices G} ≃ Fin 3) :
    Fintype.card {x : Fin 49 //
      smallHighGraphAlignedKey G e x = (none, ∅)} =
      orderFortyNineHighIncidenceCount G 0 := by
  rw [Fintype.card_subtype]
  have hset : (Finset.univ.filter fun x : Fin 49 =>
      smallHighGraphAlignedKey G e x = (none, ∅)) =
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
        simp [smallHighGraphAlignedKey, hxHigh] at hfirst
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_sdiff.mpr ⟨Finset.mem_univ x, hxNotHigh⟩, ?_⟩
      have : smallHighLabeledSupport G e x = ∅ := by
        simpa [smallHighGraphAlignedKey] using hsupp
      rw [← smallHighLabeledSupport_card G e x, this]
      simp
    · intro hx
      have hxLow := (Finset.mem_filter.mp hx).1
      have hx0 := (Finset.mem_filter.mp hx).2
      have hxNotHigh := (Finset.mem_sdiff.mp hxLow).2
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ x, ?_⟩
      have hs : smallHighLabeledSupport G e x = ∅ :=
        Finset.card_eq_zero.mp (by
          rw [smallHighLabeledSupport_card]
          exact hx0)
      simp [smallHighGraphAlignedKey, hxNotHigh, hs]
  rw [hset]
  rfl

theorem threeHigh_t1_triple_fiber_card
    (G : SimpleGraph (Fin 49)) [DecidableRel G.Adj]
    (e : {v // v ∈ orderFortyNineHighVertices G} ≃ Fin 3)
    (x : Fin 49)
    (hxSupport : smallHighLabeledSupport G e x = {0, 1, 2})
    (huniq : ∀ y : Fin 49,
      (smallHighLabeledSupport G e y).card = 3 → y = x)
    (S : Finset (Fin 3)) (hS3 : S.card = 3) :
    Fintype.card {y : Fin 49 // smallHighLabeledSupport G e y = S} =
      if S = {0, 1, 2} then 1 else 0 := by
  by_cases hS : S = {0, 1, 2}
  · subst S
    rw [if_pos rfl, Fintype.card_subtype]
    have hset : (Finset.univ.filter fun y : Fin 49 =>
        smallHighLabeledSupport G e y = {0, 1, 2}) = {x} := by
      ext y
      constructor
      · intro hy
        have hyEq := (Finset.mem_filter.mp hy).2
        have hy3 : (smallHighLabeledSupport G e y).card = 3 := by
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
    have hy3 : (smallHighLabeledSupport G e y).card = 3 := by rw [hyEq]; exact hS3
    have hyx := huniq y hy3
    apply hS
    rw [← hyEq, hyx, hxSupport]

theorem threeHigh_t1_alignedLow_other_fiber_card_eq_zero
    (G : SimpleGraph (Fin 49)) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 (Fin 49) G)
    (hmin : ∀ x : Fin 49, 7 ≤ G.degree x)
    (e : {v // v ∈ orderFortyNineHighVertices G} ≃ Fin 3)
    (x : Fin 49)
    (hxSupport : smallHighLabeledSupport G e x = {0, 1, 2})
    (huniq : ∀ y : Fin 49,
      (smallHighLabeledSupport G e y).card = 3 → y = x)
    (S : Finset (Fin 3))
    (h0 : S.card ≠ 0) (h1 : S.card ≠ 1) (h2 : S.card ≠ 2)
    (hcanonical : S ≠ {0, 1, 2}) :
    Fintype.card {y : Fin 49 //
      smallHighGraphAlignedKey G e y = (none, S)} = 0 := by
  rw [Fintype.card_subtype, Finset.card_eq_zero]
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro y hy
  have hkey := (Finset.mem_filter.mp hy).2
  have hfirst := congrArg Prod.fst hkey
  have hsupp : smallHighLabeledSupport G e y = S := by
    simpa [smallHighGraphAlignedKey] using congrArg Prod.snd hkey
  have hyNotHigh : y ∉ orderFortyNineHighVertices G := by
    intro hyHigh
    simp [smallHighGraphAlignedKey, hyHigh] at hfirst
  have hy7 : G.degree y = 7 := by
    rcases orderFortyNine_degree_eq_seven_or_eight
      G hfree hmin (Fintype.card_fin 49) y with hy7 | hy8
    · exact hy7
    · exact False.elim (hyNotHigh
        (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hy8⟩))
  have hle : S.card ≤ 3 := by
    rw [← hsupp, smallHighLabeledSupport_card]
    simpa [orderFortyNineHighSupport] using
      orderFortyNine_highNeighborCount_le_three
        G hfree hmin (Fintype.card_fin 49) hy7
  have hS3 : S.card = 3 := by omega
  have hy3 : (smallHighLabeledSupport G e y).card = 3 := by
    rw [hsupp]
    exact hS3
  have hyx := huniq y hy3
  apply hcanonical
  rw [← hsupp, hyx, hxSupport]

def threeHighT1KeyMultiplicity
    (key : Option (Fin 3) × Finset (Fin 3)) : Nat :=
  match key.1 with
  | some _ => if key.2 = ∅ then 1 else 0
  | none =>
      if key.2.card = 0 then 24
      else if key.2.card = 1 then
        if key.2 ⊆ ({0, 1, 2} : Finset (Fin 3)) then 7 else 6
      else if key.2.card = 2 then
        if key.2 ⊆ ({0, 1, 2} : Finset (Fin 3)) then 0 else 1
      else if key.2 = ({0, 1, 2} : Finset (Fin 3)) then 1 else 0

theorem threeHigh_t1_graph_key_fiber_card
    (G : SimpleGraph (Fin 49)) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 (Fin 49) G)
    (hmin : ∀ x : Fin 49, 7 ≤ G.degree x)
    (hHigh : (orderFortyNineHighVertices G).card = 3)
    (hone : orderFortyNineHighIncidenceCount G 3 = 1)
    (e : {v // v ∈ orderFortyNineHighVertices G} ≃ Fin 3)
    (x : Fin 49)
    (hxSupport : smallHighLabeledSupport G e x = {0, 1, 2})
    (huniq : ∀ y : Fin 49,
      (smallHighLabeledSupport G e y).card = 3 → y = x)
    (key : Option (Fin 3) × Finset (Fin 3)) :
    Fintype.card {y : Fin 49 // smallHighGraphAlignedKey G e y = key} =
      threeHighT1KeyMultiplicity key := by
  rcases key with ⟨label, S⟩
  cases label with
  | some w =>
      by_cases hS0 : S = ∅
      · subst S
        simpa [threeHighT1KeyMultiplicity] using
          threeHigh_alignedHigh_fiber_card_eq_one G hfree hmin e w
      · have hSne : S.Nonempty := Finset.nonempty_iff_ne_empty.mpr hS0
        simpa [threeHighT1KeyMultiplicity, hS0] using
          threeHigh_alignedHigh_nonemptySupport_fiber_card_eq_zero
            G hfree hmin e w S hSne
  | none =>
      by_cases h0 : S.card = 0
      · have hS0 : S = ∅ := Finset.card_eq_zero.mp h0
        subst S
        have hn0 := (threeHigh_t1_global_incidence
          G hfree hmin hHigh hone).1
        simpa [threeHighT1KeyMultiplicity, hn0] using
          threeHigh_aligned_emptyLow_fiber_card G e
      · by_cases h1 : S.card = 1
        · obtain ⟨w, rfl⟩ := Finset.card_eq_one.mp h1
          rw [threeHigh_nonempty_alignedLowFiber_card G hfree hmin e {w}
            (by simp)]
          have hs := threeHigh_t1_singleton_fiber_card
            G hfree hmin hHigh e x hxSupport huniq w
          simpa [threeHighT1KeyMultiplicity] using hs
        · by_cases h2 : S.card = 2
          · obtain ⟨a, b, hab, rfl⟩ := Finset.card_eq_two.mp h2
            rw [threeHigh_nonempty_alignedLowFiber_card G hfree hmin e {a, b}
              (by simp)]
            simpa [threeHighT1KeyMultiplicity, hab] using
              threeHigh_t1_pair_fiber_card
                G hfree hmin e x hxSupport huniq a b hab
          · by_cases hcanonical : S = ({0, 1, 2} : Finset (Fin 3))
            · subst S
              rw [threeHigh_nonempty_alignedLowFiber_card G hfree hmin e
                {0, 1, 2} (by simp)]
              simpa [threeHighT1KeyMultiplicity] using
                threeHigh_t1_triple_fiber_card
                  G e x hxSupport huniq {0, 1, 2} (by decide)
            · simpa [threeHighT1KeyMultiplicity, h0, h1, h2, hcanonical] using
                threeHigh_t1_alignedLow_other_fiber_card_eq_zero
                  G hfree hmin e x hxSupport huniq S h0 h1 h2 hcanonical

theorem threeHigh_t1_mask_key_fiber_card
    (key : Option (Fin 3) × Finset (Fin 3)) :
    Fintype.card {i : Fin 49 //
      smallHighMaskAlignedKey
        (OrderFortyNineSmallHighCensus.threeHighRepresentativeMasks 1) i = key} =
      threeHighT1KeyMultiplicity key := by
  decide +kernel +revert

theorem threeHighCanonicalFiberCover_one :
    ThreeHighCanonicalFiberCover 1 := by
  intro G _ _ _ hfree hmin hHigh hone
  obtain ⟨e, x, hxSupport, huniq⟩ :=
    threeHigh_t1_exists_normalized_labeling
      G hfree hmin hHigh hone
  refine ⟨e, by decide, ?_⟩
  intro key
  rw [threeHigh_t1_graph_key_fiber_card
      G hfree hmin hHigh hone e x hxSupport huniq key,
    threeHigh_t1_mask_key_fiber_card key]

theorem threeHighCanonicalGraphCover_one :
    ThreeHighCanonicalGraphCover 1 :=
  threeHighCanonicalGraphCover_of_labelingCover
    (threeHighCanonicalLabelingCover_of_fiberCover
      threeHighCanonicalFiberCover_one)

theorem threeHighCanonicalGraphCover_all
    (blocks : Nat) (hblocks : blocks ≤ 1) :
    ThreeHighCanonicalGraphCover blocks := by
  interval_cases blocks
  · exact threeHighCanonicalGraphCover_zero
  · exact threeHighCanonicalGraphCover_one

theorem orderFortyNineStratumExcluded_three_of_representativeExclusions
    (hexcluded : ∀ index, index ≤ 1 →
      ThreeHighCanonicalRepresentativeExcluded index) :
    OrderFortyNineStratumExcluded 3 :=
  orderFortyNineStratumExcluded_three_of_canonical
    threeHighCanonicalGraphCover_all hexcluded

end

end Erdos85
