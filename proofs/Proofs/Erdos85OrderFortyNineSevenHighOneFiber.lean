import Proofs.Erdos85OrderFortyNineSevenHighZeroFiber

/-!
# Fiber census for the one-block seven-high triple system

When `t=1`, the unique size-three high support can be sent to `012`.
This file begins the corresponding exact aligned-fiber normalization.
-/

namespace Erdos85

open SimpleGraph

noncomputable section

theorem sevenHigh_t1_global_incidence
    (G : SimpleGraph (Fin 49)) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 (Fin 49) G)
    (hmin : ∀ x : Fin 49, 7 ≤ G.degree x)
    (hHigh : (orderFortyNineHighVertices G).card = 7)
    (hone : orderFortyNineHighIncidenceCount G 3 = 1) :
    orderFortyNineHighIncidenceCount G 0 = 6 ∧
    orderFortyNineHighIncidenceCount G 1 = 17 ∧
    orderFortyNineHighIncidenceCount G 2 = 18 := by
  have hp := orderFortyNine_highIncidence_profile_of_seven_high
    G hfree hmin (Fintype.card_fin 49) hHigh
  dsimp only at hp
  omega

theorem sevenHigh_t1_exists_unique_triple_support
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

theorem sevenHigh_t1_exists_normalized_labeling
    (G : SimpleGraph (Fin 49)) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 (Fin 49) G)
    (hmin : ∀ x : Fin 49, 7 ≤ G.degree x)
    (hHigh : (orderFortyNineHighVertices G).card = 7)
    (hone : orderFortyNineHighIncidenceCount G 3 = 1) :
    ∃ e : {v // v ∈ orderFortyNineHighVertices G} ≃ Fin 7,
      ∃ x : Fin 49,
        sevenHighLabeledSupport G e x = {0, 1, 2} ∧
        ∀ y : Fin 49, (sevenHighLabeledSupport G e y).card = 3 → y = x := by
  let e0 : {v // v ∈ orderFortyNineHighVertices G} ≃ Fin 7 :=
    Fintype.equivFinOfCardEq (by simpa using hHigh)
  obtain ⟨x, hx, huniq⟩ := sevenHigh_t1_exists_unique_triple_support G hone
  have hx3 : (sevenHighLabeledSupport G e0 x).card = 3 := by
    rw [sevenHighLabeledSupport_card]
    exact hx.2
  obtain ⟨a, b, c, hab, hac, hbc, hsupport⟩ :=
    Finset.card_eq_three.mp hx3
  let f : Fin 3 → Fin 7 := ![a, b, c]
  have hf : Function.Injective f := by
    intro i j
    fin_cases i <;> fin_cases j <;> simp [f, hab, hac, hbc, Ne.symm hab,
      Ne.symm hac, Ne.symm hbc]
  obtain ⟨σ, hσ⟩ := Equiv.Perm.exists_extending_pair f
    (Fin.castLE (by omega : 3 ≤ 7)) hf
    (Fin.castLE_injective (by omega : 3 ≤ 7))
  let e := e0.trans σ
  refine ⟨e, x, ?_, ?_⟩
  · have hmap : sevenHighLabeledSupport G e x =
        (sevenHighLabeledSupport G e0 x).map σ.toEmbedding := by
      simp [sevenHighLabeledSupport, e, Finset.map_map]
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
      have hy0 : (sevenHighLabeledSupport G e y).card = 0 := by
        rw [sevenHighLabeledSupport_card]
        exact hz
      omega
    · rw [← sevenHighLabeledSupport_card G e y]
      exact hy3

theorem sevenHigh_singleton_fiber_card_eq_local
    (G : SimpleGraph (Fin 49)) [DecidableRel G.Adj]
    (e : {v // v ∈ orderFortyNineHighVertices G} ≃ Fin 7)
    (w : Fin 7) :
    Fintype.card {x : Fin 49 // sevenHighLabeledSupport G e x = {w}} =
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
    · have hw : w ∈ sevenHighLabeledSupport G e x := by simp [hs]
      simpa [SimpleGraph.mem_neighborFinset, G.adj_comm] using
        (mem_sevenHighLabeledSupport_iff G e x w).mp hw
    · rw [← sevenHighLabeledSupport_card G e x, hs]
      simp
  · intro hx
    have hxN := (Finset.mem_filter.mp hx).1
    have hxCard := (Finset.mem_filter.mp hx).2
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ x, ?_⟩
    have hw : w ∈ sevenHighLabeledSupport G e x := by
      apply (mem_sevenHighLabeledSupport_iff G e x w).mpr
      simpa [SimpleGraph.mem_neighborFinset, G.adj_comm] using hxN
    have hcard : (sevenHighLabeledSupport G e x).card = 1 := by
      rw [sevenHighLabeledSupport_card]
      exact hxCard
    obtain ⟨z, hz⟩ := Finset.card_eq_one.mp hcard
    have hwz : w = z := by simpa [hz] using hw
    simpa [hz, hwz]

theorem sevenHigh_t1_local_triple_card
    (G : SimpleGraph (Fin 49)) [DecidableRel G.Adj]
    (e : {v // v ∈ orderFortyNineHighVertices G} ≃ Fin 7)
    (x : Fin 49)
    (hxSupport : sevenHighLabeledSupport G e x = {0, 1, 2})
    (huniq : ∀ y : Fin 49,
      (sevenHighLabeledSupport G e y).card = 3 → y = x)
    (w : Fin 7) :
    ((G.neighborFinset (e.symm w).1).filter fun y =>
      (orderFortyNineHighSupport G y).card = 3).card =
      if w ∈ ({0, 1, 2} : Finset (Fin 7)) then 1 else 0 := by
  by_cases hw : w ∈ ({0, 1, 2} : Finset (Fin 7))
  · rw [if_pos hw]
    have hset : ((G.neighborFinset (e.symm w).1).filter fun y =>
        (orderFortyNineHighSupport G y).card = 3) = {x} := by
      ext y
      constructor
      · intro hy
        have hy3 : (sevenHighLabeledSupport G e y).card = 3 := by
          rw [sevenHighLabeledSupport_card]
          exact (Finset.mem_filter.mp hy).2
        simp [huniq y hy3]
      · intro hy
        have hyx : y = x := by simpa using hy
        subst y
        apply Finset.mem_filter.mpr
        constructor
        · simpa [SimpleGraph.mem_neighborFinset, G.adj_comm] using
            (mem_sevenHighLabeledSupport_iff G e x w).mp
              (by simpa [hxSupport] using hw)
        · rw [← sevenHighLabeledSupport_card G e x, hxSupport]
          decide
    rw [hset]
    simp
  · rw [if_neg hw, Finset.card_eq_zero]
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro y hy
    have hy3 : (sevenHighLabeledSupport G e y).card = 3 := by
      rw [sevenHighLabeledSupport_card]
      exact (Finset.mem_filter.mp hy).2
    have hyx := huniq y hy3
    have hwMem : w ∈ sevenHighLabeledSupport G e y :=
      (mem_sevenHighLabeledSupport_iff G e y w).mpr (by
        simpa [SimpleGraph.mem_neighborFinset, G.adj_comm] using
          (Finset.mem_filter.mp hy).1)
    rw [hyx, hxSupport] at hwMem
    exact hw hwMem

theorem sevenHigh_t1_singleton_fiber_card
    (G : SimpleGraph (Fin 49)) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 (Fin 49) G)
    (hmin : ∀ x : Fin 49, 7 ≤ G.degree x)
    (hHigh : (orderFortyNineHighVertices G).card = 7)
    (e : {v // v ∈ orderFortyNineHighVertices G} ≃ Fin 7)
    (x : Fin 49)
    (hxSupport : sevenHighLabeledSupport G e x = {0, 1, 2})
    (huniq : ∀ y : Fin 49,
      (sevenHighLabeledSupport G e y).card = 3 → y = x)
    (w : Fin 7) :
    Fintype.card {y : Fin 49 // sevenHighLabeledSupport G e y = {w}} =
      if w ∈ ({0, 1, 2} : Finset (Fin 7)) then 3 else 2 := by
  rw [sevenHigh_singleton_fiber_card_eq_local G e w]
  have hp := orderFortyNine_highNeighborhood_profile_of_seven_high
    G hfree hmin (Fintype.card_fin 49) hHigh
      (Finset.mem_filter.mp (e.symm w).2).2
  dsimp only at hp
  rw [sevenHigh_t1_local_triple_card G e x hxSupport huniq w] at hp
  by_cases hw : w ∈ ({0, 1, 2} : Finset (Fin 7)) <;>
    simp [hw] at hp ⊢ <;> omega

theorem sevenHigh_existsUnique_labeled_pairBlock
    (G : SimpleGraph (Fin 49)) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 (Fin 49) G)
    (hmin : ∀ x : Fin 49, 7 ≤ G.degree x)
    (e : {v // v ∈ orderFortyNineHighVertices G} ≃ Fin 7)
    {a b : Fin 7} (hab : a ≠ b) :
    ∃! x : Fin 49, ({a, b} : Finset (Fin 7)) ⊆
        sevenHighLabeledSupport G e x ∧
      ((sevenHighLabeledSupport G e x).card = 2 ∨
       (sevenHighLabeledSupport G e x).card = 3) := by
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
        exact (mem_sevenHighLabeledSupport_iff G e x _).mpr hx.1.symm
      · rw [hw]
        exact (mem_sevenHighLabeledSupport_iff G e x _).mpr hx.2.1.symm
    · simpa [sevenHighLabeledSupport_card] using hx.2.2.2
  · intro y hy
    apply huniq y
    have ha := hy.1 (by simp : a ∈ ({a, b} : Finset (Fin 7)))
    have hb := hy.1 (by simp : b ∈ ({a, b} : Finset (Fin 7)))
    refine ⟨?_, ?_, ?_, ?_⟩
    · simpa [G.adj_comm] using
        (mem_sevenHighLabeledSupport_iff G e y a).mp ha
    · simpa [G.adj_comm] using
        (mem_sevenHighLabeledSupport_iff G e y b).mp hb
    · exact orderFortyNine_neighbor_degree_seven_of_degreeEight
        G hfree hmin (Fintype.card_fin 49)
          (Finset.mem_filter.mp (e.symm a).2).2 (by
            simpa [G.adj_comm] using
              (mem_sevenHighLabeledSupport_iff G e y a).mp ha)
    · simpa [sevenHighLabeledSupport_card] using hy.2

theorem sevenHigh_t1_pair_fiber_card
    (G : SimpleGraph (Fin 49)) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 (Fin 49) G)
    (hmin : ∀ x : Fin 49, 7 ≤ G.degree x)
    (e : {v // v ∈ orderFortyNineHighVertices G} ≃ Fin 7)
    (x : Fin 49)
    (hxSupport : sevenHighLabeledSupport G e x = {0, 1, 2})
    (huniqTriple : ∀ y : Fin 49,
      (sevenHighLabeledSupport G e y).card = 3 → y = x)
    (a b : Fin 7) (hab : a ≠ b) :
    Fintype.card {y : Fin 49 // sevenHighLabeledSupport G e y = {a, b}} =
      if ({a, b} : Finset (Fin 7)) ⊆ {0, 1, 2} then 0 else 1 := by
  obtain ⟨z, hz, hzuniq⟩ :=
    sevenHigh_existsUnique_labeled_pairBlock G hfree hmin e hab
  by_cases hcovered : ({a, b} : Finset (Fin 7)) ⊆ {0, 1, 2}
  · rw [if_pos hcovered, Fintype.card_subtype, Finset.card_eq_zero]
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro y hy
    have hyEq := (Finset.mem_filter.mp hy).2
    have hyQual : ({a, b} : Finset (Fin 7)) ⊆
        sevenHighLabeledSupport G e y ∧
        ((sevenHighLabeledSupport G e y).card = 2 ∨
         (sevenHighLabeledSupport G e y).card = 3) := by
      refine ⟨by rw [hyEq], Or.inl ?_⟩
      rw [hyEq]
      simp [hab]
    have hxQual : ({a, b} : Finset (Fin 7)) ⊆
        sevenHighLabeledSupport G e x ∧
        ((sevenHighLabeledSupport G e x).card = 2 ∨
         (sevenHighLabeledSupport G e x).card = 3) := by
      refine ⟨by simpa [hxSupport] using hcovered, Or.inr ?_⟩
      rw [hxSupport]
      decide
    have hyx : y = x := (hzuniq y hyQual).trans (hzuniq x hxQual).symm
    have := congrArg (fun u => (sevenHighLabeledSupport G e u).card) hyx
    rw [hyEq, hxSupport] at this
    simp [hab] at this
  · rw [if_neg hcovered]
    have hz2 : (sevenHighLabeledSupport G e z).card = 2 := by
      rcases hz.2 with hz2 | hz3
      · exact hz2
      · have hzx := huniqTriple z hz3
        have : ({a, b} : Finset (Fin 7)) ⊆ {0, 1, 2} := by
          simpa [hzx, hxSupport] using hz.1
        exact False.elim (hcovered this)
    have hzEq : sevenHighLabeledSupport G e z = {a, b} :=
      (Finset.eq_of_subset_of_card_le hz.1 (by simp [hab, hz2])).symm
    have hone := sevenHighLabeledSupport_fiber_card_eq_one
      G hfree e z (by omega)
    simpa [hzEq] using hone

theorem sevenHigh_aligned_emptyLow_fiber_card
    (G : SimpleGraph (Fin 49)) [DecidableRel G.Adj]
    (e : {v // v ∈ orderFortyNineHighVertices G} ≃ Fin 7) :
    Fintype.card {x : Fin 49 //
      sevenHighGraphAlignedKey G e x = (none, ∅)} =
      orderFortyNineHighIncidenceCount G 0 := by
  rw [Fintype.card_subtype]
  have hset : (Finset.univ.filter fun x : Fin 49 =>
      sevenHighGraphAlignedKey G e x = (none, ∅)) =
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
        simp [sevenHighGraphAlignedKey, hxHigh] at hfirst
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_sdiff.mpr ⟨Finset.mem_univ x, hxNotHigh⟩, ?_⟩
      have : sevenHighLabeledSupport G e x = ∅ := by
        simpa [sevenHighGraphAlignedKey] using hsupp
      rw [← sevenHighLabeledSupport_card G e x, this]
      simp
    · intro hx
      have hxLow := (Finset.mem_filter.mp hx).1
      have hx0 := (Finset.mem_filter.mp hx).2
      have hxNotHigh := (Finset.mem_sdiff.mp hxLow).2
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ x, ?_⟩
      have hs : sevenHighLabeledSupport G e x = ∅ :=
        Finset.card_eq_zero.mp (by
          rw [sevenHighLabeledSupport_card]
          exact hx0)
      simp [sevenHighGraphAlignedKey, hxNotHigh, hs]
  rw [hset]
  rfl

theorem sevenHigh_t1_triple_fiber_card
    (G : SimpleGraph (Fin 49)) [DecidableRel G.Adj]
    (e : {v // v ∈ orderFortyNineHighVertices G} ≃ Fin 7)
    (x : Fin 49)
    (hxSupport : sevenHighLabeledSupport G e x = {0, 1, 2})
    (huniq : ∀ y : Fin 49,
      (sevenHighLabeledSupport G e y).card = 3 → y = x)
    (S : Finset (Fin 7)) (hS3 : S.card = 3) :
    Fintype.card {y : Fin 49 // sevenHighLabeledSupport G e y = S} =
      if S = {0, 1, 2} then 1 else 0 := by
  by_cases hS : S = {0, 1, 2}
  · subst S
    rw [if_pos rfl, Fintype.card_subtype]
    have hset : (Finset.univ.filter fun y : Fin 49 =>
        sevenHighLabeledSupport G e y = {0, 1, 2}) = {x} := by
      ext y
      constructor
      · intro hy
        have hyEq := (Finset.mem_filter.mp hy).2
        have hy3 : (sevenHighLabeledSupport G e y).card = 3 := by
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
    have hy3 : (sevenHighLabeledSupport G e y).card = 3 := by rw [hyEq]; exact hS3
    have hyx := huniq y hy3
    apply hS
    rw [← hyEq, hyx, hxSupport]

theorem sevenHigh_t1_alignedLow_other_fiber_card_eq_zero
    (G : SimpleGraph (Fin 49)) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 (Fin 49) G)
    (hmin : ∀ x : Fin 49, 7 ≤ G.degree x)
    (e : {v // v ∈ orderFortyNineHighVertices G} ≃ Fin 7)
    (x : Fin 49)
    (hxSupport : sevenHighLabeledSupport G e x = {0, 1, 2})
    (huniq : ∀ y : Fin 49,
      (sevenHighLabeledSupport G e y).card = 3 → y = x)
    (S : Finset (Fin 7))
    (h0 : S.card ≠ 0) (h1 : S.card ≠ 1) (h2 : S.card ≠ 2)
    (hcanonical : S ≠ {0, 1, 2}) :
    Fintype.card {y : Fin 49 //
      sevenHighGraphAlignedKey G e y = (none, S)} = 0 := by
  rw [Fintype.card_subtype, Finset.card_eq_zero]
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro y hy
  have hkey := (Finset.mem_filter.mp hy).2
  have hfirst := congrArg Prod.fst hkey
  have hsupp : sevenHighLabeledSupport G e y = S := by
    simpa [sevenHighGraphAlignedKey] using congrArg Prod.snd hkey
  have hyNotHigh : y ∉ orderFortyNineHighVertices G := by
    intro hyHigh
    simp [sevenHighGraphAlignedKey, hyHigh] at hfirst
  have hy7 : G.degree y = 7 := by
    rcases orderFortyNine_degree_eq_seven_or_eight
      G hfree hmin (Fintype.card_fin 49) y with hy7 | hy8
    · exact hy7
    · exact False.elim (hyNotHigh
        (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hy8⟩))
  have hle : S.card ≤ 3 := by
    rw [← hsupp, sevenHighLabeledSupport_card]
    simpa [orderFortyNineHighSupport] using
      orderFortyNine_highNeighborCount_le_three
        G hfree hmin (Fintype.card_fin 49) hy7
  have hS3 : S.card = 3 := by omega
  have hy3 : (sevenHighLabeledSupport G e y).card = 3 := by
    rw [hsupp]
    exact hS3
  have hyx := huniq y hy3
  apply hcanonical
  rw [← hsupp, hyx, hxSupport]

def sevenHighT1KeyMultiplicity
    (key : Option (Fin 7) × Finset (Fin 7)) : Nat :=
  match key.1 with
  | some _ => if key.2 = ∅ then 1 else 0
  | none =>
      if key.2.card = 0 then 6
      else if key.2.card = 1 then
        if key.2 ⊆ ({0, 1, 2} : Finset (Fin 7)) then 3 else 2
      else if key.2.card = 2 then
        if key.2 ⊆ ({0, 1, 2} : Finset (Fin 7)) then 0 else 1
      else if key.2 = ({0, 1, 2} : Finset (Fin 7)) then 1 else 0

theorem sevenHigh_t1_graph_key_fiber_card
    (G : SimpleGraph (Fin 49)) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 (Fin 49) G)
    (hmin : ∀ x : Fin 49, 7 ≤ G.degree x)
    (hHigh : (orderFortyNineHighVertices G).card = 7)
    (hone : orderFortyNineHighIncidenceCount G 3 = 1)
    (e : {v // v ∈ orderFortyNineHighVertices G} ≃ Fin 7)
    (x : Fin 49)
    (hxSupport : sevenHighLabeledSupport G e x = {0, 1, 2})
    (huniq : ∀ y : Fin 49,
      (sevenHighLabeledSupport G e y).card = 3 → y = x)
    (key : Option (Fin 7) × Finset (Fin 7)) :
    Fintype.card {y : Fin 49 // sevenHighGraphAlignedKey G e y = key} =
      sevenHighT1KeyMultiplicity key := by
  rcases key with ⟨label, S⟩
  cases label with
  | some w =>
      by_cases hS0 : S = ∅
      · subst S
        simpa [sevenHighT1KeyMultiplicity] using
          sevenHigh_alignedHigh_fiber_card_eq_one G hfree hmin e w
      · have hSne : S.Nonempty := Finset.nonempty_iff_ne_empty.mpr hS0
        simpa [sevenHighT1KeyMultiplicity, hS0] using
          sevenHigh_alignedHigh_nonemptySupport_fiber_card_eq_zero
            G hfree hmin e w S hSne
  | none =>
      by_cases h0 : S.card = 0
      · have hS0 : S = ∅ := Finset.card_eq_zero.mp h0
        subst S
        have hn0 := (sevenHigh_t1_global_incidence
          G hfree hmin hHigh hone).1
        simpa [sevenHighT1KeyMultiplicity, hn0] using
          sevenHigh_aligned_emptyLow_fiber_card G e
      · by_cases h1 : S.card = 1
        · obtain ⟨w, rfl⟩ := Finset.card_eq_one.mp h1
          rw [sevenHigh_nonempty_alignedLowFiber_card G hfree hmin e {w}
            (by simp)]
          have hs := sevenHigh_t1_singleton_fiber_card
            G hfree hmin hHigh e x hxSupport huniq w
          simpa [sevenHighT1KeyMultiplicity] using hs
        · by_cases h2 : S.card = 2
          · obtain ⟨a, b, hab, rfl⟩ := Finset.card_eq_two.mp h2
            rw [sevenHigh_nonempty_alignedLowFiber_card G hfree hmin e {a, b}
              (by simp)]
            simpa [sevenHighT1KeyMultiplicity, hab] using
              sevenHigh_t1_pair_fiber_card
                G hfree hmin e x hxSupport huniq a b hab
          · by_cases hcanonical : S = ({0, 1, 2} : Finset (Fin 7))
            · subst S
              rw [sevenHigh_nonempty_alignedLowFiber_card G hfree hmin e
                {0, 1, 2} (by simp)]
              simpa [sevenHighT1KeyMultiplicity] using
                sevenHigh_t1_triple_fiber_card
                  G e x hxSupport huniq {0, 1, 2} (by decide)
            · simpa [sevenHighT1KeyMultiplicity, h0, h1, h2, hcanonical] using
                sevenHigh_t1_alignedLow_other_fiber_card_eq_zero
                  G hfree hmin e x hxSupport huniq S h0 h1 h2 hcanonical

theorem sevenHigh_t1_mask_key_fiber_card
    (key : Option (Fin 7) × Finset (Fin 7)) :
    Fintype.card {i : Fin 49 //
      sevenHighMaskAlignedKey
        (OrderFortyNineSevenHighCensus.representativeMasks 1 0) i = key} =
      sevenHighT1KeyMultiplicity key := by
  native_decide +revert

theorem sevenHighCanonicalFiberCover_one :
    SevenHighCanonicalFiberCover 1 := by
  intro G _ _ _ hfree hmin hHigh hone
  obtain ⟨e, x, hxSupport, huniq⟩ :=
    sevenHigh_t1_exists_normalized_labeling
      G hfree hmin hHigh hone
  refine ⟨0, by native_decide, e, by native_decide, ?_⟩
  intro key
  rw [sevenHigh_t1_graph_key_fiber_card
      G hfree hmin hHigh hone e x hxSupport huniq key,
    sevenHigh_t1_mask_key_fiber_card key]

theorem sevenHighCanonicalGraphCover_one :
    SevenHighCanonicalGraphCover 1 :=
  sevenHighCanonicalGraphCover_of_labelingCover
    (sevenHighCanonicalLabelingCover_of_fiberCover
      sevenHighCanonicalFiberCover_one)

end

end Erdos85
