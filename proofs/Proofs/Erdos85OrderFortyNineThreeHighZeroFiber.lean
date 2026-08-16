import Proofs.Erdos85OrderFortyNineSmallHighFiberLabeling

/-!
# Fiber census for the empty three-high triple system

When `t=0`, every low high-support has size at most two.  Globally there are
twenty-five empty, eighteen singleton, and three pair supports; locally at
each high point there are exactly six singleton and two pair supports.
-/

namespace Erdos85

open SimpleGraph

noncomputable section

theorem threeHigh_t0_global_incidence
    (G : SimpleGraph (Fin 49)) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 (Fin 49) G)
    (hmin : ∀ x : Fin 49, 7 ≤ G.degree x)
    (hHigh : (orderFortyNineHighVertices G).card = 3)
    (hzero : orderFortyNineHighIncidenceCount G 3 = 0) :
    orderFortyNineHighIncidenceCount G 0 = 25 ∧
    orderFortyNineHighIncidenceCount G 1 = 18 ∧
    orderFortyNineHighIncidenceCount G 2 = 3 := by
  have hp := orderFortyNine_highIncidence_profile_of_three_high
    G hfree hmin (Fintype.card_fin 49) hHigh
  dsimp only at hp
  omega

theorem threeHigh_t0_no_triple_neighbor
    (G : SimpleGraph (Fin 49)) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 (Fin 49) G)
    (hmin : ∀ x : Fin 49, 7 ≤ G.degree x)
    (hzero : orderFortyNineHighIncidenceCount G 3 = 0)
    {v : Fin 49} (hv : v ∈ orderFortyNineHighVertices G) :
    ((G.neighborFinset v).filter fun x =>
      (orderFortyNineHighSupport G x).card = 3).card = 0 := by
  rw [Finset.card_eq_zero]
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro x hx
  have hxN := (Finset.mem_filter.mp hx).1
  have hx3 := (Finset.mem_filter.mp hx).2
  have hxLow : x ∈ orderFortyNineLowVertices G := by
    apply Finset.mem_sdiff.mpr
    refine ⟨Finset.mem_univ x, ?_⟩
    intro hxHigh
    have hx8 := (Finset.mem_filter.mp hxHigh).2
    have hv8 := (Finset.mem_filter.mp hv).2
    have hadj : G.Adj v x := by
      simpa [SimpleGraph.mem_neighborFinset] using hxN
    have hx7 := orderFortyNine_neighbor_degree_seven_of_degreeEight
      G hfree hmin (Fintype.card_fin 49) hv8 hadj
    omega
  have hxGlobal : x ∈ (orderFortyNineLowVertices G).filter fun y =>
      (G.neighborFinset y ∩ orderFortyNineHighVertices G).card = 3 := by
    apply Finset.mem_filter.mpr
    simpa [orderFortyNineHighSupport] using And.intro hxLow hx3
  have hempty : ((orderFortyNineLowVertices G).filter fun y =>
      (G.neighborFinset y ∩ orderFortyNineHighVertices G).card = 3) = ∅ := by
    apply Finset.card_eq_zero.mp
    exact hzero
  rw [hempty] at hxGlobal
  simp at hxGlobal

theorem threeHigh_t0_local_incidence
    (G : SimpleGraph (Fin 49)) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 (Fin 49) G)
    (hmin : ∀ x : Fin 49, 7 ≤ G.degree x)
    (hHigh : (orderFortyNineHighVertices G).card = 3)
    (hzero : orderFortyNineHighIncidenceCount G 3 = 0)
    {v : Fin 49} (hv : v ∈ orderFortyNineHighVertices G) :
    ((G.neighborFinset v).filter fun x =>
      (orderFortyNineHighSupport G x).card = 1).card = 6 ∧
    ((G.neighborFinset v).filter fun x =>
      (orderFortyNineHighSupport G x).card = 2).card = 2 := by
  have hv8 : G.degree v = 8 := (Finset.mem_filter.mp hv).2
  have hp := orderFortyNine_highNeighborhood_general_profile
    G hfree hmin (Fintype.card_fin 49) hv8
  dsimp only at hp
  rw [hHigh] at hp
  have h3 := threeHigh_t0_no_triple_neighbor G hfree hmin hzero hv
  omega

theorem threeHigh_t0_exists_pair_support
    (G : SimpleGraph (Fin 49)) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 (Fin 49) G)
    (hmin : ∀ x : Fin 49, 7 ≤ G.degree x)
    (hzero : orderFortyNineHighIncidenceCount G 3 = 0)
    (e : {v // v ∈ orderFortyNineHighVertices G} ≃ Fin 3)
    (a b : Fin 3) (hab : a ≠ b) :
    ∃ x : Fin 49, smallHighLabeledSupport G e x = {a, b} := by
  have hvab : (e.symm a).1 ≠ (e.symm b).1 := by
    intro h
    apply hab
    apply e.symm.injective
    exact Subtype.ext h
  obtain ⟨x, hx, _⟩ := orderFortyNine_existsUnique_pairBlock_of_highs
    G hfree hmin (Fintype.card_fin 49)
      (e.symm a).2 (e.symm b).2 hvab
  have hxCard : (orderFortyNineHighSupport G x).card = 2 := by
    rcases hx.2.2.2 with h2 | h3
    · exact h2
    · exfalso
      have hxLow : x ∈ orderFortyNineLowVertices G := by
        apply Finset.mem_sdiff.mpr
        refine ⟨Finset.mem_univ x, ?_⟩
        intro hxHigh
        have hx8 := (Finset.mem_filter.mp hxHigh).2
        omega
      have hxGlobal : x ∈ (orderFortyNineLowVertices G).filter fun y =>
          (G.neighborFinset y ∩ orderFortyNineHighVertices G).card = 3 := by
        exact Finset.mem_filter.mpr ⟨hxLow, by
          simpa [orderFortyNineHighSupport] using h3⟩
      have hempty : ((orderFortyNineLowVertices G).filter fun y =>
          (G.neighborFinset y ∩ orderFortyNineHighVertices G).card = 3) = ∅ :=
        Finset.card_eq_zero.mp hzero
      rw [hempty] at hxGlobal
      simp at hxGlobal
  have hcardL : (smallHighLabeledSupport G e x).card = 2 := by
    rw [smallHighLabeledSupport_card]
    exact hxCard
  have hsub : ({a, b} : Finset (Fin 3)) ⊆
      smallHighLabeledSupport G e x := by
    intro w hw
    simp only [Finset.mem_insert, Finset.mem_singleton] at hw
    rcases hw with hw | hw
    · subst w
      exact (mem_smallHighLabeledSupport_iff G e x _).mpr hx.1.symm
    · subst w
      exact (mem_smallHighLabeledSupport_iff G e x _).mpr hx.2.1.symm
  refine ⟨x, ?_⟩
  have hpCard : ({a, b} : Finset (Fin 3)).card = 2 := by simp [hab]
  exact (Finset.eq_of_subset_of_card_le hsub (by omega)).symm

theorem threeHigh_t0_pair_fiber_card_eq_one
    (G : SimpleGraph (Fin 49)) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 (Fin 49) G)
    (hmin : ∀ x : Fin 49, 7 ≤ G.degree x)
    (hzero : orderFortyNineHighIncidenceCount G 3 = 0)
    (e : {v // v ∈ orderFortyNineHighVertices G} ≃ Fin 3)
    (a b : Fin 3) (hab : a ≠ b) :
    Fintype.card {x : Fin 49 // smallHighLabeledSupport G e x = {a, b}} = 1 := by
  obtain ⟨x, hx⟩ := threeHigh_t0_exists_pair_support
    G hfree hmin hzero e a b hab
  have hcard := smallHighLabeledSupport_fiber_card_eq_one
    G hfree e x (by rw [hx]; simp [hab])
  simpa [hx] using hcard

theorem threeHigh_t0_singleton_fiber_card_eq_six
    (G : SimpleGraph (Fin 49)) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 (Fin 49) G)
    (hmin : ∀ x : Fin 49, 7 ≤ G.degree x)
    (hHigh : (orderFortyNineHighVertices G).card = 3)
    (hzero : orderFortyNineHighIncidenceCount G 3 = 0)
    (e : {v // v ∈ orderFortyNineHighVertices G} ≃ Fin 3)
    (w : Fin 3) :
    Fintype.card {x : Fin 49 // smallHighLabeledSupport G e x = {w}} = 6 := by
  rw [Fintype.card_subtype]
  let v : Fin 49 := (e.symm w).1
  have hv : v ∈ orderFortyNineHighVertices G := (e.symm w).2
  have hset : (Finset.univ.filter fun x : Fin 49 =>
      smallHighLabeledSupport G e x = {w}) =
      (G.neighborFinset v).filter fun x =>
        (orderFortyNineHighSupport G x).card = 1 := by
    ext x
    constructor
    · intro hx
      have hs := (Finset.mem_filter.mp hx).2
      apply Finset.mem_filter.mpr
      constructor
      · have hwMem : w ∈ smallHighLabeledSupport G e x := by simp [hs]
        simpa [v, SimpleGraph.mem_neighborFinset, G.adj_comm] using
          (mem_smallHighLabeledSupport_iff G e x w).mp hwMem
      · rw [← smallHighLabeledSupport_card G e x, hs]
        simp
    · intro hx
      have hxN := (Finset.mem_filter.mp hx).1
      have hxCard := (Finset.mem_filter.mp hx).2
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ x, ?_⟩
      have hwMem : w ∈ smallHighLabeledSupport G e x := by
        apply (mem_smallHighLabeledSupport_iff G e x w).mpr
        simpa [v, SimpleGraph.mem_neighborFinset, G.adj_comm] using hxN
      have hcard : (smallHighLabeledSupport G e x).card = 1 := by
        rw [smallHighLabeledSupport_card]
        exact hxCard
      obtain ⟨z, hz⟩ := Finset.card_eq_one.mp hcard
      have hwz : w = z := by
        rw [hz] at hwMem
        simpa using hwMem
      simp [hz, hwz]
  rw [hset]
  exact (threeHigh_t0_local_incidence
    G hfree hmin hHigh hzero hv).1

theorem threeHigh_nonempty_alignedLowFiber_card
    (G : SimpleGraph (Fin 49)) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 (Fin 49) G)
    (hmin : ∀ x : Fin 49, 7 ≤ G.degree x)
    (e : {v // v ∈ orderFortyNineHighVertices G} ≃ Fin 3)
    (S : Finset (Fin 3)) (hS : S.Nonempty) :
    Fintype.card {x : Fin 49 // smallHighGraphAlignedKey G e x = (none, S)} =
      Fintype.card {x : Fin 49 // smallHighLabeledSupport G e x = S} := by
  simp only [Fintype.card_subtype]
  congr 1
  ext x
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · intro hx
    exact congrArg Prod.snd hx
  · intro hx
    have hxNotHigh : x ∉ orderFortyNineHighVertices G := by
      intro hxHigh
      have hz := orderFortyNine_highNeighborCount_eq_zero_of_high
        G hfree hmin (Fintype.card_fin 49) hxHigh
      have hcard : (smallHighLabeledSupport G e x).card = 0 := by
        rw [smallHighLabeledSupport_card]
        exact hz
      rw [hx] at hcard
      exact hS.ne_empty (Finset.card_eq_zero.mp hcard)
    simp [smallHighGraphAlignedKey, hxNotHigh, hx]

theorem threeHigh_t0_aligned_emptyLow_fiber_card_eq_twentyFive
    (G : SimpleGraph (Fin 49)) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 (Fin 49) G)
    (hmin : ∀ x : Fin 49, 7 ≤ G.degree x)
    (hHigh : (orderFortyNineHighVertices G).card = 3)
    (hzero : orderFortyNineHighIncidenceCount G 3 = 0)
    (e : {v // v ∈ orderFortyNineHighVertices G} ≃ Fin 3) :
    Fintype.card {x : Fin 49 //
      smallHighGraphAlignedKey G e x = (none, ∅)} = 25 := by
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
  exact (threeHigh_t0_global_incidence
    G hfree hmin hHigh hzero).1

theorem threeHigh_alignedHigh_fiber_card_eq_one
    (G : SimpleGraph (Fin 49)) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 (Fin 49) G)
    (hmin : ∀ x : Fin 49, 7 ≤ G.degree x)
    (e : {v // v ∈ orderFortyNineHighVertices G} ≃ Fin 3)
    (w : Fin 3) :
    Fintype.card {x : Fin 49 //
      smallHighGraphAlignedKey G e x = (some w, ∅)} = 1 := by
  rw [Fintype.card_subtype]
  let v : Fin 49 := (e.symm w).1
  have hv : v ∈ orderFortyNineHighVertices G := (e.symm w).2
  have hset : (Finset.univ.filter fun x : Fin 49 =>
      smallHighGraphAlignedKey G e x = (some w, ∅)) = {v} := by
    ext x
    constructor
    · intro hx
      have hkey := (Finset.mem_filter.mp hx).2
      have hfirst := congrArg Prod.fst hkey
      have hxHigh : x ∈ orderFortyNineHighVertices G := by
        by_contra hxNot
        simp [smallHighGraphAlignedKey, hxNot] at hfirst
      have heq : e ⟨x, hxHigh⟩ = w := by
        simpa [smallHighGraphAlignedKey, hxHigh] using hfirst
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
      have hs : smallHighLabeledSupport G e v = ∅ :=
        Finset.card_eq_zero.mp (by
          rw [smallHighLabeledSupport_card]
          exact hz)
      simp [smallHighGraphAlignedKey, hv, v, hs]
  rw [hset]
  simp

def threeHighT0KeyMultiplicity
    (key : Option (Fin 3) × Finset (Fin 3)) : Nat :=
  match key.1 with
  | some _ => if key.2 = ∅ then 1 else 0
  | none =>
      if key.2.card = 0 then 25
      else if key.2.card = 1 then 6
      else if key.2.card = 2 then 1
      else 0

/-- Independent finite audit of the complete mask-side aligned-key census for
the empty-triple representative. -/
theorem threeHigh_t0_mask_key_fiber_card
    (key : Option (Fin 3) × Finset (Fin 3)) :
    Fintype.card {i : Fin 49 //
      smallHighMaskAlignedKey
        (OrderFortyNineSmallHighCensus.threeHighRepresentativeMasks 0) i = key} =
      threeHighT0KeyMultiplicity key := by
  native_decide +revert

theorem threeHigh_alignedHigh_nonemptySupport_fiber_card_eq_zero
    (G : SimpleGraph (Fin 49)) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 (Fin 49) G)
    (hmin : ∀ x : Fin 49, 7 ≤ G.degree x)
    (e : {v // v ∈ orderFortyNineHighVertices G} ≃ Fin 3)
    (w : Fin 3) (S : Finset (Fin 3)) (hS : S.Nonempty) :
    Fintype.card {x : Fin 49 //
      smallHighGraphAlignedKey G e x = (some w, S)} = 0 := by
  rw [Fintype.card_subtype, Finset.card_eq_zero]
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro x hx
  have hkey := (Finset.mem_filter.mp hx).2
  have hfirst := congrArg Prod.fst hkey
  have hsupp := congrArg Prod.snd hkey
  have hxHigh : x ∈ orderFortyNineHighVertices G := by
    by_contra hxNot
    simp [smallHighGraphAlignedKey, hxNot] at hfirst
  have hz := orderFortyNine_highNeighborCount_eq_zero_of_high
    G hfree hmin (Fintype.card_fin 49) hxHigh
  have hcard : (smallHighLabeledSupport G e x).card = 0 := by
    rw [smallHighLabeledSupport_card]
    exact hz
  have hs : smallHighLabeledSupport G e x = S := by
    simpa [smallHighGraphAlignedKey] using hsupp
  rw [hs] at hcard
  exact hS.ne_empty (Finset.card_eq_zero.mp hcard)

theorem threeHigh_t0_alignedLow_other_fiber_card_eq_zero
    (G : SimpleGraph (Fin 49)) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 (Fin 49) G)
    (hmin : ∀ x : Fin 49, 7 ≤ G.degree x)
    (hzero : orderFortyNineHighIncidenceCount G 3 = 0)
    (e : {v // v ∈ orderFortyNineHighVertices G} ≃ Fin 3)
    (S : Finset (Fin 3))
    (h0 : S.card ≠ 0) (h1 : S.card ≠ 1) (h2 : S.card ≠ 2) :
    Fintype.card {x : Fin 49 //
      smallHighGraphAlignedKey G e x = (none, S)} = 0 := by
  rw [Fintype.card_subtype, Finset.card_eq_zero]
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro x hx
  have hkey := (Finset.mem_filter.mp hx).2
  have hfirst := congrArg Prod.fst hkey
  have hsupp : smallHighLabeledSupport G e x = S := by
    simpa [smallHighGraphAlignedKey] using congrArg Prod.snd hkey
  have hxNotHigh : x ∉ orderFortyNineHighVertices G := by
    intro hxHigh
    simp [smallHighGraphAlignedKey, hxHigh] at hfirst
  have hx7 : G.degree x = 7 := by
    rcases orderFortyNine_degree_eq_seven_or_eight
      G hfree hmin (Fintype.card_fin 49) x with hx7 | hx8
    · exact hx7
    · exact False.elim (hxNotHigh
        (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hx8⟩))
  have hle : S.card ≤ 3 := by
    rw [← hsupp, smallHighLabeledSupport_card]
    simpa [orderFortyNineHighSupport] using
      orderFortyNine_highNeighborCount_le_three
        G hfree hmin (Fintype.card_fin 49) hx7
  have h3 : S.card = 3 := by omega
  have hxLow : x ∈ orderFortyNineLowVertices G :=
    Finset.mem_sdiff.mpr ⟨Finset.mem_univ x, hxNotHigh⟩
  have hxGlobal : x ∈ (orderFortyNineLowVertices G).filter fun y =>
      (G.neighborFinset y ∩ orderFortyNineHighVertices G).card = 3 := by
    apply Finset.mem_filter.mpr
    refine ⟨hxLow, ?_⟩
    change (orderFortyNineHighSupport G x).card = 3
    rw [← smallHighLabeledSupport_card G e x, hsupp]
    exact h3
  have hempty : ((orderFortyNineLowVertices G).filter fun y =>
      (G.neighborFinset y ∩ orderFortyNineHighVertices G).card = 3) = ∅ :=
    Finset.card_eq_zero.mp hzero
  rw [hempty] at hxGlobal
  simp at hxGlobal

theorem threeHigh_t0_graph_key_fiber_card
    (G : SimpleGraph (Fin 49)) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 (Fin 49) G)
    (hmin : ∀ x : Fin 49, 7 ≤ G.degree x)
    (hHigh : (orderFortyNineHighVertices G).card = 3)
    (hzero : orderFortyNineHighIncidenceCount G 3 = 0)
    (e : {v // v ∈ orderFortyNineHighVertices G} ≃ Fin 3)
    (key : Option (Fin 3) × Finset (Fin 3)) :
    Fintype.card {x : Fin 49 // smallHighGraphAlignedKey G e x = key} =
      threeHighT0KeyMultiplicity key := by
  rcases key with ⟨label, S⟩
  cases label with
  | some w =>
      by_cases hS0 : S = ∅
      · subst S
        simpa [threeHighT0KeyMultiplicity] using
          threeHigh_alignedHigh_fiber_card_eq_one G hfree hmin e w
      · have hSne : S.Nonempty := Finset.nonempty_iff_ne_empty.mpr hS0
        simpa [threeHighT0KeyMultiplicity, hS0] using
          threeHigh_alignedHigh_nonemptySupport_fiber_card_eq_zero
            G hfree hmin e w S hSne
  | none =>
      by_cases h0 : S.card = 0
      · have hS0 : S = ∅ := Finset.card_eq_zero.mp h0
        subst S
        simpa [threeHighT0KeyMultiplicity] using
          threeHigh_t0_aligned_emptyLow_fiber_card_eq_twentyFive
            G hfree hmin hHigh hzero e
      · by_cases h1 : S.card = 1
        · obtain ⟨w, rfl⟩ := Finset.card_eq_one.mp h1
          simpa [threeHighT0KeyMultiplicity] using
            threeHigh_nonempty_alignedLowFiber_card G hfree hmin e {w}
              (by simp) |>.trans
              (threeHigh_t0_singleton_fiber_card_eq_six
                G hfree hmin hHigh hzero e w)
        · by_cases h2 : S.card = 2
          · obtain ⟨a, b, hab, rfl⟩ := Finset.card_eq_two.mp h2
            simpa [threeHighT0KeyMultiplicity, hab] using
              (threeHigh_nonempty_alignedLowFiber_card G hfree hmin e {a, b}
                (by simp) |>.trans
                (threeHigh_t0_pair_fiber_card_eq_one
                  G hfree hmin hzero e a b hab))
          · simpa [threeHighT0KeyMultiplicity, h0, h1, h2] using
              threeHigh_t0_alignedLow_other_fiber_card_eq_zero
                G hfree hmin hzero e S h0 h1 h2

theorem threeHighCanonicalFiberCover_zero :
    ThreeHighCanonicalFiberCover 0 := by
  intro G _ _ _ hfree hmin hHigh hzero
  let e : {v // v ∈ orderFortyNineHighVertices G} ≃ Fin 3 :=
    Fintype.equivFinOfCardEq (by simpa using hHigh)
  refine ⟨e, by native_decide, ?_⟩
  intro key
  rw [threeHigh_t0_graph_key_fiber_card
      G hfree hmin hHigh hzero e key,
    threeHigh_t0_mask_key_fiber_card key]

theorem threeHighCanonicalGraphCover_zero :
    ThreeHighCanonicalGraphCover 0 :=
  threeHighCanonicalGraphCover_of_labelingCover
    (threeHighCanonicalLabelingCover_of_fiberCover
      threeHighCanonicalFiberCover_zero)

end

end Erdos85
