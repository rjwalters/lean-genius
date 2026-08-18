import Proofs.Erdos85OrderFortyNineSevenHighFiberLabeling

/-!
# Fiber census for the empty seven-high triple system

When `t=0`, every low high-support has size at most two.  Globally there are
seven empty, fourteen singleton, and twenty-one pair supports; locally at
each high point there are exactly two singleton and six pair supports.
-/

namespace Erdos85

open SimpleGraph

noncomputable section

theorem sevenHigh_t0_global_incidence
    (G : SimpleGraph (Fin 49)) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 (Fin 49) G)
    (hmin : ∀ x : Fin 49, 7 ≤ G.degree x)
    (hHigh : (orderFortyNineHighVertices G).card = 7)
    (hzero : orderFortyNineHighIncidenceCount G 3 = 0) :
    orderFortyNineHighIncidenceCount G 0 = 7 ∧
    orderFortyNineHighIncidenceCount G 1 = 14 ∧
    orderFortyNineHighIncidenceCount G 2 = 21 := by
  have hp := orderFortyNine_highIncidence_profile_of_seven_high
    G hfree hmin (Fintype.card_fin 49) hHigh
  dsimp only at hp
  omega

theorem sevenHigh_t0_no_triple_neighbor
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

theorem sevenHigh_t0_local_incidence
    (G : SimpleGraph (Fin 49)) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 (Fin 49) G)
    (hmin : ∀ x : Fin 49, 7 ≤ G.degree x)
    (hHigh : (orderFortyNineHighVertices G).card = 7)
    (hzero : orderFortyNineHighIncidenceCount G 3 = 0)
    {v : Fin 49} (hv : v ∈ orderFortyNineHighVertices G) :
    ((G.neighborFinset v).filter fun x =>
      (orderFortyNineHighSupport G x).card = 1).card = 2 ∧
    ((G.neighborFinset v).filter fun x =>
      (orderFortyNineHighSupport G x).card = 2).card = 6 := by
  have hv8 : G.degree v = 8 := (Finset.mem_filter.mp hv).2
  have hp := orderFortyNine_highNeighborhood_profile_of_seven_high
    G hfree hmin (Fintype.card_fin 49) hHigh hv8
  dsimp only at hp
  have h3 := sevenHigh_t0_no_triple_neighbor G hfree hmin hzero hv
  omega

theorem sevenHigh_t0_exists_pair_support
    (G : SimpleGraph (Fin 49)) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 (Fin 49) G)
    (hmin : ∀ x : Fin 49, 7 ≤ G.degree x)
    (hzero : orderFortyNineHighIncidenceCount G 3 = 0)
    (e : {v // v ∈ orderFortyNineHighVertices G} ≃ Fin 7)
    (a b : Fin 7) (hab : a ≠ b) :
    ∃ x : Fin 49, sevenHighLabeledSupport G e x = {a, b} := by
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
  have hcardL : (sevenHighLabeledSupport G e x).card = 2 := by
    rw [sevenHighLabeledSupport_card]
    exact hxCard
  have hsub : ({a, b} : Finset (Fin 7)) ⊆
      sevenHighLabeledSupport G e x := by
    intro w hw
    simp only [Finset.mem_insert, Finset.mem_singleton] at hw
    rcases hw with hw | hw
    · subst w
      exact (mem_sevenHighLabeledSupport_iff G e x _).mpr hx.1.symm
    · subst w
      exact (mem_sevenHighLabeledSupport_iff G e x _).mpr hx.2.1.symm
  refine ⟨x, ?_⟩
  have hpCard : ({a, b} : Finset (Fin 7)).card = 2 := by simp [hab]
  exact (Finset.eq_of_subset_of_card_le hsub (by omega)).symm

theorem sevenHigh_t0_pair_fiber_card_eq_one
    (G : SimpleGraph (Fin 49)) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 (Fin 49) G)
    (hmin : ∀ x : Fin 49, 7 ≤ G.degree x)
    (hzero : orderFortyNineHighIncidenceCount G 3 = 0)
    (e : {v // v ∈ orderFortyNineHighVertices G} ≃ Fin 7)
    (a b : Fin 7) (hab : a ≠ b) :
    Fintype.card {x : Fin 49 // sevenHighLabeledSupport G e x = {a, b}} = 1 := by
  obtain ⟨x, hx⟩ := sevenHigh_t0_exists_pair_support
    G hfree hmin hzero e a b hab
  have hcard := sevenHighLabeledSupport_fiber_card_eq_one
    G hfree e x (by rw [hx]; simp [hab])
  simpa [hx] using hcard

theorem sevenHigh_t0_singleton_fiber_card_eq_two
    (G : SimpleGraph (Fin 49)) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 (Fin 49) G)
    (hmin : ∀ x : Fin 49, 7 ≤ G.degree x)
    (hHigh : (orderFortyNineHighVertices G).card = 7)
    (hzero : orderFortyNineHighIncidenceCount G 3 = 0)
    (e : {v // v ∈ orderFortyNineHighVertices G} ≃ Fin 7)
    (w : Fin 7) :
    Fintype.card {x : Fin 49 // sevenHighLabeledSupport G e x = {w}} = 2 := by
  rw [Fintype.card_subtype]
  let v : Fin 49 := (e.symm w).1
  have hv : v ∈ orderFortyNineHighVertices G := (e.symm w).2
  have hset : (Finset.univ.filter fun x : Fin 49 =>
      sevenHighLabeledSupport G e x = {w}) =
      (G.neighborFinset v).filter fun x =>
        (orderFortyNineHighSupport G x).card = 1 := by
    ext x
    constructor
    · intro hx
      have hs := (Finset.mem_filter.mp hx).2
      apply Finset.mem_filter.mpr
      constructor
      · have hwMem : w ∈ sevenHighLabeledSupport G e x := by simp [hs]
        simpa [v, SimpleGraph.mem_neighborFinset, G.adj_comm] using
          (mem_sevenHighLabeledSupport_iff G e x w).mp hwMem
      · rw [← sevenHighLabeledSupport_card G e x, hs]
        simp
    · intro hx
      have hxN := (Finset.mem_filter.mp hx).1
      have hxCard := (Finset.mem_filter.mp hx).2
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ x, ?_⟩
      have hwMem : w ∈ sevenHighLabeledSupport G e x := by
        apply (mem_sevenHighLabeledSupport_iff G e x w).mpr
        simpa [v, SimpleGraph.mem_neighborFinset, G.adj_comm] using hxN
      have hcard : (sevenHighLabeledSupport G e x).card = 1 := by
        rw [sevenHighLabeledSupport_card]
        exact hxCard
      obtain ⟨z, hz⟩ := Finset.card_eq_one.mp hcard
      have hwz : w = z := by
        rw [hz] at hwMem
        simpa using hwMem
      simp [hz, hwz]
  rw [hset]
  exact (sevenHigh_t0_local_incidence
    G hfree hmin hHigh hzero hv).1

theorem sevenHigh_nonempty_alignedLowFiber_card
    (G : SimpleGraph (Fin 49)) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 (Fin 49) G)
    (hmin : ∀ x : Fin 49, 7 ≤ G.degree x)
    (e : {v // v ∈ orderFortyNineHighVertices G} ≃ Fin 7)
    (S : Finset (Fin 7)) (hS : S.Nonempty) :
    Fintype.card {x : Fin 49 // sevenHighGraphAlignedKey G e x = (none, S)} =
      Fintype.card {x : Fin 49 // sevenHighLabeledSupport G e x = S} := by
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
      have hcard : (sevenHighLabeledSupport G e x).card = 0 := by
        rw [sevenHighLabeledSupport_card]
        exact hz
      rw [hx] at hcard
      exact hS.ne_empty (Finset.card_eq_zero.mp hcard)
    simp [sevenHighGraphAlignedKey, hxNotHigh, hx]

theorem sevenHigh_t0_aligned_emptyLow_fiber_card_eq_seven
    (G : SimpleGraph (Fin 49)) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 (Fin 49) G)
    (hmin : ∀ x : Fin 49, 7 ≤ G.degree x)
    (hHigh : (orderFortyNineHighVertices G).card = 7)
    (hzero : orderFortyNineHighIncidenceCount G 3 = 0)
    (e : {v // v ∈ orderFortyNineHighVertices G} ≃ Fin 7) :
    Fintype.card {x : Fin 49 //
      sevenHighGraphAlignedKey G e x = (none, ∅)} = 7 := by
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
  exact (sevenHigh_t0_global_incidence
    G hfree hmin hHigh hzero).1

theorem sevenHigh_alignedHigh_fiber_card_eq_one
    (G : SimpleGraph (Fin 49)) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 (Fin 49) G)
    (hmin : ∀ x : Fin 49, 7 ≤ G.degree x)
    (e : {v // v ∈ orderFortyNineHighVertices G} ≃ Fin 7)
    (w : Fin 7) :
    Fintype.card {x : Fin 49 //
      sevenHighGraphAlignedKey G e x = (some w, ∅)} = 1 := by
  rw [Fintype.card_subtype]
  let v : Fin 49 := (e.symm w).1
  have hv : v ∈ orderFortyNineHighVertices G := (e.symm w).2
  have hset : (Finset.univ.filter fun x : Fin 49 =>
      sevenHighGraphAlignedKey G e x = (some w, ∅)) = {v} := by
    ext x
    constructor
    · intro hx
      have hkey := (Finset.mem_filter.mp hx).2
      have hfirst := congrArg Prod.fst hkey
      have hxHigh : x ∈ orderFortyNineHighVertices G := by
        by_contra hxNot
        simp [sevenHighGraphAlignedKey, hxNot] at hfirst
      have heq : e ⟨x, hxHigh⟩ = w := by
        simpa [sevenHighGraphAlignedKey, hxHigh] using hfirst
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
      have hs : sevenHighLabeledSupport G e v = ∅ :=
        Finset.card_eq_zero.mp (by
          rw [sevenHighLabeledSupport_card]
          exact hz)
      simp [sevenHighGraphAlignedKey, hv, v, hs]
  rw [hset]
  simp

def sevenHighT0KeyMultiplicity
    (key : Option (Fin 7) × Finset (Fin 7)) : Nat :=
  match key.1 with
  | some _ => if key.2 = ∅ then 1 else 0
  | none =>
      if key.2.card = 0 then 7
      else if key.2.card = 1 then 2
      else if key.2.card = 2 then 1
      else 0

/-- Independent finite audit of the complete mask-side aligned-key census for
the empty-triple representative. -/
theorem sevenHigh_t0_mask_key_fiber_card
    (key : Option (Fin 7) × Finset (Fin 7)) :
    Fintype.card {i : Fin 49 //
      sevenHighMaskAlignedKey
        (OrderFortyNineSevenHighCensus.representativeMasks 0 0) i = key} =
      sevenHighT0KeyMultiplicity key := by
  native_decide +revert

theorem sevenHigh_alignedHigh_nonemptySupport_fiber_card_eq_zero
    (G : SimpleGraph (Fin 49)) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 (Fin 49) G)
    (hmin : ∀ x : Fin 49, 7 ≤ G.degree x)
    (e : {v // v ∈ orderFortyNineHighVertices G} ≃ Fin 7)
    (w : Fin 7) (S : Finset (Fin 7)) (hS : S.Nonempty) :
    Fintype.card {x : Fin 49 //
      sevenHighGraphAlignedKey G e x = (some w, S)} = 0 := by
  rw [Fintype.card_subtype, Finset.card_eq_zero]
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro x hx
  have hkey := (Finset.mem_filter.mp hx).2
  have hfirst := congrArg Prod.fst hkey
  have hsupp := congrArg Prod.snd hkey
  have hxHigh : x ∈ orderFortyNineHighVertices G := by
    by_contra hxNot
    simp [sevenHighGraphAlignedKey, hxNot] at hfirst
  have hz := orderFortyNine_highNeighborCount_eq_zero_of_high
    G hfree hmin (Fintype.card_fin 49) hxHigh
  have hcard : (sevenHighLabeledSupport G e x).card = 0 := by
    rw [sevenHighLabeledSupport_card]
    exact hz
  have hs : sevenHighLabeledSupport G e x = S := by
    simpa [sevenHighGraphAlignedKey] using hsupp
  rw [hs] at hcard
  exact hS.ne_empty (Finset.card_eq_zero.mp hcard)

theorem sevenHigh_t0_alignedLow_other_fiber_card_eq_zero
    (G : SimpleGraph (Fin 49)) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 (Fin 49) G)
    (hmin : ∀ x : Fin 49, 7 ≤ G.degree x)
    (hzero : orderFortyNineHighIncidenceCount G 3 = 0)
    (e : {v // v ∈ orderFortyNineHighVertices G} ≃ Fin 7)
    (S : Finset (Fin 7))
    (h0 : S.card ≠ 0) (h1 : S.card ≠ 1) (h2 : S.card ≠ 2) :
    Fintype.card {x : Fin 49 //
      sevenHighGraphAlignedKey G e x = (none, S)} = 0 := by
  rw [Fintype.card_subtype, Finset.card_eq_zero]
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro x hx
  have hkey := (Finset.mem_filter.mp hx).2
  have hfirst := congrArg Prod.fst hkey
  have hsupp : sevenHighLabeledSupport G e x = S := by
    simpa [sevenHighGraphAlignedKey] using congrArg Prod.snd hkey
  have hxNotHigh : x ∉ orderFortyNineHighVertices G := by
    intro hxHigh
    simp [sevenHighGraphAlignedKey, hxHigh] at hfirst
  have hx7 : G.degree x = 7 := by
    rcases orderFortyNine_degree_eq_seven_or_eight
      G hfree hmin (Fintype.card_fin 49) x with hx7 | hx8
    · exact hx7
    · exact False.elim (hxNotHigh
        (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hx8⟩))
  have hle : S.card ≤ 3 := by
    rw [← hsupp, sevenHighLabeledSupport_card]
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
    rw [← sevenHighLabeledSupport_card G e x, hsupp]
    exact h3
  have hempty : ((orderFortyNineLowVertices G).filter fun y =>
      (G.neighborFinset y ∩ orderFortyNineHighVertices G).card = 3) = ∅ :=
    Finset.card_eq_zero.mp hzero
  rw [hempty] at hxGlobal
  simp at hxGlobal

theorem sevenHigh_t0_graph_key_fiber_card
    (G : SimpleGraph (Fin 49)) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 (Fin 49) G)
    (hmin : ∀ x : Fin 49, 7 ≤ G.degree x)
    (hHigh : (orderFortyNineHighVertices G).card = 7)
    (hzero : orderFortyNineHighIncidenceCount G 3 = 0)
    (e : {v // v ∈ orderFortyNineHighVertices G} ≃ Fin 7)
    (key : Option (Fin 7) × Finset (Fin 7)) :
    Fintype.card {x : Fin 49 // sevenHighGraphAlignedKey G e x = key} =
      sevenHighT0KeyMultiplicity key := by
  rcases key with ⟨label, S⟩
  cases label with
  | some w =>
      by_cases hS0 : S = ∅
      · subst S
        simpa [sevenHighT0KeyMultiplicity] using
          sevenHigh_alignedHigh_fiber_card_eq_one G hfree hmin e w
      · have hSne : S.Nonempty := Finset.nonempty_iff_ne_empty.mpr hS0
        simpa [sevenHighT0KeyMultiplicity, hS0] using
          sevenHigh_alignedHigh_nonemptySupport_fiber_card_eq_zero
            G hfree hmin e w S hSne
  | none =>
      by_cases h0 : S.card = 0
      · have hS0 : S = ∅ := Finset.card_eq_zero.mp h0
        subst S
        simpa [sevenHighT0KeyMultiplicity] using
          sevenHigh_t0_aligned_emptyLow_fiber_card_eq_seven
            G hfree hmin hHigh hzero e
      · by_cases h1 : S.card = 1
        · obtain ⟨w, rfl⟩ := Finset.card_eq_one.mp h1
          simpa [sevenHighT0KeyMultiplicity] using
            sevenHigh_nonempty_alignedLowFiber_card G hfree hmin e {w}
              (by simp) |>.trans
              (sevenHigh_t0_singleton_fiber_card_eq_two
                G hfree hmin hHigh hzero e w)
        · by_cases h2 : S.card = 2
          · obtain ⟨a, b, hab, rfl⟩ := Finset.card_eq_two.mp h2
            simpa [sevenHighT0KeyMultiplicity, hab] using
              (sevenHigh_nonempty_alignedLowFiber_card G hfree hmin e {a, b}
                (by simp) |>.trans
                (sevenHigh_t0_pair_fiber_card_eq_one
                  G hfree hmin hzero e a b hab))
          · simpa [sevenHighT0KeyMultiplicity, h0, h1, h2] using
              sevenHigh_t0_alignedLow_other_fiber_card_eq_zero
                G hfree hmin hzero e S h0 h1 h2

theorem sevenHighCanonicalFiberCover_zero :
    SevenHighCanonicalFiberCover 0 := by
  intro G _ _ _ hfree hmin hHigh hzero
  let e : {v // v ∈ orderFortyNineHighVertices G} ≃ Fin 7 :=
    Fintype.equivFinOfCardEq (by simpa using hHigh)
  refine ⟨0, by native_decide, e, by native_decide, ?_⟩
  intro key
  rw [sevenHigh_t0_graph_key_fiber_card
      G hfree hmin hHigh hzero e key,
    sevenHigh_t0_mask_key_fiber_card key]

theorem sevenHighCanonicalGraphCover_zero :
    SevenHighCanonicalGraphCover 0 :=
  sevenHighCanonicalGraphCover_of_labelingCover
    (sevenHighCanonicalLabelingCover_of_fiberCover
      sevenHighCanonicalFiberCover_zero)

end

end Erdos85
