import Proofs.Erdos85PureEndpointExteriorMinimalCircuitCutWitness

/-! # Connected-cut property of a minimal exterior circuit -/

open Finset BigOperators

namespace Erdos85

noncomputable section

/-- Odd incidence on both shores of a split produces two incident elements,
one on each shore. -/
theorem odd_cut_point_exists_crossing_pair
    {α β : Type*} [DecidableEq α]
    (Inc : α → β → Prop) [DecidableRel Inc]
    (T U : Finset α) (y : β)
    (hUodd : Odd ((U.filter fun a => Inc a y).card))
    (hCodd : Odd (((T \ U).filter fun a => Inc a y).card)) :
    ∃ a ∈ U, ∃ b ∈ T \ U, Inc a y ∧ Inc b y := by
  rcases hUodd with ⟨r, hr⟩
  rcases hCodd with ⟨s, hs⟩
  have hUnonempty : (U.filter fun a => Inc a y).Nonempty := by
    apply card_pos.mp
    omega
  have hCnonempty : ((T \ U).filter fun a => Inc a y).Nonempty := by
    apply card_pos.mp
    omega
  obtain ⟨a, ha⟩ := hUnonempty
  obtain ⟨b, hb⟩ := hCnonempty
  exact ⟨a, (mem_filter.mp ha).1, b, (mem_filter.mp hb).1,
    (mem_filter.mp ha).2, (mem_filter.mp hb).2⟩

/-- The extracted minimal circuit's row-intersection graph crosses every
proper nonempty vertex cut. -/
theorem c4Free_binarySquare_pureEndpoint_exists_minimal_even_configuration_connectedCut
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) {q m : ℕ}
    (hq : 8 ≤ q) (hqm : q = 2 * m)
    (hreg : ∀ v, G.degree v = q)
    (hcard : Fintype.card V = q * q)
    (S : Finset V)
    (hempty : emptyLineCenters G S = ∅)
    (hCcard : (fullLineCenters G S q).card = q)
    (hshore : 2 * S.card = q * q + q)
    (htri : ∀ v,
      (G.neighborFinset v ∩ S).card = 0 ∨
      (G.neighborFinset v ∩ S).card = m ∨
      (G.neighborFinset v ∩ S).card = q) :
    let F := fullLineCenters G S q
    let W := {w : V // w ∈ Fᶜ}
    let P := {y : V // y ∈ S}
    let row := fun w : W => G.neighborFinset w.1 ∩ S
    ∃ T : Finset W, T.Nonempty ∧ m + 1 ≤ T.card ∧
      (∀ y : P, Even ((T.filter fun w => G.Adj w.1 y.1).card)) ∧
      (∀ U : Finset W, U ⊂ T → U.Nonempty →
        ¬ ∀ y : P, Even ((U.filter fun w => G.Adj w.1 y.1).card)) ∧
      (∀ U : Finset W, U ⊂ T → U.Nonempty →
        ∃ y : P,
          Odd ((U.filter fun w => G.Adj w.1 y.1).card) ∧
          Odd (((T \ U).filter fun w => G.Adj w.1 y.1).card)) ∧
      ∀ U : Finset W, U ⊂ T → U.Nonempty →
        ∃ w ∈ U, ∃ z ∈ T \ U, (row w ∩ row z).Nonempty := by
  classical
  dsimp only
  let F := fullLineCenters G S q
  let W := {w : V // w ∈ Fᶜ}
  let P := {y : V // y ∈ S}
  let row : W → Finset V := fun w => G.neighborFinset w.1 ∩ S
  let Inc : W → P → Prop := fun w y => G.Adj w.1 y.1
  obtain ⟨T, hT, hlarge, heven, hminimal, hoddCut⟩ :=
    c4Free_binarySquare_pureEndpoint_exists_minimal_even_configuration_cutWitness
      G hfree hq hqm hreg hcard S hempty hCcard hshore htri
  refine ⟨T, hT, hlarge, heven, hminimal, hoddCut, ?_⟩
  intro U hUT hU
  obtain ⟨y, hyU, hyC⟩ := hoddCut U hUT hU
  obtain ⟨w, hwU, z, hzC, hwy, hzy⟩ :=
    odd_cut_point_exists_crossing_pair Inc T U y hyU hyC
  refine ⟨w, hwU, z, hzC, y.1, ?_⟩
  exact mem_inter.mpr ⟨mem_inter.mpr ⟨
    (G.mem_neighborFinset w.1 y.1).mpr hwy, y.2⟩,
    mem_inter.mpr ⟨(G.mem_neighborFinset z.1 y.1).mpr hzy, y.2⟩⟩

end

end Erdos85

#print axioms Erdos85.odd_cut_point_exists_crossing_pair
#print axioms
  Erdos85.c4Free_binarySquare_pureEndpoint_exists_minimal_even_configuration_connectedCut
