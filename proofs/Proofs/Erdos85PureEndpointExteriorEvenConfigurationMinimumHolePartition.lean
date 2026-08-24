import Proofs.Erdos85PureEndpointExteriorEvenConfigurationHoleMassDichotomy

/-!
# The minimum-hole partition

At minimum hole mass, every full center is omitted by exactly one equality
circuit row.  Thus the row hole sets are pairwise disjoint and cover the full
center set.
-/

open Finset SimpleGraph BigOperators

namespace Erdos85

noncomputable section

/-- If an equality circuit has minimum hole mass `q`, its row hole sets form
a partition of the full centers. -/
theorem c4Free_binarySquare_pureEndpoint_evenConfiguration_eq_succ_minimumHolePartition
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) {q m : ℕ}
    (hq : 8 ≤ q) (hqm : q = 2 * m) (hmEven : Even m)
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
    let K : W → Finset V := fun w =>
      (secondOrderDefectGraph G).neighborFinset w.1 ∩ F
    ∀ T : Finset W,
      (∀ y : P, Even ((T.filter fun w => G.Adj w.1 y.1).card)) →
      T.card = m + 1 →
      (∑ w ∈ T, (K w).card) = q →
      (↑T : Set W).PairwiseDisjoint K ∧ T.biUnion K = F := by
  classical
  dsimp only
  let F := fullLineCenters G S q
  let W := {w : V // w ∈ Fᶜ}
  let P := {y : V // y ∈ S}
  let K : W → Finset V := fun w =>
    (secondOrderDefectGraph G).neighborFinset w.1 ∩ F
  intro T heven hTcard hmass
  have hdich :=
    c4Free_binarySquare_pureEndpoint_evenConfiguration_eq_succ_holeMassDichotomy
      G hfree hq hqm hmEven hreg hcard S hempty hCcard hshore htri
      T heven hTcard
  have hcenterOne : ∀ i ∈ F,
      (T.filter fun w => i ∈ K w).card = 1 := by
    rcases hdich with hminimum | hlarge
    · simpa [K, F] using hminimum.2.1
    · exfalso
      have hlarge' : q + 2 ≤ ∑ w ∈ T, (K w).card := by
        simpa [K, F] using hlarge
      have hmass' : (∑ w ∈ T, (K w).card) = q := by
        simpa [K, F] using hmass
      omega
  constructor
  · intro w hwT z hzT hwz
    apply Finset.disjoint_left.mpr
    intro i hiw hiz
    have hiF : i ∈ F := Finset.inter_subset_right hiw
    have hc := hcenterOne i hiF
    have hwFilter : w ∈ T.filter fun a => i ∈ K a :=
      Finset.mem_filter.mpr ⟨hwT, hiw⟩
    have hzFilter : z ∈ T.filter fun a => i ∈ K a :=
      Finset.mem_filter.mpr ⟨hzT, hiz⟩
    have hwzEq : w = z := by
      apply Finset.card_le_one.mp
      · rw [hc]
      · exact hwFilter
      · exact hzFilter
    exact hwz hwzEq
  · ext i
    constructor
    · intro hi
      obtain ⟨w, _hwT, hiK⟩ := Finset.mem_biUnion.mp hi
      exact Finset.inter_subset_right hiK
    · intro hiF
      have hc := hcenterOne i hiF
      have hnonempty : (T.filter fun w => i ∈ K w).Nonempty := by
        rw [← Finset.card_pos, hc]
        omega
      obtain ⟨w, hw⟩ := hnonempty
      have hwData := Finset.mem_filter.mp hw
      exact Finset.mem_biUnion.mpr ⟨w, hwData.1, hwData.2⟩

end

end Erdos85

#print axioms
  Erdos85.c4Free_binarySquare_pureEndpoint_evenConfiguration_eq_succ_minimumHolePartition
