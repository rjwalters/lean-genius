import Proofs.Erdos85PureEndpointExteriorEvenConfigurationEqAddTwoPairMultiplicity
import Proofs.Erdos85PureEndpointExteriorEvenConfigurationGeneralCenterParity

/-!
# Center matchings for an `m+2` circuit

Degree-two shore fibers pair all nonhole rows at each full center.  This gives
an exact centerwise equation, while general center parity makes the remaining
hole fiber even in the `m+2` stratum.
-/

open Finset SimpleGraph BigOperators

namespace Erdos85

noncomputable section

/-- If every used shore point has selected-row degree two, each full center
splits the selected rows into pairs supported by owner points and hole rows. -/
theorem c4Free_binarySquare_pureEndpoint_degreeTwo_centerMatching
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
    let owner : V → Finset V := fun y => G.neighborFinset y ∩ F
    let K : W → Finset V := fun w =>
      (secondOrderDefectGraph G).neighborFinset w.1 ∩ F
    ∀ T : Finset W,
      (∀ y ∈ S, (T.filter fun w => G.Adj w.1 y).Nonempty →
        (T.filter fun w => G.Adj w.1 y).card = 2) →
      ∀ i ∈ F,
        let Uᵢ := S.filter fun y =>
          i ∈ owner y ∧ (T.filter fun w => G.Adj w.1 y).Nonempty
        2 * Uᵢ.card + (T.filter fun w => i ∈ K w).card = T.card := by
  classical
  dsimp only
  let F := fullLineCenters G S q
  let W := {w : V // w ∈ Fᶜ}
  let owner : V → Finset V := fun y => G.neighborFinset y ∩ F
  let K : W → Finset V := fun w =>
    (secondOrderDefectGraph G).neighborFinset w.1 ∩ F
  intro T hpoint i hiF
  let Lᵢ := S.filter fun y => i ∈ owner y
  let Uᵢ := S.filter fun y =>
    i ∈ owner y ∧ (T.filter fun w => G.Adj w.1 y).Nonempty
  have hnear := c4Free_binarySquare_pureEndpoint_exterior_nearParallelDesign
    G hfree hq hqm hreg hcard S hempty hCcard hshore htri
  have hrow : ∀ w ∈ T,
      (Lᵢ.filter fun y => G.Adj w.1 y).card =
        if i ∈ K w then 0 else 1 := by
    intro w _hw
    have hwF : w.1 ∉ F := Finset.mem_compl.mp w.2
    have hd := hnear w.1 hwF
    let B := G.neighborFinset w.1 ∩ S
    have hunion : B.biUnion owner = F \ K w := by
      simpa [B, K, owner, F] using hd.2.2.2
    by_cases hiK : i ∈ K w
    · simp only [hiK, if_true, Finset.card_eq_zero]
      ext y
      simp only [Finset.mem_filter]
      constructor
      · rintro ⟨hyL, hyAdj⟩
        have hyData := Finset.mem_filter.mp hyL
        have hyB : y ∈ B := Finset.mem_inter.mpr
          ⟨(G.mem_neighborFinset w.1 y).mpr hyAdj, hyData.1⟩
        have hiUnion : i ∈ B.biUnion owner :=
          Finset.mem_biUnion.mpr ⟨y, hyB, hyData.2⟩
        rw [hunion] at hiUnion
        exact ((Finset.mem_sdiff.mp hiUnion).2 hiK).elim
      · intro hy
        simp at hy
    · simp only [hiK, if_false]
      have hiUnion : i ∈ B.biUnion owner := by
        rw [hunion]
        exact Finset.mem_sdiff.mpr ⟨hiF, hiK⟩
      obtain ⟨y, hyB, hiy⟩ := Finset.mem_biUnion.mp hiUnion
      have hyL : y ∈ Lᵢ := Finset.mem_filter.mpr
        ⟨(Finset.mem_inter.mp hyB).2, hiy⟩
      have hyMem : y ∈ Lᵢ.filter fun z => G.Adj w.1 z :=
        Finset.mem_filter.mpr
          ⟨hyL, (G.mem_neighborFinset w.1 y).mp (Finset.mem_inter.mp hyB).1⟩
      apply Finset.card_eq_one.mpr
      refine ⟨y, ?_⟩
      ext z
      constructor
      · intro hz
        have hzData := Finset.mem_filter.mp hz
        have hzL := Finset.mem_filter.mp hzData.1
        have hzB : z ∈ B := Finset.mem_inter.mpr
          ⟨(G.mem_neighborFinset w.1 z).mpr hzData.2, hzL.1⟩
        have hzy : z = y := by
          by_contra hne
          have hdj := hd.2.2.1 hyB hzB (Ne.symm hne)
          exact Finset.disjoint_left.mp hdj hiy hzL.2
        simpa using hzy
      · intro hz
        have hzy : z = y := by simpa using hz
        simpa [hzy] using hyMem
  have hswap : (∑ w ∈ T, (Lᵢ.filter fun y => G.Adj w.1 y).card) =
      ∑ y ∈ Lᵢ, (T.filter fun w => G.Adj w.1 y).card := by
    calc
      (∑ w ∈ T, (Lᵢ.filter fun y => G.Adj w.1 y).card) =
          ∑ w ∈ T, ∑ y ∈ Lᵢ, if G.Adj w.1 y then 1 else 0 := by
        apply Finset.sum_congr rfl
        intro w _hw
        rw [Finset.card_filter]
      _ = ∑ y ∈ Lᵢ, ∑ w ∈ T, if G.Adj w.1 y then 1 else 0 := by
        rw [Finset.sum_comm]
      _ = ∑ y ∈ Lᵢ, (T.filter fun w => G.Adj w.1 y).card := by
        apply Finset.sum_congr rfl
        intro y _hy
        rw [Finset.card_filter]
  have hsupport : (∑ y ∈ Lᵢ,
      (T.filter fun w => G.Adj w.1 y).card) = 2 * Uᵢ.card := by
    rw [show Uᵢ.card = ∑ y ∈ Lᵢ,
        if (T.filter fun w => G.Adj w.1 y).Nonempty then 1 else 0 by
      rw [show Uᵢ = Lᵢ.filter
          (fun y => (T.filter fun w => G.Adj w.1 y).Nonempty) by
        ext y
        simp [Uᵢ, Lᵢ, and_assoc]]
      rw [Finset.card_filter]]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro y hyL
    have hyS := (Finset.mem_filter.mp hyL).1
    by_cases hyUsed : (T.filter fun w => G.Adj w.1 y).Nonempty
    · simp [hyUsed, hpoint y hyS hyUsed]
    · have hyEmpty : T.filter (fun w => G.Adj w.1 y) = ∅ :=
        Finset.not_nonempty_iff_eq_empty.mp hyUsed
      simp [hyEmpty]
  have hnonhole : (T.filter fun w => i ∉ K w).card = 2 * Uᵢ.card := by
    calc
      (T.filter fun w => i ∉ K w).card =
          ∑ w ∈ T, if i ∈ K w then 0 else 1 := by
        rw [Finset.card_filter]
        apply Finset.sum_congr rfl
        intro w _hw
        by_cases hi : i ∈ K w <;> simp [hi]
      _ = ∑ w ∈ T, (Lᵢ.filter fun y => G.Adj w.1 y).card := by
        apply Finset.sum_congr rfl
        intro w hw
        symm
        exact hrow w hw
      _ = 2 * Uᵢ.card := by rw [hswap, hsupport]
  have hpartition : (T.filter fun w => i ∉ K w).card +
      (T.filter fun w => i ∈ K w).card = T.card := by
    simpa using (Finset.card_filter_add_card_filter_not
      (s := T) (fun w => i ∉ K w))
  change 2 * Uᵢ.card + (T.filter fun w => i ∈ K w).card = T.card
  rw [← hnonhole]
  exact hpartition

set_option maxHeartbeats 800000 in
/-- In an endpoint `m+2` even configuration, each center has an even hole
fiber and the nonhole rows are paired by used points owned by that center. -/
theorem c4Free_binarySquare_pureEndpoint_evenConfiguration_eq_add_two_centerMatching
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
    let owner : V → Finset V := fun y => G.neighborFinset y ∩ F
    let K : W → Finset V := fun w =>
      (secondOrderDefectGraph G).neighborFinset w.1 ∩ F
    ∀ T : Finset W,
      (∀ y : P, Even ((T.filter fun w => G.Adj w.1 y.1).card)) →
      T.card = m + 2 →
      ∀ i ∈ F,
        let Uᵢ := S.filter fun y =>
          i ∈ owner y ∧ (T.filter fun w => G.Adj w.1 y).Nonempty
        2 * Uᵢ.card + (T.filter fun w => i ∈ K w).card = m + 2 ∧
        Even ((T.filter fun w => i ∈ K w).card) := by
  classical
  dsimp only
  let F := fullLineCenters G S q
  let W := {w : V // w ∈ Fᶜ}
  let P := {y : V // y ∈ S}
  let owner : V → Finset V := fun y => G.neighborFinset y ∩ F
  let K : W → Finset V := fun w =>
    (secondOrderDefectGraph G).neighborFinset w.1 ∩ F
  intro T heven hTcard i hiF
  have hpoint : ∀ y ∈ S, (T.filter fun w => G.Adj w.1 y).Nonempty →
      (T.filter fun w => G.Adj w.1 y).card = 2 := by
    intro y hyS hyUsed
    obtain ⟨w, hw⟩ := hyUsed
    have hwData := Finset.mem_filter.mp hw
    have hmul :=
      c4Free_binarySquare_pureEndpoint_evenConfiguration_eq_add_two_pointMultiplicity
        G hfree hq hqm hmEven hreg hcard S hempty hCcard hshore htri
        T heven hTcard w hwData.1 y
    simpa [SimpleGraph.mem_neighborFinset, hyS] using
      hmul (Finset.mem_inter.mpr
        ⟨(G.mem_neighborFinset w.1 y).mpr hwData.2, hyS⟩)
  have heq := c4Free_binarySquare_pureEndpoint_degreeTwo_centerMatching
    G hfree hq hqm hreg hcard S hempty hCcard hshore htri
    T hpoint i hiF
  have hparity :=
    (c4Free_binarySquare_pureEndpoint_evenConfiguration_centerHoleParity_iff
      G hfree hq hqm hreg hcard S hempty hCcard hshore htri
      T heven i hiF).2
  have hTcardEven : Even T.card := by
    rcases hmEven with ⟨a, ha⟩
    refine ⟨a + 1, ?_⟩
    omega
  change 2 * (S.filter fun y => i ∈ owner y ∧
      (T.filter fun w => G.Adj w.1 y).Nonempty).card +
      (T.filter fun w => i ∈ K w).card = m + 2 ∧ _
  exact ⟨heq.trans hTcard, hparity hTcardEven⟩

end

end Erdos85

#print axioms Erdos85.c4Free_binarySquare_pureEndpoint_degreeTwo_centerMatching
#print axioms
  Erdos85.c4Free_binarySquare_pureEndpoint_evenConfiguration_eq_add_two_centerMatching
