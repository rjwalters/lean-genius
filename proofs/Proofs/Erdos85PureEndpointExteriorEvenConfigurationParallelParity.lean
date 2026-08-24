import Proofs.Erdos85PureEndpointExteriorEvenConfigurationGirth
import Proofs.Erdos85PureEndpointExteriorNearParallelDesign

/-!
# Parallel equality circuits force odd half-degree

If every row of an exterior even configuration is a genuine parallel class,
then fixing any full center gives exactly one incident shore point in each
row.  Swapping incidences expresses the number of rows as a sum of even point
degrees.  Thus an equality circuit of size `m+1` forces `m` odd.
-/

open Finset SimpleGraph BigOperators

namespace Erdos85

noncomputable section

/-- If every selected block contains exactly one point from a label class
and all point degrees in the selected configuration are even, then the number
of selected blocks is even. -/
theorem even_card_of_unique_labeled_incidence
    {α β : Type*} [DecidableEq α] [DecidableEq β]
    (Inc : α → β → Prop) [DecidableRel Inc]
    (T : Finset α) (L : Finset β)
    (hone : ∀ a ∈ T, (L.filter fun y => Inc a y).card = 1)
    (heven : ∀ y ∈ L, Even ((T.filter fun a => Inc a y).card)) :
    Even T.card := by
  classical
  have hswap :
      (∑ a ∈ T, (L.filter fun y => Inc a y).card) =
        ∑ y ∈ L, (T.filter fun a => Inc a y).card := by
    calc
      (∑ a ∈ T, (L.filter fun y => Inc a y).card) =
          ∑ a ∈ T, ∑ y ∈ L, if Inc a y then 1 else 0 := by
        apply Finset.sum_congr rfl
        intro a _ha
        rw [Finset.card_filter]
      _ = ∑ y ∈ L, ∑ a ∈ T, if Inc a y then 1 else 0 := by
        rw [Finset.sum_comm]
      _ = ∑ y ∈ L, (T.filter fun a => Inc a y).card := by
        apply Finset.sum_congr rfl
        intro y _hy
        rw [Finset.card_filter]
  have hleft : (∑ a ∈ T, (L.filter fun y => Inc a y).card) = T.card := by
    calc
      (∑ a ∈ T, (L.filter fun y => Inc a y).card) =
          ∑ _a ∈ T, 1 := Finset.sum_congr rfl hone
      _ = T.card := by simp
  rw [← hleft, hswap]
  exact Finset.even_sum _ fun y hy => heven y hy

/-- At a pure endpoint, an equality-size exterior even configuration all of
whose rows have zero full-center defect holes forces `m` odd. -/
theorem c4Free_binarySquare_pureEndpoint_parallel_evenConfiguration_eq_succ_forces_odd
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
    ∀ T : Finset W,
      (∀ y : P, Even ((T.filter fun w => G.Adj w.1 y.1).card)) →
      T.card = m + 1 →
      (∀ w ∈ T,
        ((secondOrderDefectGraph G).neighborFinset w.1 ∩ F).card = 0) →
      Odd m := by
  classical
  dsimp only
  let F := fullLineCenters G S q
  let W := {w : V // w ∈ Fᶜ}
  let P := {y : V // y ∈ S}
  let owner : V → Finset V := fun y => G.neighborFinset y ∩ F
  intro T heven hTcard hzero
  have hFcard : F.card = q := by simpa [F] using hCcard
  have hFpos : 0 < F.card := by rw [hFcard]; omega
  obtain ⟨i, hiF⟩ := Finset.card_pos.mp hFpos
  let L : Finset P := (Finset.univ : Finset P).filter fun y => i ∈ owner y.1
  let Inc : W → P → Prop := fun w y => G.Adj w.1 y.1
  have hnear := c4Free_binarySquare_pureEndpoint_exterior_nearParallelDesign
    G hfree hq hqm hreg hcard S hempty hCcard hshore htri
  have hone : ∀ w ∈ T, (L.filter fun y => Inc w y).card = 1 := by
    intro w hwT
    have hwF : w.1 ∉ F := Finset.mem_compl.mp w.2
    have hd := hnear w.1 hwF
    let B := G.neighborFinset w.1 ∩ S
    let K := (secondOrderDefectGraph G).neighborFinset w.1 ∩ F
    have hK : K = ∅ := Finset.card_eq_zero.mp (by simpa [K] using hzero w hwT)
    have hunion : B.biUnion owner = F := by
      simpa [B, K, hK, sdiff_empty, owner, F] using hd.2.2.2
    have hiUnion : i ∈ B.biUnion owner := by rw [hunion]; exact hiF
    obtain ⟨y, hyB, hiy⟩ := Finset.mem_biUnion.mp hiUnion
    let yy : P := ⟨y, (Finset.mem_inter.mp hyB).2⟩
    have hyy : yy ∈ L.filter fun z => Inc w z := by
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ yy, hiy⟩, ?_⟩
      exact (G.mem_neighborFinset w.1 y).mp (Finset.mem_inter.mp hyB).1
    apply Finset.card_eq_one.mpr
    refine ⟨yy, ?_⟩
    ext z
    constructor
    · intro hz
      have hzData := Finset.mem_filter.mp hz
      have hzL := Finset.mem_filter.mp hzData.1
      have hzB : z.1 ∈ B := Finset.mem_inter.mpr
        ⟨(G.mem_neighborFinset w.1 z.1).mpr hzData.2, z.2⟩
      have hzy : z.1 = y := by
        by_contra hne
        have hdj := hd.2.2.1 hyB hzB (Ne.symm hne)
        exact Finset.disjoint_left.mp hdj hiy hzL.2
      simpa [yy] using Subtype.ext hzy
    · intro hz
      have : z = yy := by simpa using hz
      simpa [this] using hyy
  have hLeven : ∀ y ∈ L, Even ((T.filter fun w => Inc w y).card) := by
    intro y _hy
    exact heven y
  have hTeven := even_card_of_unique_labeled_incidence Inc T L hone hLeven
  rw [hTcard] at hTeven
  rcases hTeven with ⟨k, hk⟩
  have hmpos : 0 < m := by omega
  refine ⟨k - 1, ?_⟩
  omega

/-- In the dyadic-relevant case `m` even, an equality-size exterior even
configuration must contain a row with a positive defect-hole count. -/
theorem c4Free_binarySquare_pureEndpoint_evenConfiguration_eq_succ_exists_hole
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
    ∀ T : Finset W,
      (∀ y : P, Even ((T.filter fun w => G.Adj w.1 y.1).card)) →
      T.card = m + 1 →
      ∃ w ∈ T,
        0 < ((secondOrderDefectGraph G).neighborFinset w.1 ∩ F).card := by
  classical
  dsimp only
  intro T heven hTcard
  by_contra hnone
  simp only [not_exists, not_and, not_lt] at hnone
  have hall : ∀ w ∈ T,
      ((secondOrderDefectGraph G).neighborFinset w.1 ∩
        fullLineCenters G S q).card = 0 := by
    intro w hw
    exact Nat.eq_zero_of_le_zero (hnone w hw)
  have hodd :=
    c4Free_binarySquare_pureEndpoint_parallel_evenConfiguration_eq_succ_forces_odd
      G hfree hq hqm hreg hcard S hempty hCcard hshore htri
      T heven hTcard hall
  rcases hmEven with ⟨a, ha⟩
  rcases hodd with ⟨b, hb⟩
  omega

end

end Erdos85

#print axioms Erdos85.even_card_of_unique_labeled_incidence
#print axioms
  Erdos85.c4Free_binarySquare_pureEndpoint_parallel_evenConfiguration_eq_succ_forces_odd
#print axioms
  Erdos85.c4Free_binarySquare_pureEndpoint_evenConfiguration_eq_succ_exists_hole
