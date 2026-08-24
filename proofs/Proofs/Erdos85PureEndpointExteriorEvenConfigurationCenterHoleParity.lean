import Proofs.Erdos85PureEndpointExteriorEvenConfigurationHoleParity

/-!
# Centerwise hole parity in an equality circuit

For a fixed full center, each exterior row either omits it (a defect hole) or
contains it in the unique owner block of one shore neighbor.  Even circuit
incidence makes the number of using rows even.  An equality circuit has odd
size when `m` is even, so every center is omitted by a positive odd number of
rows.  Summing over centers forces total hole mass at least `q`.
-/

open Finset SimpleGraph BigOperators

namespace Erdos85

noncomputable section

/-- Swapping a labeled incidence sum: even point fibers make the total number
of labeled incidences even. -/
theorem even_sum_labeled_incidence
    {α β : Type*} [DecidableEq α] [DecidableEq β]
    (Inc : α → β → Prop) [DecidableRel Inc]
    (T : Finset α) (L : Finset β)
    (heven : ∀ y ∈ L, Even ((T.filter fun a => Inc a y).card)) :
    Even (∑ a ∈ T, (L.filter fun y => Inc a y).card) := by
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
  rw [hswap]
  exact Finset.even_sum _ fun y hy => heven y hy

/-- In the even-`m` equality case, every full center is a defect hole of a
positive odd number of circuit rows, and the total hole mass is at least
`q`. -/
theorem c4Free_binarySquare_pureEndpoint_evenConfiguration_eq_succ_centerHoleParity
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
      (∀ i ∈ F, Odd ((T.filter fun w =>
        i ∈ (secondOrderDefectGraph G).neighborFinset w.1 ∩ F).card)) ∧
      q ≤ ∑ w ∈ T,
        ((secondOrderDefectGraph G).neighborFinset w.1 ∩ F).card := by
  classical
  dsimp only
  let F := fullLineCenters G S q
  let W := {w : V // w ∈ Fᶜ}
  let P := {y : V // y ∈ S}
  let owner : V → Finset V := fun y => G.neighborFinset y ∩ F
  let Inc : W → P → Prop := fun w y => G.Adj w.1 y.1
  let K : W → Finset V := fun w =>
    (secondOrderDefectGraph G).neighborFinset w.1 ∩ F
  intro T heven hTcard
  have hnear := c4Free_binarySquare_pureEndpoint_exterior_nearParallelDesign
    G hfree hq hqm hreg hcard S hempty hCcard hshore htri
  have hrow : ∀ i ∈ F, ∀ w ∈ T,
      (((Finset.univ : Finset P).filter fun y => i ∈ owner y.1).filter
        fun y => Inc w y).card = if i ∈ K w then 0 else 1 := by
    intro i hiF w hwT
    have hwF : w.1 ∉ F := Finset.mem_compl.mp w.2
    have hd := hnear w.1 hwF
    let B := G.neighborFinset w.1 ∩ S
    have hunion : B.biUnion owner = F \ K w := by
      simpa [B, K, owner, F] using hd.2.2.2
    by_cases hiK : i ∈ K w
    · simp only [hiK, if_true, Finset.card_eq_zero]
      ext y
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨hyLabel, hyInc⟩
        have hyB : y.1 ∈ B := Finset.mem_inter.mpr
          ⟨(G.mem_neighborFinset w.1 y.1).mpr hyInc, y.2⟩
        have hiUnion : i ∈ B.biUnion owner :=
          Finset.mem_biUnion.mpr ⟨y.1, hyB, hyLabel⟩
        rw [hunion] at hiUnion
        exact ((Finset.mem_sdiff.mp hiUnion).2 hiK).elim
      · intro hy
        simpa using hy
    · simp only [hiK, if_false]
      have hiUnion : i ∈ B.biUnion owner := by
        rw [hunion]
        exact Finset.mem_sdiff.mpr ⟨hiF, hiK⟩
      obtain ⟨y, hyB, hiy⟩ := Finset.mem_biUnion.mp hiUnion
      let yy : P := ⟨y, (Finset.mem_inter.mp hyB).2⟩
      have hyy : yy ∈ (((Finset.univ : Finset P).filter fun z =>
          i ∈ owner z.1).filter fun z => Inc w z) := by
        apply Finset.mem_filter.mpr
        refine ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ yy, hiy⟩, ?_⟩
        exact (G.mem_neighborFinset w.1 y).mp (Finset.mem_inter.mp hyB).1
      apply Finset.card_eq_one.mpr
      refine ⟨yy, ?_⟩
      ext z
      constructor
      · intro hz
        have hzData := Finset.mem_filter.mp hz
        have hzLabel := Finset.mem_filter.mp hzData.1
        have hzB : z.1 ∈ B := Finset.mem_inter.mpr
          ⟨(G.mem_neighborFinset w.1 z.1).mpr hzData.2, z.2⟩
        have hzy : z.1 = y := by
          by_contra hne
          have hdj := hd.2.2.1 hyB hzB (Ne.symm hne)
          exact Finset.disjoint_left.mp hdj hiy hzLabel.2
        simpa [yy] using Subtype.ext hzy
      · intro hz
        have : z = yy := by simpa using hz
        simpa [this] using hyy
  have hcenterOdd : ∀ i ∈ F, Odd ((T.filter fun w => i ∈ K w).card) := by
    intro i hiF
    let L : Finset P := (Finset.univ : Finset P).filter fun y => i ∈ owner y.1
    have husedEven : Even (∑ w ∈ T, (L.filter fun y => Inc w y).card) := by
      apply even_sum_labeled_incidence Inc T L
      intro y _hy
      exact heven y
    have husedEq : (∑ w ∈ T, (L.filter fun y => Inc w y).card) =
        (T.filter fun w => i ∉ K w).card := by
      calc
        (∑ w ∈ T, (L.filter fun y => Inc w y).card) =
            ∑ w ∈ T, if i ∈ K w then 0 else 1 := by
          apply Finset.sum_congr rfl
          intro w hwT
          simpa [L] using hrow i hiF w hwT
        _ = (T.filter fun w => i ∉ K w).card := by
          rw [Finset.card_filter]
          apply Finset.sum_congr rfl
          intro w _hw
          by_cases hi : i ∈ K w <;> simp [hi]
    rw [husedEq] at husedEven
    have hpartition : (T.filter fun w => i ∉ K w).card +
        (T.filter fun w => i ∈ K w).card = T.card := by
      rw [← Finset.card_union_of_disjoint]
      · congr 1
        ext w
        by_cases hi : i ∈ K w <;> simp [hi]
      · exact Finset.disjoint_left.mpr fun w hnot hmem =>
          (Finset.mem_filter.mp hnot).2 (Finset.mem_filter.mp hmem).2
    rcases husedEven with ⟨a, ha⟩
    rcases hmEven with ⟨b, hb⟩
    refine ⟨(T.filter fun w => i ∈ K w).card / 2, ?_⟩
    omega
  refine ⟨hcenterOdd, ?_⟩
  have hswap : (∑ w ∈ T, (K w).card) =
      ∑ i ∈ F, (T.filter fun w => i ∈ K w).card := by
    calc
      (∑ w ∈ T, (K w).card) =
          ∑ w ∈ T, ∑ i ∈ F, if i ∈ K w then 1 else 0 := by
        apply Finset.sum_congr rfl
        intro w _hw
        have hsub : K w ⊆ F := Finset.inter_subset_right
        rw [← Finset.sum_subset hsub]
        · simp
        · intro i _hiF hiK
          simp [hiK]
      _ = ∑ i ∈ F, ∑ w ∈ T, if i ∈ K w then 1 else 0 := by
        rw [Finset.sum_comm]
      _ = ∑ i ∈ F, (T.filter fun w => i ∈ K w).card := by
        apply Finset.sum_congr rfl
        intro i _hi
        rw [Finset.card_filter]
  rw [show (∑ w ∈ T,
      ((secondOrderDefectGraph G).neighborFinset w.1 ∩ F).card) =
      ∑ w ∈ T, (K w).card by rfl, hswap]
  calc
    q = F.card := by simpa [F] using hCcard.symm
    _ = ∑ _i ∈ F, 1 := by simp
    _ ≤ ∑ i ∈ F, (T.filter fun w => i ∈ K w).card := by
      apply Finset.sum_le_sum
      intro i hiF
      rcases hcenterOdd i hiF with ⟨a, ha⟩
      omega

end

end Erdos85

#print axioms Erdos85.even_sum_labeled_incidence
#print axioms
  Erdos85.c4Free_binarySquare_pureEndpoint_evenConfiguration_eq_succ_centerHoleParity
