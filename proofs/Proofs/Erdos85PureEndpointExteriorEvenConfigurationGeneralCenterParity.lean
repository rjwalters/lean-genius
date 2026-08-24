import Proofs.Erdos85PureEndpointExteriorEvenConfigurationCenterHoleParity

/-!
# Unrestricted center-hole parity

The centerwise incidence swap does not require an equality-size circuit.
For any even exterior row configuration, the number of rows omitting a fixed
full center has the same parity as the total number of selected rows.
-/

open Finset SimpleGraph BigOperators

namespace Erdos85

noncomputable section

/-- In every even exterior configuration, each center-hole fiber has the
same parity as the configuration itself. -/
theorem c4Free_binarySquare_pureEndpoint_evenConfiguration_centerHoleParity_iff
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
      ∀ i ∈ F,
        Even ((T.filter fun w =>
          i ∈ (secondOrderDefectGraph G).neighborFinset w.1 ∩ F).card) ↔
        Even T.card := by
  classical
  dsimp only
  let F := fullLineCenters G S q
  let W := {w : V // w ∈ Fᶜ}
  let P := {y : V // y ∈ S}
  let owner : V → Finset V := fun y => G.neighborFinset y ∩ F
  let Inc : W → P → Prop := fun w y => G.Adj w.1 y.1
  let K : W → Finset V := fun w =>
    (secondOrderDefectGraph G).neighborFinset w.1 ∩ F
  intro T heven i hiF
  have hnear := c4Free_binarySquare_pureEndpoint_exterior_nearParallelDesign
    G hfree hq hqm hreg hcard S hempty hCcard hshore htri
  have hrow : ∀ w ∈ T,
      (((Finset.univ : Finset P).filter fun y => i ∈ owner y.1).filter
        fun y => Inc w y).card = if i ∈ K w then 0 else 1 := by
    intro w _hwT
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
        simpa [L] using hrow w hwT
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
  change Even ((T.filter fun w => i ∈ K w).card) ↔ Even T.card
  constructor
  · intro hholeEven
    rcases husedEven with ⟨a, ha⟩
    rcases hholeEven with ⟨b, hb⟩
    refine ⟨a + b, ?_⟩
    omega
  · intro hTEven
    rcases husedEven with ⟨a, ha⟩
    rcases hTEven with ⟨b, hb⟩
    refine ⟨(T.filter fun w => i ∈ K w).card / 2, ?_⟩
    omega

end

end Erdos85

#print axioms
  Erdos85.c4Free_binarySquare_pureEndpoint_evenConfiguration_centerHoleParity_iff
