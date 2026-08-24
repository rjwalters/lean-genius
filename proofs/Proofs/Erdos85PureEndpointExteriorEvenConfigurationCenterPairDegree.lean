import Proofs.Erdos85PureEndpointExteriorEvenConfigurationEqualityPartnerBijection
import Proofs.Erdos85PureEndpointExteriorNearParallelDesign

/-!
# Center-colored partner degrees

Each full center colors the circuit-row pairs whose unique intersection point
is owned by that center.  A row has colored degree one unless it omits the
center, in which case its colored degree is zero.
-/

open Finset SimpleGraph BigOperators

namespace Erdos85

noncomputable section

/-- Filtering a row-partner bijection by any point predicate preserves
cardinality, expressed without mentioning the chosen bijection. -/
theorem linear_evenConfiguration_eq_succ_partner_filter_card
    {α β : Type*} [Fintype α] [DecidableEq α] [DecidableEq β]
    (B : α → Finset β) (T : Finset α) (m : ℕ)
    (hcard : ∀ a ∈ T, (B a).card = m)
    (hlinear : ∀ a ∈ T, ∀ b ∈ T, a ≠ b →
      ((B a) ∩ (B b)).card ≤ 1)
    (heven : ∀ y : β, Even ((T.filter fun a => y ∈ B a).card))
    (hTcard : T.card = m + 1)
    (pred : β → Prop) [DecidablePred pred]
    (a : α) (haT : a ∈ T) :
    ((B a).filter pred).card =
      ((T.erase a).filter fun b =>
        ∃ y ∈ B a, y ∈ B b ∧ pred y).card := by
  classical
  obtain ⟨f, hfBij, hfmem⟩ :=
    linear_evenConfiguration_eq_succ_partnerBijection
      B T m hcard hlinear heven hTcard a haT
  apply Finset.card_bij
      (fun y hy => (f ⟨y, (Finset.mem_filter.mp hy).1⟩).1)
  · intro y hy
    have hyData := Finset.mem_filter.mp hy
    apply Finset.mem_filter.mpr
    refine ⟨(f ⟨y, hyData.1⟩).2, y, hyData.1, ?_, hyData.2⟩
    exact hfmem ⟨y, hyData.1⟩
  · intro y hy z hz hyz
    have hsub : (⟨y, (Finset.mem_filter.mp hy).1⟩ : {x // x ∈ B a}) =
        ⟨z, (Finset.mem_filter.mp hz).1⟩ := by
      apply hfBij.1
      exact Subtype.ext hyz
    exact congrArg Subtype.val hsub
  · intro b hb
    have hbData := Finset.mem_filter.mp hb
    obtain ⟨x, hxa, hxb, hxPred⟩ := hbData.2
    let bb : {b // b ∈ T.erase a} := ⟨b, hbData.1⟩
    obtain ⟨y, hyf⟩ := hfBij.2 bb
    have hbT : b ∈ T := Finset.mem_of_mem_erase hbData.1
    have hab : a ≠ b := (Finset.ne_of_mem_erase hbData.1).symm
    have hyb : y.1 ∈ B b := by
      have hval : (f y).1 = b := congrArg Subtype.val hyf
      simpa [hval] using hfmem y
    have hyx : y.1 = x := by
      apply Finset.card_le_one.mp (hlinear a haT b hbT hab)
      · exact Finset.mem_inter.mpr ⟨y.2, hyb⟩
      · exact Finset.mem_inter.mpr ⟨hxa, hxb⟩
    refine ⟨y.1, Finset.mem_filter.mpr ⟨y.2, by simpa [hyx] using hxPred⟩, ?_⟩
    exact congrArg Subtype.val hyf

/-- The exact center-colored degree of every equality-circuit row. -/
theorem c4Free_binarySquare_pureEndpoint_evenConfiguration_eq_succ_centerPairDegree
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
    let owner : V → Finset V := fun y => G.neighborFinset y ∩ F
    let B : W → Finset V := fun w => G.neighborFinset w.1 ∩ S
    let K : W → Finset V := fun w =>
      (secondOrderDefectGraph G).neighborFinset w.1 ∩ F
    ∀ T : Finset W,
      (∀ y : P, Even ((T.filter fun w => G.Adj w.1 y.1).card)) →
      T.card = m + 1 →
      ∀ i ∈ F, ∀ w ∈ T,
        ((T.erase w).filter fun z =>
          ∃ y ∈ B w, y ∈ B z ∧ i ∈ owner y).card =
        if i ∈ K w then 0 else 1 := by
  classical
  dsimp only
  let F := fullLineCenters G S q
  let W := {w : V // w ∈ Fᶜ}
  let P := {y : V // y ∈ S}
  let owner : V → Finset V := fun y => G.neighborFinset y ∩ F
  let B : W → Finset V := fun w => G.neighborFinset w.1 ∩ S
  let K : W → Finset V := fun w =>
    (secondOrderDefectGraph G).neighborFinset w.1 ∩ F
  intro T heven hTcard
  have hnear := c4Free_binarySquare_pureEndpoint_exterior_nearParallelDesign
    G hfree hq hqm hreg hcard S hempty hCcard hshore htri
  have hBcard : ∀ w ∈ T, (B w).card = m := by
    intro w _hw
    have hwF : w.1 ∉ F := Finset.mem_compl.mp w.2
    simpa [B, F] using (hnear w.1 hwF).1
  have hlinear : ∀ w ∈ T, ∀ z ∈ T, w ≠ z →
      ((B w) ∩ (B z)).card ≤ 1 := by
    intro w _hw z _hz hwz
    apply (Finset.card_le_card (show (B w) ∩ (B z) ⊆
        G.neighborFinset w.1 ∩ G.neighborFinset z.1 by
      intro y hy
      exact Finset.mem_inter.mpr
        ⟨(Finset.mem_inter.mp (Finset.mem_inter.mp hy).1).1,
          (Finset.mem_inter.mp (Finset.mem_inter.mp hy).2).1⟩)).trans
    exact card_inter_neighborFinset_le_one hfree (Subtype.coe_injective.ne hwz)
  have hevenB : ∀ y : V, Even ((T.filter fun w => y ∈ B w).card) := by
    intro y
    by_cases hyS : y ∈ S
    · let yy : P := ⟨y, hyS⟩
      have hsame : T.filter (fun w => y ∈ B w) =
          T.filter (fun w => G.Adj w.1 y) := by
        ext w
        simp [B, hyS, SimpleGraph.mem_neighborFinset]
      rw [hsame]
      simpa [yy] using heven yy
    · have hemptyFiber : T.filter (fun w => y ∈ B w) = ∅ := by
        ext w
        simp [B, hyS]
      simp [hemptyFiber]
  intro i hiF w hwT
  have hfilter := linear_evenConfiguration_eq_succ_partner_filter_card
    B T m hBcard hlinear hevenB hTcard (fun y => i ∈ owner y) w hwT
  rw [← hfilter]
  change ((B w).filter fun y => i ∈ owner y).card =
    if i ∈ K w then 0 else 1
  have hwF : w.1 ∉ F := Finset.mem_compl.mp w.2
  have hd := hnear w.1 hwF
  have hunion : (B w).biUnion owner = F \ K w := by
    simpa [B, K, owner, F] using hd.2.2.2
  by_cases hiK : i ∈ K w
  · simp only [hiK, if_true, Finset.card_eq_zero]
    ext y
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨hyB, hiy⟩
      have hiUnion : i ∈ (B w).biUnion owner :=
        Finset.mem_biUnion.mpr ⟨y, hyB, hiy⟩
      rw [hunion] at hiUnion
      exact ((Finset.mem_sdiff.mp hiUnion).2 hiK).elim
    · intro hy
      simpa using hy
  · simp only [hiK, if_false]
    have hiUnion : i ∈ (B w).biUnion owner := by
      rw [hunion]
      exact Finset.mem_sdiff.mpr ⟨hiF, hiK⟩
    obtain ⟨y, hyB, hiy⟩ := Finset.mem_biUnion.mp hiUnion
    have hyMem : y ∈ (B w).filter fun z => i ∈ owner z :=
      Finset.mem_filter.mpr ⟨hyB, hiy⟩
    apply Finset.card_eq_one.mpr
    refine ⟨y, ?_⟩
    ext z
    constructor
    · intro hz
      have hzData := Finset.mem_filter.mp hz
      have hzy : z = y := by
        by_contra hne
        have hdj := hd.2.2.1 hyB hzData.1 (Ne.symm hne)
        exact Finset.disjoint_left.mp hdj hiy hzData.2
      simpa using hzy
    · intro hz
      have hzy : z = y := by simpa using hz
      simpa [hzy] using hyMem

end

end Erdos85

#print axioms Erdos85.linear_evenConfiguration_eq_succ_partner_filter_card
#print axioms
  Erdos85.c4Free_binarySquare_pureEndpoint_evenConfiguration_eq_succ_centerPairDegree
