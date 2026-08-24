import Proofs.Erdos85PureEndpointExteriorEvenConfigurationPrivateSupport

/-!
# Center matchings in an equality circuit

For each full center, its nonhole circuit rows are paired by the shore points
owned by that center.  Equality rigidity makes every used shore-point fiber
have size two, producing an exact centerwise matching equation.
-/

open Finset SimpleGraph BigOperators

namespace Erdos85

noncomputable section

/-- Every full center decomposes the equality circuit into two-row owner
fibers and an odd set of omitted rows. -/
theorem c4Free_binarySquare_pureEndpoint_evenConfiguration_eq_succ_centerMatching
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
      T.card = m + 1 →
      ∀ i ∈ F,
        let Uᵢ := S.filter fun y =>
          i ∈ owner y ∧ (T.filter fun w => G.Adj w.1 y).Nonempty
        2 * Uᵢ.card + (T.filter fun w => i ∈ K w).card = m + 1 ∧
        Odd ((T.filter fun w => i ∈ K w).card) := by
  classical
  dsimp only
  let F := fullLineCenters G S q
  let W := {w : V // w ∈ Fᶜ}
  let P := {y : V // y ∈ S}
  let owner : V → Finset V := fun y => G.neighborFinset y ∩ F
  let K : W → Finset V := fun w =>
    (secondOrderDefectGraph G).neighborFinset w.1 ∩ F
  intro T heven hTcard i hiF
  let B : W → Finset V := fun w => G.neighborFinset w.1 ∩ S
  let Lᵢ := S.filter fun y => i ∈ owner y
  let Uᵢ := S.filter fun y =>
    i ∈ owner y ∧ (T.filter fun w => G.Adj w.1 y).Nonempty
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
  have hrigid := linear_evenConfiguration_eq_succ_rigidity
    B T m hBcard hlinear hevenB hTcard
  have husedTwo : ∀ y ∈ Lᵢ,
      (T.filter fun w => G.Adj w.1 y).Nonempty →
      (T.filter fun w => G.Adj w.1 y).card = 2 := by
    intro y hyL hyUsed
    have hyS : y ∈ S := (Finset.mem_filter.mp hyL).1
    have hsame : (T.filter fun w => G.Adj w.1 y) =
        T.filter fun w => y ∈ B w := by
      ext w
      simp [B, hyS, SimpleGraph.mem_neighborFinset]
    rw [hsame]
    exact hrigid.2 y (hsame ▸ hyUsed)
  have hrow : ∀ w ∈ T,
      (Lᵢ.filter fun y => G.Adj w.1 y).card =
        if i ∈ K w then 0 else 1 := by
    intro w _hw
    have hwF : w.1 ∉ F := Finset.mem_compl.mp w.2
    have hd := hnear w.1 hwF
    have hunion : (B w).biUnion owner = F \ K w := by
      simpa [B, K, owner, F] using hd.2.2.2
    by_cases hiK : i ∈ K w
    · simp only [hiK, if_true, Finset.card_eq_zero]
      ext y
      simp only [Finset.mem_filter]
      constructor
      · rintro ⟨hyL, hyAdj⟩
        have hyData := Finset.mem_filter.mp hyL
        have hyB : y ∈ B w := Finset.mem_inter.mpr
          ⟨(G.mem_neighborFinset w.1 y).mpr hyAdj, hyData.1⟩
        have hiUnion : i ∈ (B w).biUnion owner :=
          Finset.mem_biUnion.mpr ⟨y, hyB, hyData.2⟩
        rw [hunion] at hiUnion
        exact ((Finset.mem_sdiff.mp hiUnion).2 hiK).elim
      · intro hy
        simpa using hy
    · simp only [hiK, if_false]
      have hiUnion : i ∈ (B w).biUnion owner := by
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
        have hzB : z ∈ B w := Finset.mem_inter.mpr
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
    by_cases hyUsed : (T.filter fun w => G.Adj w.1 y).Nonempty
    · simp [hyUsed, husedTwo y hyL hyUsed]
    · have hyEmpty : T.filter (fun w => G.Adj w.1 y) = ∅ :=
        Finset.not_nonempty_iff_eq_empty.mp hyUsed
      simp [hyUsed, hyEmpty]
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
    rw [← Finset.card_union_of_disjoint]
    · congr 1
      ext w
      by_cases hi : i ∈ K w <;> simp [hi]
    · exact Finset.disjoint_left.mpr fun w hnot hmem =>
        (Finset.mem_filter.mp hnot).2 (Finset.mem_filter.mp hmem).2
  have hodd :=
    (c4Free_binarySquare_pureEndpoint_evenConfiguration_eq_succ_centerHoleParity
      G hfree hq hqm hmEven hreg hcard S hempty hCcard hshore htri
      T heven hTcard).1 i hiF
  change 2 * Uᵢ.card + (T.filter fun w => i ∈ K w).card = m + 1 ∧ _
  rw [← hnonhole, hpartition, hTcard]
  exact ⟨rfl, hodd⟩

end

end Erdos85

#print axioms
  Erdos85.c4Free_binarySquare_pureEndpoint_evenConfiguration_eq_succ_centerMatching
