import Proofs.Erdos85PureEndpointExteriorEvenConfigurationEqualityPartnerBijection
import Proofs.Erdos85PureEndpointExteriorNearParallelDesign

/-!
# The private-pair graph degree law

Two circuit rows are private partners when their unique common shore point
has exactly one full-center owner.  The partner coordinatization identifies
the private neighbors of a row with its singleton-owner shore points, whose
number is exactly that row's full-center defect-hole count.
-/

open Finset SimpleGraph BigOperators

namespace Erdos85

noncomputable section

/-- In any equality circuit, the number of private partner rows of `w` is
exactly the number of full-center holes of `w`. -/
theorem c4Free_binarySquare_pureEndpoint_evenConfiguration_eq_succ_privatePairDegree
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
      ∀ w ∈ T,
        ((T.erase w).filter fun z =>
          ∃ y ∈ B w, y ∈ B z ∧ (owner y).card = 1).card =
        (K w).card := by
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
  have hpartner := linear_evenConfiguration_eq_succ_partnerBijection
    B T m hBcard hlinear hevenB hTcard
  intro w hwT
  let R₁ := S.filter fun y => (owner y).card = 1
  let A := (B w).filter fun y => (owner y).card = 1
  let Q := (T.erase w).filter fun z =>
    ∃ y ∈ B w, y ∈ B z ∧ (owner y).card = 1
  obtain ⟨f, hfBij, hfmem⟩ := hpartner w hwT
  have hAQ : A.card = Q.card := by
    apply Finset.card_bij
        (fun y hy => (f ⟨y, (Finset.mem_filter.mp hy).1⟩).1)
    · intro y hy
      have hyData := Finset.mem_filter.mp hy
      apply Finset.mem_filter.mpr
      refine ⟨(f ⟨y, hyData.1⟩).2, y, hyData.1, ?_, hyData.2⟩
      exact hfmem ⟨y, hyData.1⟩
    · intro y hy z hz hyz
      have hsub : (⟨y, (Finset.mem_filter.mp hy).1⟩ : {x // x ∈ B w}) =
          ⟨z, (Finset.mem_filter.mp hz).1⟩ := by
        apply hfBij.1
        exact Subtype.ext hyz
      exact congrArg Subtype.val hsub
    · intro z hz
      have hzData := Finset.mem_filter.mp hz
      obtain ⟨x, hxw, hxz, hxOne⟩ := hzData.2
      let zz : {b // b ∈ T.erase w} := ⟨z, hzData.1⟩
      obtain ⟨y, hyf⟩ := hfBij.2 zz
      have hzT : z ∈ T := Finset.mem_of_mem_erase hzData.1
      have hwz : w ≠ z := (Finset.ne_of_mem_erase hzData.1).symm
      have hyz : y.1 ∈ B z := by
        have hval : (f y).1 = z := congrArg Subtype.val hyf
        simpa [hval] using hfmem y
      have hyx : y.1 = x := by
        apply Finset.card_le_one.mp (hlinear w hwT z hzT hwz)
        · exact Finset.mem_inter.mpr ⟨y.2, hyz⟩
        · exact Finset.mem_inter.mpr ⟨hxw, hxz⟩
      refine ⟨y.1, Finset.mem_filter.mpr ⟨y.2, by simpa [hyx] using hxOne⟩, ?_⟩
      exact congrArg Subtype.val hyf
  have hhole : (K w).card = A.card := by
    have hwF : w.1 ∉ F := Finset.mem_compl.mp w.2
    have hAR : A = G.neighborFinset w.1 ∩ R₁ := by
      ext y
      simp [A, B, R₁, and_assoc, and_left_comm, and_comm]
    rw [hAR]
    simpa [K, R₁, owner, F] using (hnear w.1 hwF).2.1
  change Q.card = (K w).card
  omega

end

end Erdos85

#print axioms
  Erdos85.c4Free_binarySquare_pureEndpoint_evenConfiguration_eq_succ_privatePairDegree
