import Proofs.Erdos85PureEndpointExteriorEvenConfigurationOutsideMatching

/-! # Multiplicity of circuit edges in the outside matching cover -/

open Finset BigOperators

namespace Erdos85

noncomputable section

/-- A used circuit point lies on exactly `q - ownerCount - 2` exterior rows
outside the equality circuit. Thus its row-pair edge occurs in that many of
the outside-row matchings. -/
theorem c4Free_binarySquare_pureEndpoint_evenConfiguration_eq_succ_outsideEdgeMultiplicity
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
    let owner := fun y : V => G.neighborFinset y ∩ F
    ∀ T : Finset W,
      (∀ y : P, Even ((T.filter fun w => G.Adj w.1 y.1).card)) →
      T.card = m + 1 →
      ∀ y ∈ S,
        (T.filter fun w => G.Adj w.1 y).Nonempty →
        (((univ : Finset W) \ T).filter fun u => G.Adj u.1 y).card =
          q - (owner y).card - 2 := by
  classical
  dsimp only
  let F := fullLineCenters G S q
  let W := {w : V // w ∈ Fᶜ}
  let P := {y : V // y ∈ S}
  let row : W → Finset V := fun w => G.neighborFinset w.1 ∩ S
  let owner : V → Finset V := fun y => G.neighborFinset y ∩ F
  intro T heven hTcard y hyS hyUsed
  have hdesign := c4Free_binarySquare_pureEndpoint_exterior_blockDesign
    G hfree hq hqm hreg hcard S hempty hCcard hshore htri
  have huniform : ∀ w ∈ T, (row w).card = m := by
    intro w hw
    exact hdesign.1 w.1 (by simpa [F] using (mem_compl.mp w.2))
  have hlinear : ∀ w ∈ T, ∀ z ∈ T, w ≠ z →
      ((row w) ∩ (row z)).card ≤ 1 := by
    intro w hw z hz hwz
    exact hdesign.2.1 w.1 (by simpa [F] using (mem_compl.mp w.2))
      z.1 (by simpa [F] using (mem_compl.mp z.2))
      (fun h => hwz (Subtype.ext h))
  have hevenV : ∀ z : V, Even ((T.filter fun w => z ∈ row w).card) := by
    intro z
    by_cases hz : z ∈ S
    · let zz : P := ⟨z, hz⟩
      simpa [row, hz] using heven zz
    · have hzero : T.filter (fun w => z ∈ row w) = ∅ := by
        ext w
        simp [row, hz]
      rw [hzero]
      exact ⟨0, rfl⟩
  have hrigid := (linear_evenConfiguration_eq_succ_rigidity
    row T m huniform hlinear hevenV hTcard).2
  have hyUsedRow : (T.filter fun w => y ∈ row w).Nonempty := by
    simpa [row, hyS] using hyUsed
  have hTfiber : (T.filter fun w => G.Adj w.1 y).card = 2 := by
    simpa [row, hyS] using hrigid y hyUsedRow
  let A := (univ : Finset W).filter fun w => G.Adj w.1 y
  let C := ((univ : Finset W) \ T).filter fun w => G.Adj w.1 y
  let I := T.filter fun w => G.Adj w.1 y
  have hpart : A = I ∪ C := by
    ext w
    simp only [A, I, C, mem_filter, mem_univ, true_and, mem_union, mem_sdiff]
    constructor
    · intro hwy
      by_cases hwT : w ∈ T
      · exact Or.inl ⟨hwT, hwy⟩
      · exact Or.inr ⟨hwT, hwy⟩
    · rintro (⟨_hwT, hwy⟩ | ⟨_hwNotT, hwy⟩) <;> exact hwy
  have hdis : Disjoint I C := by
    rw [Finset.disjoint_left]
    intro w hwI hwC
    exact (mem_sdiff.mp (mem_filter.mp hwC).1).2
      (mem_filter.mp hwI).1
  have hcardPart : A.card = I.card + C.card := by
    rw [hpart, card_union_of_disjoint hdis]
  have hAcard : A.card = q - (owner y).card := by
    have houtside := (hdesign.2.2 y hyS).2
    have himage : A.image (fun w => w.1) =
        G.neighborFinset y ∩ Fᶜ := by
      ext z
      constructor
      · intro hz
        obtain ⟨w, hwA, rfl⟩ := mem_image.mp hz
        exact mem_inter.mpr ⟨
          (G.mem_neighborFinset y w.1).mpr (mem_filter.mp hwA).2.symm,
          w.2⟩
      · intro hz
        have hzData := mem_inter.mp hz
        let w : W := ⟨z, hzData.2⟩
        exact mem_image.mpr ⟨w, mem_filter.mpr ⟨mem_univ _,
          ((G.mem_neighborFinset y z).mp hzData.1).symm⟩, rfl⟩
    calc
      A.card = (A.image fun w => w.1).card :=
        (card_image_of_injective _ Subtype.val_injective).symm
      _ = (G.neighborFinset y ∩ Fᶜ).card := congrArg card himage
      _ = q - (owner y).card := by simpa [owner, F] using houtside
  change C.card = q - (owner y).card - 2
  have hIcard : I.card = 2 := by simpa [I] using hTfiber
  omega

end

end Erdos85

#print axioms
  Erdos85.c4Free_binarySquare_pureEndpoint_evenConfiguration_eq_succ_outsideEdgeMultiplicity
