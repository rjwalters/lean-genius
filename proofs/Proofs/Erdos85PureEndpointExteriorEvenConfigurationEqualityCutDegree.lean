import Proofs.Erdos85PureEndpointExteriorEvenConfigurationEquality
import Proofs.Erdos85PureEndpointExteriorRowIntersectionDegree

/-! # Exact external degree of a minimum exterior circuit -/

open Finset BigOperators

namespace Erdos85

noncomputable section

/-- In an equality-size even exterior configuration, every selected row has
exactly `m * (q - 4) + holes` intersections with rows outside the
configuration. -/
theorem c4Free_binarySquare_pureEndpoint_evenConfiguration_eq_succ_cutDegree
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
    ∀ T : Finset W,
      (∀ y : P, Even ((T.filter fun w => G.Adj w.1 y.1).card)) →
      T.card = m + 1 →
      ∀ w ∈ T,
        (((univ : Finset W) \ T).filter fun u =>
          (row w ∩ row u).Nonempty).card =
        m * (q - 4) +
          ((secondOrderDefectGraph G).neighborFinset w.1 ∩ F).card := by
  classical
  dsimp only
  let F := fullLineCenters G S q
  let W := {w : V // w ∈ Fᶜ}
  let P := {y : V // y ∈ S}
  let row : W → Finset V := fun w => G.neighborFinset w.1 ∩ S
  intro T heven hTcard w hwT
  have hdesign := c4Free_binarySquare_pureEndpoint_exterior_blockDesign
    G hfree hq hqm hreg hcard S hempty hCcard hshore htri
  have huniform : ∀ a ∈ T, (row a).card = m := by
    intro a ha
    exact hdesign.1 a.1 (by simpa [F] using (mem_compl.mp a.2))
  have hlinear : ∀ a ∈ T, ∀ b ∈ T, a ≠ b →
      ((row a) ∩ (row b)).card ≤ 1 := by
    intro a ha b hb hab
    exact hdesign.2.1 a.1 (by simpa [F] using (mem_compl.mp a.2))
      b.1 (by simpa [F] using (mem_compl.mp b.2))
      (fun h => hab (Subtype.ext h))
  have hevenRow : ∀ y : V, Even ((T.filter fun a => y ∈ row a).card) := by
    intro y
    by_cases hy : y ∈ S
    · let yy : P := ⟨y, hy⟩
      simpa [row, hy] using heven yy
    · have hz : T.filter (fun a => y ∈ row a) = ∅ := by
        ext a
        simp [row, hy]
      rw [hz]
      exact ⟨0, rfl⟩
  have hrigid := (linear_evenConfiguration_eq_succ_rigidity
    row T m huniform hlinear hevenRow hTcard).1
  let I := (T.erase w).filter fun u => (row w ∩ row u).Nonempty
  let C := ((univ : Finset W) \ T).filter fun u =>
    (row w ∩ row u).Nonempty
  let A := ((univ : Finset W).erase w).filter fun u =>
    (row w ∩ row u).Nonempty
  let H := ((secondOrderDefectGraph G).neighborFinset w.1 ∩ F).card
  have hI : I = T.erase w := by
    apply Finset.filter_eq_self.mpr
    intro u hu
    exact card_pos.mp (by
      rw [hrigid w hwT u (mem_of_mem_erase hu) (ne_of_mem_erase hu).symm]
      omega)
  have hIcard : I.card = m := by
    rw [hI, card_erase_of_mem hwT, hTcard]
    omega
  have hpart : A = I ∪ C := by
    ext u
    simp only [A, I, C, mem_filter, mem_erase, mem_univ, true_and,
      mem_union, mem_sdiff]
    constructor
    · rintro ⟨huw, hmeet⟩
      by_cases huT : u ∈ T
      · exact Or.inl ⟨⟨huw.1, huT⟩, hmeet⟩
      · exact Or.inr ⟨huT, hmeet⟩
    · rintro (⟨⟨huw, _⟩, hmeet⟩ | ⟨huNotT, hmeet⟩)
      · exact ⟨⟨huw, trivial⟩, hmeet⟩
      · exact ⟨⟨(fun huwEq => huNotT (huwEq ▸ hwT)), trivial⟩, hmeet⟩
  have hdis : Disjoint I C := by
    rw [Finset.disjoint_left]
    intro u huI huC
    exact (mem_sdiff.mp (mem_filter.mp huC).1).2
      (mem_erase.mp (mem_filter.mp huI).1).2
  have hcardPart : A.card = I.card + C.card := by
    rw [hpart, card_union_of_disjoint hdis]
  have hdegree := c4Free_binarySquare_pureEndpoint_exterior_rowIntersection_degree
    G hfree hq hqm hreg hcard S hempty hCcard hshore htri
  have hAcard : A.card = m * (q - 3) + H := by
    have hwR : w.1 ∈ (Fᶜ : Finset V) := by simpa [F] using w.2
    have hdegData := hdegree w.1 hwR
    let R := (Fᶜ : Finset V)
    let B : V → Finset V := fun v => G.neighborFinset v ∩ S
    let meetV := (R.erase w.1).filter fun v =>
      ((B w.1) ∩ (B v)).Nonempty
    have himage : A.image (fun u => u.1) = meetV := by
      ext v
      constructor
      · intro hv
        obtain ⟨u, huA, rfl⟩ := mem_image.mp hv
        have huData := mem_filter.mp huA
        exact mem_filter.mpr ⟨mem_erase.mpr ⟨
          (fun h => (mem_erase.mp huData.1).1 (Subtype.ext h)), u.2⟩,
          by simpa [row, B] using huData.2⟩
      · intro hv
        have hvData := mem_filter.mp hv
        let u : W := ⟨v, (mem_erase.mp hvData.1).2⟩
        refine mem_image.mpr ⟨u, mem_filter.mpr ⟨mem_erase.mpr ⟨?_, mem_univ _⟩,
          ?_⟩, rfl⟩
        · intro huv
          exact (mem_erase.mp hvData.1).1 (congrArg Subtype.val huv)
        · simpa [row, B] using hvData.2
    calc
      A.card = (A.image fun u => u.1).card :=
        (card_image_of_injective _ Subtype.val_injective).symm
      _ = meetV.card := congrArg card himage
      _ = m * (q - 3) + H := by rw [hdegData.1, hdegData.2]
  change C.card = m * (q - 4) + H
  have hbase : m * (q - 3) = m + m * (q - 4) := by
    have hsub : q - 3 = (q - 4) + 1 := by omega
    rw [hsub]
    ring
  rw [hcardPart, hIcard, hbase] at hAcard
  omega

end

end Erdos85

#print axioms Erdos85.c4Free_binarySquare_pureEndpoint_evenConfiguration_eq_succ_cutDegree
