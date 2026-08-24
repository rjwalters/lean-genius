import Proofs.Erdos85PureEndpointExteriorEvenConfigurationComplementDegreeParity

/-! # Complement degrees in odd-excess exterior circuits -/

open Finset BigOperators

namespace Erdos85

noncomputable section

set_option maxHeartbeats 800000

/-- A selected `m`-uniform block in a linear pointwise-even configuration
meets at least `m` other selected blocks. -/
theorem linear_even_configuration_internal_degree_ge_uniform
    {α β : Type*} [DecidableEq α] [DecidableEq β]
    (B : α → Finset β) (T : Finset α) (p : α) (m : ℕ)
    (hp : p ∈ T) (hcard : (B p).card = m)
    (heven : ∀ y : β, Even ((T.filter fun q => y ∈ B q).card))
    (hlinear : ∀ q ∈ T.erase p, ((B p) ∩ (B q)).card ≤ 1) :
    m ≤ ((T.erase p).filter fun q => ((B p) ∩ (B q)).Nonempty).card := by
  classical
  let M := (T.erase p).filter fun q => ((B p) ∩ (B q)).Nonempty
  have hpartner : ∀ y ∈ B p, ∃ q, q ∈ M ∧ y ∈ B q := by
    intro y hy
    let I := T.filter fun q => y ∈ B q
    have hpI : p ∈ I := mem_filter.mpr ⟨hp, hy⟩
    have hIeven : Even I.card := by simpa [I] using heven y
    have htwo : 2 ≤ I.card := by
      rcases hIeven with ⟨a, ha⟩
      have hpos : 0 < I.card := card_pos.mpr ⟨p, hpI⟩
      omega
    have hnonempty : (I.erase p).Nonempty := by
      apply card_pos.mp
      rw [card_erase_of_mem hpI]
      omega
    obtain ⟨q, hq⟩ := hnonempty
    have hqData := mem_erase.mp hq
    have hqI := mem_filter.mp hqData.2
    refine ⟨q, mem_filter.mpr ⟨mem_erase.mpr ⟨hqData.1, hqI.1⟩, ?_⟩,
      hqI.2⟩
    exact ⟨y, mem_inter.mpr ⟨hy, hqI.2⟩⟩
  let f : {y // y ∈ B p} → {q // q ∈ M} := fun y =>
    ⟨(hpartner y.1 y.2).choose, (hpartner y.1 y.2).choose_spec.1⟩
  have hfmem : ∀ y : {y // y ∈ B p}, y.1 ∈ B (f y).1 := by
    intro y
    exact (hpartner y.1 y.2).choose_spec.2
  have hfinj : Function.Injective f := by
    intro y z hyz
    apply Subtype.ext
    have hfErase := (mem_filter.mp (f y).2).1
    apply card_le_one.mp (hlinear (f y).1 hfErase)
    · exact mem_inter.mpr ⟨y.2, hfmem y⟩
    · exact mem_inter.mpr ⟨z.2, by simpa [hyz] using hfmem z⟩
  calc
    m = Fintype.card {y // y ∈ B p} := by
      rw [Fintype.card_coe, hcard]
    _ ≤ Fintype.card {q // q ∈ M} := Fintype.card_le_of_injective f hfinj
    _ = M.card := Fintype.card_coe M
    _ = ((T.erase p).filter fun q =>
        ((B p) ∩ (B q)).Nonempty).card := rfl

/-- Every row in any endpoint exterior even configuration has internal
intersection degree at least its uniform row size `m`. -/
theorem c4Free_binarySquare_pureEndpoint_evenConfiguration_internalDegree_ge
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) {q m : ℕ}
    (hq : 8 ≤ q) (hqm : q = 2 * m)
    (hreg : ∀ v, G.degree v = q)
    (hcardV : Fintype.card V = q * q)
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
      ∀ w ∈ T, m ≤ ((T.erase w).filter fun u =>
        (row w ∩ row u).Nonempty).card := by
  classical
  dsimp only
  let F := fullLineCenters G S q
  let W := {w : V // w ∈ Fᶜ}
  let P := {y : V // y ∈ S}
  let row : W → Finset V := fun w => G.neighborFinset w.1 ∩ S
  intro T heven w hw
  have hdesign := c4Free_binarySquare_pureEndpoint_exterior_blockDesign
    G hfree hq hqm hreg hcardV S hempty hCcard hshore htri
  have hrowCard : (row w).card = m :=
    hdesign.1 w.1 (by simpa [F] using (mem_compl.mp w.2))
  have hevenV : ∀ y : V, Even ((T.filter fun u => y ∈ row u).card) := by
    intro y
    by_cases hy : y ∈ S
    · let yy : P := ⟨y, hy⟩
      simpa [row, hy] using heven yy
    · have hz : T.filter (fun u => y ∈ row u) = ∅ := by
        ext u
        simp [row, hy]
      rw [hz]
      exact ⟨0, rfl⟩
  have hlinear : ∀ u ∈ T.erase w, ((row w) ∩ (row u)).card ≤ 1 := by
    intro u hu
    exact hdesign.2.1 w.1 (by simpa [F] using (mem_compl.mp w.2))
      u.1 (by simpa [F] using (mem_compl.mp u.2))
      (fun h => (ne_of_mem_erase hu) (Subtype.ext h).symm)
  exact linear_even_configuration_internal_degree_ge_uniform
    row T w m hw hrowCard hevenV hlinear

/-- If an exterior even configuration has odd size `m+1+2s`, every row has
an even number of missing partners, bounded by `2s`. -/
theorem c4Free_binarySquare_pureEndpoint_evenConfiguration_oddExcess_complementDegree
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) {q m s : ℕ}
    (hq : 8 ≤ q) (hqm : q = 2 * m) (hmEven : Even m)
    (hreg : ∀ v, G.degree v = q)
    (hcardV : Fintype.card V = q * q)
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
      T.card = m + 1 + 2 * s →
      ∀ w ∈ T,
        Even (((T.erase w).filter fun u =>
          ¬ (row w ∩ row u).Nonempty).card) ∧
        ((T.erase w).filter fun u =>
          ¬ (row w ∩ row u).Nonempty).card ≤ 2 * s := by
  classical
  dsimp only
  let F := fullLineCenters G S q
  let W := {w : V // w ∈ Fᶜ}
  let P := {y : V // y ∈ S}
  let row : W → Finset V := fun w => G.neighborFinset w.1 ∩ S
  intro T heven hTcard w hw
  let I := (T.erase w).filter fun u => (row w ∩ row u).Nonempty
  let N := (T.erase w).filter fun u => ¬ (row w ∩ row u).Nonempty
  have hIge : m ≤ I.card := by
    simpa [I, row, inter_assoc] using
      c4Free_binarySquare_pureEndpoint_evenConfiguration_internalDegree_ge
        G hfree hq hqm hreg hcardV S hempty hCcard hshore htri T heven w hw
  have hparity :=
    c4Free_binarySquare_pureEndpoint_evenConfiguration_complementDegreeParity
      G hfree hq hqm hmEven hreg hcardV S hempty hCcard hshore htri
      T heven w hw
  have hTcardOdd : Odd T.card := by
    rcases hmEven with ⟨a, ha⟩
    refine ⟨a + s, ?_⟩
    omega
  have hNeven : Even N.card := by
    simpa [N, row, inter_assoc] using hparity.1 hTcardOdd
  have hpart : T.erase w = I ∪ N := by
    ext u
    simp only [I, N, mem_erase, mem_union, mem_filter]
    constructor
    · intro hu
      by_cases hmeet : (row w ∩ row u).Nonempty
      · exact Or.inl ⟨hu, hmeet⟩
      · exact Or.inr ⟨hu, hmeet⟩
    · rintro (⟨hu, _⟩ | ⟨hu, _⟩) <;> exact hu
  have hdis : Disjoint I N := by
    rw [Finset.disjoint_left]
    intro u huI huN
    exact (mem_filter.mp huN).2 (mem_filter.mp huI).2
  have hcardPart : (T.erase w).card = I.card + N.card := by
    rw [hpart, card_union_of_disjoint hdis]
  have herase : (T.erase w).card = T.card - 1 := card_erase_of_mem hw
  refine ⟨by simpa [N, row, inter_assoc] using hNeven, ?_⟩
  change N.card ≤ 2 * s
  omega

/-- At the first larger odd stratum `|T|=m+3`, every row has either zero or
two missing partners. -/
theorem c4Free_binarySquare_pureEndpoint_evenConfiguration_eq_add_three_complementDegree
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) {q m : ℕ}
    (hq : 8 ≤ q) (hqm : q = 2 * m) (hmEven : Even m)
    (hreg : ∀ v, G.degree v = q)
    (hcardV : Fintype.card V = q * q)
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
      T.card = m + 3 →
      ∀ w ∈ T,
        (((T.erase w).filter fun u =>
          ¬ (row w ∩ row u).Nonempty).card = 0 ∨
        ((T.erase w).filter fun u =>
          ¬ (row w ∩ row u).Nonempty).card = 2) := by
  classical
  dsimp only
  intro T heven hTcard w hw
  have h :=
    c4Free_binarySquare_pureEndpoint_evenConfiguration_oddExcess_complementDegree
      G hfree hq hqm hmEven hreg hcardV S hempty hCcard hshore htri
      T heven (by omega : T.card = m + 1 + 2 * 1) w hw
  let N := (T.erase w).filter fun u =>
    ¬ ((G.neighborFinset w.1 ∩ S) ∩
      (G.neighborFinset u.1 ∩ S)).Nonempty
  have hNeven : Even N.card := by simpa [N] using h.1
  have hNle : N.card ≤ 2 := by simpa [N] using h.2
  rcases hNeven with ⟨a, ha⟩
  change N.card = 0 ∨ N.card = 2
  omega

end

end Erdos85

#print axioms Erdos85.linear_even_configuration_internal_degree_ge_uniform
#print axioms Erdos85.c4Free_binarySquare_pureEndpoint_evenConfiguration_internalDegree_ge
#print axioms
  Erdos85.c4Free_binarySquare_pureEndpoint_evenConfiguration_oddExcess_complementDegree
#print axioms
  Erdos85.c4Free_binarySquare_pureEndpoint_evenConfiguration_eq_add_three_complementDegree
