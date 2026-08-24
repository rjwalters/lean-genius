import Proofs.Erdos85PureEndpointExteriorEvenConfigurationEqAddTwoRigidity

/-!
# Point multiplicities in an `m+2` row circuit

The rigidity theorem makes the chosen-partner injection from the points of a
row onto all rows meeting it.  Linearity then shows that no third row can use
the same point.  Thus every used point has circuit multiplicity exactly two.
-/

open Finset SimpleGraph

namespace Erdos85

noncomputable section

/-- In a linear uniform even configuration, if a row meets exactly as many
other rows as it has points, every point of that row occurs in exactly two
configuration rows. -/
theorem linear_evenConfiguration_fiberCard_eq_two_of_internalDegree_eq_uniformCard
    {α β : Type*} [DecidableEq α] [DecidableEq β]
    (B : α → Finset β) (T : Finset α) (m : ℕ)
    (hcard : ∀ a ∈ T, (B a).card = m)
    (hlinear : ∀ a ∈ T, ∀ b ∈ T, a ≠ b →
      ((B a) ∩ (B b)).card ≤ 1)
    (heven : ∀ y : β, Even ((T.filter fun a => y ∈ B a).card))
    (a : α) (haT : a ∈ T)
    (hdegree : ((T.erase a).filter fun b => (B a ∩ B b).Nonempty).card = m) :
    ∀ y ∈ B a, (T.filter fun b => y ∈ B b).card = 2 := by
  classical
  let Q := (T.erase a).filter fun b => (B a ∩ B b).Nonempty
  have hpartner : ∀ y ∈ B a, ∃ b, b ∈ T.erase a ∧ y ∈ B b := by
    intro y hya
    let I := T.filter fun b => y ∈ B b
    have haI : a ∈ I := Finset.mem_filter.mpr ⟨haT, hya⟩
    have hpos : 0 < I.card := Finset.card_pos.mpr ⟨a, haI⟩
    have hIEven : Even I.card := by simpa [I] using heven y
    have htwo : 2 ≤ I.card := by
      rcases hIEven with ⟨k, hk⟩
      omega
    have herase : (I.erase a).card = I.card - 1 :=
      Finset.card_erase_of_mem haI
    have hne : (I.erase a).Nonempty := by
      apply Finset.card_pos.mp
      rw [herase]
      omega
    obtain ⟨b, hb⟩ := hne
    have hbData := Finset.mem_erase.mp hb
    have hbI := Finset.mem_filter.mp hbData.2
    exact ⟨b, Finset.mem_erase.mpr ⟨hbData.1, hbI.1⟩, hbI.2⟩
  let f : {y // y ∈ B a} → {b // b ∈ Q} := fun y =>
    ⟨(hpartner y.1 y.2).choose, Finset.mem_filter.mpr
      ⟨(hpartner y.1 y.2).choose_spec.1,
        ⟨y.1, Finset.mem_inter.mpr
          ⟨y.2, (hpartner y.1 y.2).choose_spec.2⟩⟩⟩⟩
  have hfinj : Function.Injective f := by
    intro y z hyz
    apply Subtype.ext
    have hfT : (f y).1 ∈ T :=
      Finset.mem_of_mem_erase (Finset.mem_filter.mp (f y).2).1
    have hfa : (f y).1 ≠ a :=
      Finset.ne_of_mem_erase (Finset.mem_filter.mp (f y).2).1
    apply Finset.card_le_one.mp (hlinear a haT (f y).1 hfT hfa.symm)
    · exact Finset.mem_inter.mpr
        ⟨y.2, (hpartner y.1 y.2).choose_spec.2⟩
    · exact Finset.mem_inter.mpr
        ⟨z.2, by
          have hfval : (f z).1 = (f y).1 :=
            congrArg Subtype.val hyz.symm
          rw [← hfval]
          exact (hpartner z.1 z.2).choose_spec.2⟩
  have hQcard : Q.card = m := by simpa [Q] using hdegree
  have hfsurj : Function.Surjective f :=
    (Fintype.bijective_iff_injective_and_card f).mpr
      ⟨hfinj, by simp [hcard a haT, hQcard]⟩ |>.2
  intro y hya
  let I := T.filter fun b => y ∈ B b
  have haI : a ∈ I := Finset.mem_filter.mpr ⟨haT, hya⟩
  have hsmall : (I.erase a).card ≤ 1 := Finset.card_le_one.mpr fun b hb c hc => by
    have hbData := Finset.mem_erase.mp hb
    have hcData := Finset.mem_erase.mp hc
    let qb : {b // b ∈ Q} := ⟨b, Finset.mem_filter.mpr
      ⟨Finset.mem_erase.mpr ⟨hbData.1, (Finset.mem_filter.mp hbData.2).1⟩,
        ⟨y, Finset.mem_inter.mpr ⟨hya, (Finset.mem_filter.mp hbData.2).2⟩⟩⟩⟩
    let qc : {b // b ∈ Q} := ⟨c, Finset.mem_filter.mpr
      ⟨Finset.mem_erase.mpr ⟨hcData.1, (Finset.mem_filter.mp hcData.2).1⟩,
        ⟨y, Finset.mem_inter.mpr ⟨hya, (Finset.mem_filter.mp hcData.2).2⟩⟩⟩⟩
    obtain ⟨yb, hyb⟩ := hfsurj qb
    obtain ⟨yc, hyc⟩ := hfsurj qc
    have hybEq : yb.1 = y := by
      apply Finset.card_le_one.mp
        (hlinear a haT b (Finset.mem_filter.mp hbData.2).1 hbData.1.symm)
      · exact Finset.mem_inter.mpr
          ⟨yb.2, by
            have : (f yb).1 = b := congrArg Subtype.val hyb
            rw [← this]
            exact (hpartner yb.1 yb.2).choose_spec.2⟩
      · exact Finset.mem_inter.mpr
          ⟨hya, (Finset.mem_filter.mp hbData.2).2⟩
    have hycEq : yc.1 = y := by
      apply Finset.card_le_one.mp
        (hlinear a haT c (Finset.mem_filter.mp hcData.2).1 hcData.1.symm)
      · exact Finset.mem_inter.mpr
          ⟨yc.2, by
            have : (f yc).1 = c := congrArg Subtype.val hyc
            rw [← this]
            exact (hpartner yc.1 yc.2).choose_spec.2⟩
      · exact Finset.mem_inter.mpr
          ⟨hya, (Finset.mem_filter.mp hcData.2).2⟩
    have hybyc : yb = yc := Subtype.ext (hybEq.trans hycEq.symm)
    have : qb = qc := hyb.symm.trans ((congrArg f hybyc).trans hyc)
    exact congrArg Subtype.val this
  have hIcard : I.card = (I.erase a).card + 1 := by
    have hIpos' : 0 < I.card := Finset.card_pos.mpr ⟨a, haI⟩
    rw [Finset.card_erase_of_mem haI]
    omega
  have hIEven : Even I.card := by simpa [I] using heven y
  have hIpos : 0 < I.card := Finset.card_pos.mpr ⟨a, haI⟩
  change I.card = 2
  rcases hIEven with ⟨k, hk⟩
  omega

set_option maxHeartbeats 800000 in
/-- Every shore point used by a row in an endpoint even configuration of size
`m+2` occurs on exactly two rows of that configuration. -/
theorem c4Free_binarySquare_pureEndpoint_evenConfiguration_eq_add_two_pointMultiplicity
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
    let row := fun w : W => G.neighborFinset w.1 ∩ S
    ∀ T : Finset W,
      (∀ y : P, Even ((T.filter fun w => G.Adj w.1 y.1).card)) →
      T.card = m + 2 →
      ∀ w ∈ T, ∀ y ∈ row w,
        (T.filter fun u => y ∈ row u).card = 2 := by
  classical
  dsimp only
  let F := fullLineCenters G S q
  let W := {w : V // w ∈ Fᶜ}
  let P := {y : V // y ∈ S}
  let row : W → Finset V := fun w => G.neighborFinset w.1 ∩ S
  intro T heven hTcard w hwT y hyrow
  have hdesign := c4Free_binarySquare_pureEndpoint_exterior_blockDesign
    G hfree hq hqm hreg hcard S hempty hCcard hshore htri
  have hrowCard : ∀ a ∈ T, (row a).card = m := by
    intro a _ha
    exact hdesign.1 a.1 (by simpa [F] using Finset.mem_compl.mp a.2)
  have hlinear : ∀ a ∈ T, ∀ b ∈ T, a ≠ b →
      ((row a) ∩ (row b)).card ≤ 1 := by
    intro a _ha b _hb hab
    simpa [row] using hdesign.2.1 a.1
      (by simpa [F] using Finset.mem_compl.mp a.2) b.1
      (by simpa [F] using Finset.mem_compl.mp b.2)
      (Subtype.coe_injective.ne hab)
  have hevenRow : ∀ z : V, Even ((T.filter fun a => z ∈ row a).card) := by
    intro z
    by_cases hzS : z ∈ S
    · let zz : P := ⟨z, hzS⟩
      have hsame : T.filter (fun a => z ∈ row a) =
          T.filter (fun a => G.Adj a.1 z) := by
        ext a
        simp [row, hzS, SimpleGraph.mem_neighborFinset]
      rw [hsame]
      simpa [zz] using heven zz
    · have hemptyFiber : T.filter (fun a => z ∈ row a) = ∅ := by
        ext a
        simp [row, hzS]
      simp [hemptyFiber]
  have hdegree :=
    (c4Free_binarySquare_pureEndpoint_evenConfiguration_eq_add_two_rigidity
      G hfree hq hqm hmEven hreg hcard S hempty hCcard hshore htri
      T heven hTcard w hwT).1
  exact linear_evenConfiguration_fiberCard_eq_two_of_internalDegree_eq_uniformCard
    row T m hrowCard hlinear hevenRow w hwT hdegree y hyrow

end

end Erdos85

#print axioms
  Erdos85.linear_evenConfiguration_fiberCard_eq_two_of_internalDegree_eq_uniformCard
#print axioms
  Erdos85.c4Free_binarySquare_pureEndpoint_evenConfiguration_eq_add_two_pointMultiplicity
