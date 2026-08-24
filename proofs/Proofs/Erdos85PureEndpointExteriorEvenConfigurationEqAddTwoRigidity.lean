import Proofs.Erdos85PureEndpointExteriorMinimalCircuitEulerian

/-!
# Rigidity of an `m+2` row circuit

Every row in a linear `m`-uniform even configuration meets at least `m`
other rows.  At size `m+2`, the endpoint internal-degree parity forces this
degree to be exactly `m`; consequently every row has a unique nonpartner.
Thus the row-intersection graph is a complete graph minus a perfect matching.
-/

open Finset SimpleGraph BigOperators

namespace Erdos85

noncomputable section

/-- A row of a linear uniform even configuration meets at least one distinct
partner through each of its points, and these chosen partners are distinct. -/
theorem linear_evenConfiguration_internalDegree_ge_uniformCard
    {α β : Type*} [DecidableEq α] [DecidableEq β]
    (B : α → Finset β) (T : Finset α) (m : ℕ)
    (hcard : ∀ a ∈ T, (B a).card = m)
    (hlinear : ∀ a ∈ T, ∀ b ∈ T, a ≠ b →
      ((B a) ∩ (B b)).card ≤ 1)
    (heven : ∀ y : β, Even ((T.filter fun a => y ∈ B a).card)) :
    ∀ a ∈ T, m ≤ ((T.erase a).filter fun b => (B a ∩ B b).Nonempty).card := by
  classical
  intro a haT
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
  have hle : (B a).card ≤ Q.card :=
    Finset.card_le_card_of_injective hfinj
  simpa [Q, hcard a haT] using hle

set_option maxHeartbeats 800000 in
/-- An endpoint even configuration of size `m+2` has internal degree `m` at
every row and exactly one nonmeeting partner per row. -/
theorem c4Free_binarySquare_pureEndpoint_evenConfiguration_eq_add_two_rigidity
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
      ∀ w ∈ T,
        ((T.erase w).filter fun u => (row w ∩ row u).Nonempty).card = m ∧
        ((T.erase w).filter fun u => ¬(row w ∩ row u).Nonempty).card = 1 := by
  classical
  dsimp only
  let F := fullLineCenters G S q
  let W := {w : V // w ∈ Fᶜ}
  let P := {y : V // y ∈ S}
  let row : W → Finset V := fun w => G.neighborFinset w.1 ∩ S
  intro T heven hTcard w hwT
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
  have hevenRow : ∀ y : V, Even ((T.filter fun a => y ∈ row a).card) := by
    intro y
    by_cases hyS : y ∈ S
    · let yy : P := ⟨y, hyS⟩
      have hsame : T.filter (fun a => y ∈ row a) =
          T.filter (fun a => G.Adj a.1 y) := by
        ext a
        simp [row, hyS, SimpleGraph.mem_neighborFinset]
      rw [hsame]
      simpa [yy] using heven yy
    · have hemptyFiber : T.filter (fun a => y ∈ row a) = ∅ := by
        ext a
        simp [row, hyS]
      simp [hemptyFiber]
  let Q := (T.erase w).filter fun u => (row w ∩ row u).Nonempty
  let R := (T.erase w).filter fun u => ¬(row w ∩ row u).Nonempty
  have hlow : m ≤ Q.card := by
    simpa [Q] using linear_evenConfiguration_internalDegree_ge_uniformCard
      row T m hrowCard hlinear hevenRow w hwT
  have hupp : Q.card ≤ m + 1 := by
    calc
      Q.card ≤ (T.erase w).card := Finset.card_filter_le _ _
      _ = m + 1 := by rw [Finset.card_erase_of_mem hwT, hTcard]; omega
  have hQEven : Even Q.card := by
    simpa [Q, row, F] using
      c4Free_binarySquare_pureEndpoint_evenConfiguration_internalDegreeEven
        G hfree hq hqm hmEven hreg hcard S hempty hCcard hshore htri
        T heven w hwT
  have hQcard : Q.card = m := by
    rcases hmEven with ⟨a, ha⟩
    rcases hQEven with ⟨b, hb⟩
    omega
  have hpartition : Q.card + R.card = (T.erase w).card := by
    simpa [Q, R] using
      (Finset.card_filter_add_card_filter_not
        (s := T.erase w) (fun u => (row w ∩ row u).Nonempty))
  refine ⟨?_, ?_⟩
  · change Q.card = m
    exact hQcard
  change R.card = 1
  rw [Finset.card_erase_of_mem hwT, hTcard] at hpartition
  omega

end

end Erdos85

#print axioms Erdos85.linear_evenConfiguration_internalDegree_ge_uniformCard
#print axioms
  Erdos85.c4Free_binarySquare_pureEndpoint_evenConfiguration_eq_add_two_rigidity
