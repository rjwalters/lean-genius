import Proofs.Erdos85PureEndpointExteriorEvenConfigurationEqAddThreeLocalMultiplicity

/-! # Endpoint wrapper for `m+3` local multiplicity rigidity -/

open Finset BigOperators

namespace Erdos85

noncomputable section

set_option maxHeartbeats 800000

theorem c4Free_binarySquare_pureEndpoint_evenConfiguration_eq_add_three_localMultiplicity
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
      ((((T.erase w).filter fun u =>
          ¬ (row w ∩ row u).Nonempty).card = 2 ∧
        ∀ y ∈ row w, (T.filter fun u => y ∈ row u).card = 2) ∨
       (((T.erase w).filter fun u =>
          ¬ (row w ∩ row u).Nonempty).card = 0 ∧
        ∃! y, y ∈ row w ∧ (T.filter fun u => y ∈ row u).card = 4 ∧
          ∀ z ∈ row w, z ≠ y →
            (T.filter fun u => z ∈ row u).card = 2)) := by
  classical
  dsimp only
  let F := fullLineCenters G S q
  let W := {w : V // w ∈ Fᶜ}
  let P := {y : V // y ∈ S}
  let row : W → Finset V := fun w => G.neighborFinset w.1 ∩ S
  intro T heven hTcard w hw
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
  have hmissing :=
    c4Free_binarySquare_pureEndpoint_evenConfiguration_eq_add_three_complementDegree
      G hfree hq hqm hmEven hreg hcardV S hempty hCcard hshore htri
      T heven hTcard w hw
  have hmissingRow :
      ((T.erase w).filter fun u => ¬ (row w ∩ row u).Nonempty).card = 0 ∨
      ((T.erase w).filter fun u => ¬ (row w ∩ row u).Nonempty).card = 2 := by
    change ((T.erase w).filter fun u =>
      ¬ ((G.neighborFinset w.1 ∩ S) ∩
        (G.neighborFinset u.1 ∩ S)).Nonempty).card = 0 ∨
      ((T.erase w).filter fun u =>
      ¬ ((G.neighborFinset w.1 ∩ S) ∩
        (G.neighborFinset u.1 ∩ S)).Nonempty).card = 2
    simpa only [inter_assoc] using hmissing
  exact linear_even_configuration_eq_add_three_localMultiplicity
    row T w m hw hrowCard hTcard hevenV hlinear hmissingRow

end

end Erdos85

#print axioms
  Erdos85.c4Free_binarySquare_pureEndpoint_evenConfiguration_eq_add_three_localMultiplicity
