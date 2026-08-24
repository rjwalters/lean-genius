import Proofs.Erdos85PureEndpointExteriorEvenConfigurationEqAddTwoPairMultiplicity
import Proofs.Erdos85PureEndpointExteriorEvenConfigurationPrivateSupport

/-!
# Private support of an `m+2` circuit

Degree-two incidence makes total singleton-owner incidence exactly twice the
number of distinct singleton-owner points used.  At the endpoint this is the
total center-hole mass, giving the uniform cap `2q = 4m`.
-/

open Finset SimpleGraph BigOperators

namespace Erdos85

noncomputable section

/-- A degree-two incidence relation has total incidence twice the size of
its used support. -/
theorem degreeTwo_incidence_total_eq_two_support
    {α β : Type*} [DecidableEq α] [DecidableEq β]
    (Inc : α → β → Prop) [DecidableRel Inc]
    (T : Finset α) (L : Finset β)
    (hpoint : ∀ y ∈ L, (T.filter fun a => Inc a y).Nonempty →
      (T.filter fun a => Inc a y).card = 2) :
    (∑ a ∈ T, (L.filter fun y => Inc a y).card) =
      2 * (L.filter fun y => (T.filter fun a => Inc a y).Nonempty).card := by
  classical
  calc
    (∑ a ∈ T, (L.filter fun y => Inc a y).card) =
        ∑ a ∈ T, ∑ y ∈ L, if Inc a y then 1 else 0 := by
      apply Finset.sum_congr rfl
      intro a _ha
      rw [Finset.card_filter]
    _ = ∑ y ∈ L, ∑ a ∈ T, if Inc a y then 1 else 0 := by
      rw [Finset.sum_comm]
    _ = ∑ y ∈ L, (T.filter fun a => Inc a y).card := by
      apply Finset.sum_congr rfl
      intro y _hy
      rw [Finset.card_filter]
    _ = ∑ y ∈ L,
        if (T.filter fun a => Inc a y).Nonempty then 2 else 0 := by
      apply Finset.sum_congr rfl
      intro y hy
      by_cases hu : (T.filter fun a => Inc a y).Nonempty
      · simp [hu, hpoint y hy hu]
      · have hz : T.filter (fun a => Inc a y) = ∅ :=
          Finset.not_nonempty_iff_eq_empty.mp hu
        simp [hz]
    _ = 2 * (L.filter fun y =>
        (T.filter fun a => Inc a y).Nonempty).card := by
      rw [← Finset.sum_filter]
      simp [Nat.mul_comm]

set_option maxHeartbeats 800000 in
/-- For an endpoint `m+2` even configuration, total center-hole mass is
twice its used singleton-owner support and is at most `2q = 4m`. -/
theorem c4Free_binarySquare_pureEndpoint_evenConfiguration_eq_add_two_privateSupport
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
    let R₁ := S.filter fun y => (owner y).card = 1
    ∀ T : Finset W,
      (∀ y : P, Even ((T.filter fun w => G.Adj w.1 y.1).card)) →
      T.card = m + 2 →
      let U := R₁.filter fun y =>
        (T.filter fun w => G.Adj w.1 y).Nonempty
      R₁.card = q ∧
        (∑ w ∈ T,
          ((secondOrderDefectGraph G).neighborFinset w.1 ∩ F).card) =
            2 * U.card ∧
        (∑ w ∈ T,
          ((secondOrderDefectGraph G).neighborFinset w.1 ∩ F).card) ≤
            2 * q := by
  classical
  dsimp only
  let F := fullLineCenters G S q
  let W := {w : V // w ∈ Fᶜ}
  let P := {y : V // y ∈ S}
  let owner : V → Finset V := fun y => G.neighborFinset y ∩ F
  let R₁ := S.filter fun y => (owner y).card = 1
  intro T heven hTcard
  let U := R₁.filter fun y =>
    (T.filter fun w => G.Adj w.1 y).Nonempty
  have hnear := c4Free_binarySquare_pureEndpoint_exterior_nearParallelDesign
    G hfree hq hqm hreg hcard S hempty hCcard hshore htri
  have hpointOnRow :=
    c4Free_binarySquare_pureEndpoint_evenConfiguration_eq_add_two_pointMultiplicity
      G hfree hq hqm hmEven hreg hcard S hempty hCcard hshore htri
      T heven hTcard
  have husedTwo : ∀ y ∈ R₁,
      (T.filter fun w => G.Adj w.1 y).Nonempty →
      (T.filter fun w => G.Adj w.1 y).card = 2 := by
    intro y hyR hyUsed
    obtain ⟨w, hw⟩ := hyUsed
    have hwData := Finset.mem_filter.mp hw
    have hyS := (Finset.mem_filter.mp hyR).1
    have hyRow : y ∈ G.neighborFinset w.1 ∩ S :=
      Finset.mem_inter.mpr
        ⟨(G.mem_neighborFinset w.1 y).mpr hwData.2, hyS⟩
    simpa [SimpleGraph.mem_neighborFinset, hyS] using
      hpointOnRow w hwData.1 y hyRow
  have hpoint : ∀ w : W,
      ((secondOrderDefectGraph G).neighborFinset w.1 ∩ F).card =
        (R₁.filter fun y => G.Adj w.1 y).card := by
    intro w
    have hwF : w.1 ∉ F := Finset.mem_compl.mp w.2
    have hbase := (hnear w.1 hwF).2.1
    rw [show R₁.filter (fun y => G.Adj w.1 y) =
        G.neighborFinset w.1 ∩ R₁ by
      ext y
      simp [SimpleGraph.mem_neighborFinset, and_comm]]
    simpa [F, owner, R₁] using hbase
  have hmassEq : (∑ w ∈ T,
      ((secondOrderDefectGraph G).neighborFinset w.1 ∩ F).card) =
        2 * U.card := by
    rw [Finset.sum_congr rfl (fun w _hw => hpoint w)]
    exact degreeTwo_incidence_total_eq_two_support
      (fun w y => G.Adj w.1 y) T R₁ husedTwo
  have hR₁card : R₁.card = q := by
    simpa [R₁, owner, F] using
      (c4Free_binarySquare_pureEndpoint_fullLineCenters_exactReplicationProfile
        G hfree hq hqm hreg hcard S hempty hCcard hshore htri).2.1
  have hUle : U.card ≤ R₁.card := Finset.card_filter_le _ _
  refine ⟨hR₁card, hmassEq, ?_⟩
  rw [hmassEq, ← hR₁card]
  omega

end

end Erdos85

#print axioms Erdos85.degreeTwo_incidence_total_eq_two_support
#print axioms
  Erdos85.c4Free_binarySquare_pureEndpoint_evenConfiguration_eq_add_two_privateSupport
