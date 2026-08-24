import Proofs.Erdos85PureEndpointExteriorEvenConfigurationGirth
import Proofs.Erdos85PureEndpointExteriorNearParallelDesign
import Proofs.Erdos85PureEndpointExteriorEvenConfigurationParallelParity

/-!
# Defect-mass parity of an exterior even configuration

The hole count of an exterior row equals its number of singleton-owner shore
points.  Summing over an even row configuration and swapping incidences shows
that its total hole mass is even.
-/

open Finset SimpleGraph BigOperators

namespace Erdos85

noncomputable section

/-- Every exterior row configuration with even incidence at every shore
point has even total full-center defect-hole mass. -/
theorem c4Free_binarySquare_pureEndpoint_even_exteriorRowConfiguration_holeParity
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
    ∀ T : Finset W,
      (∀ y : P, Even ((T.filter fun w => G.Adj w.1 y.1).card)) →
      Even (∑ w ∈ T,
        ((secondOrderDefectGraph G).neighborFinset w.1 ∩ F).card) := by
  classical
  dsimp only
  let F := fullLineCenters G S q
  let W := {w : V // w ∈ Fᶜ}
  let P := {y : V // y ∈ S}
  let owner : V → Finset V := fun y => G.neighborFinset y ∩ F
  let R₁ := S.filter fun y => (owner y).card = 1
  intro T heven
  have hnear := c4Free_binarySquare_pureEndpoint_exterior_nearParallelDesign
    G hfree hq hqm hreg hcard S hempty hCcard hshore htri
  have hpoint : ∀ w : W,
      ((secondOrderDefectGraph G).neighborFinset w.1 ∩ F).card =
        (G.neighborFinset w.1 ∩ R₁).card := by
    intro w
    have hwF : w.1 ∉ F := Finset.mem_compl.mp w.2
    simpa [F, owner, R₁] using (hnear w.1 hwF).2.1
  have hswap :
      (∑ w ∈ T, (G.neighborFinset w.1 ∩ R₁).card) =
        ∑ y ∈ R₁, (T.filter fun w => G.Adj w.1 y).card := by
    calc
      (∑ w ∈ T, (G.neighborFinset w.1 ∩ R₁).card) =
          ∑ w ∈ T, ∑ y ∈ R₁, if G.Adj w.1 y then 1 else 0 := by
        apply Finset.sum_congr rfl
        intro w _hw
        rw [show G.neighborFinset w.1 ∩ R₁ =
            R₁.filter (fun y => G.Adj w.1 y) by
          ext y
          simp [SimpleGraph.mem_neighborFinset, and_comm]]
        rw [Finset.card_filter]
      _ = ∑ y ∈ R₁, ∑ w ∈ T, if G.Adj w.1 y then 1 else 0 := by
        rw [Finset.sum_comm]
      _ = ∑ y ∈ R₁, (T.filter fun w => G.Adj w.1 y).card := by
        apply Finset.sum_congr rfl
        intro y _hy
        rw [Finset.card_filter]
  have hrightEven : Even
      (∑ y ∈ R₁, (T.filter fun w => G.Adj w.1 y).card) := by
    apply Finset.even_sum
    intro y hyR₁
    let yy : P := ⟨y, (Finset.mem_filter.mp hyR₁).1⟩
    simpa [yy] using heven yy
  rw [Finset.sum_congr rfl (fun w _hw => hpoint w), hswap]
  exact hrightEven

/-- A pure endpoint has a large nonempty even exterior-row configuration
whose total number of full-center defect incidences is even. -/
theorem c4Free_binarySquare_pureEndpoint_exists_large_even_exteriorRowConfiguration_holeParity
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
    ∃ T : Finset W, T.Nonempty ∧ m + 1 ≤ T.card ∧
      (∀ y : P, Even ((T.filter fun w => G.Adj w.1 y.1).card)) ∧
      Even (∑ w ∈ T,
        ((secondOrderDefectGraph G).neighborFinset w.1 ∩ F).card) := by
  classical
  dsimp only
  let F := fullLineCenters G S q
  let W := {w : V // w ∈ Fᶜ}
  let P := {y : V // y ∈ S}
  let owner : V → Finset V := fun y => G.neighborFinset y ∩ F
  let R₁ := S.filter fun y => (owner y).card = 1
  obtain ⟨T, hT, hlarge, heven⟩ :=
    c4Free_binarySquare_pureEndpoint_exists_large_even_exteriorRowConfiguration
      G hfree hq hqm hreg hcard S hempty hCcard hshore htri
  have hnear := c4Free_binarySquare_pureEndpoint_exterior_nearParallelDesign
    G hfree hq hqm hreg hcard S hempty hCcard hshore htri
  have hpoint : ∀ w : W,
      ((secondOrderDefectGraph G).neighborFinset w.1 ∩ F).card =
        (G.neighborFinset w.1 ∩ R₁).card := by
    intro w
    have hwF : w.1 ∉ F := Finset.mem_compl.mp w.2
    simpa [F, owner, R₁] using (hnear w.1 hwF).2.1
  have hswap :
      (∑ w ∈ T, (G.neighborFinset w.1 ∩ R₁).card) =
        ∑ y ∈ R₁, (T.filter fun w => G.Adj w.1 y).card := by
    calc
      (∑ w ∈ T, (G.neighborFinset w.1 ∩ R₁).card) =
          ∑ w ∈ T, ∑ y ∈ R₁, if G.Adj w.1 y then 1 else 0 := by
        apply Finset.sum_congr rfl
        intro w _hw
        rw [show G.neighborFinset w.1 ∩ R₁ =
            R₁.filter (fun y => G.Adj w.1 y) by
          ext y
          simp [SimpleGraph.mem_neighborFinset, and_comm]]
        rw [Finset.card_filter]
      _ = ∑ y ∈ R₁, ∑ w ∈ T, if G.Adj w.1 y then 1 else 0 := by
        rw [Finset.sum_comm]
      _ = ∑ y ∈ R₁, (T.filter fun w => G.Adj w.1 y).card := by
        apply Finset.sum_congr rfl
        intro y _hy
        rw [Finset.card_filter]
  have hrightEven : Even
      (∑ y ∈ R₁, (T.filter fun w => G.Adj w.1 y).card) := by
    apply Finset.even_sum
    intro y hyR₁
    let yy : P := ⟨y, (Finset.mem_filter.mp hyR₁).1⟩
    simpa [yy] using heven yy
  refine ⟨T, hT, hlarge, heven, ?_⟩
  rw [Finset.sum_congr rfl (fun w _hw => hpoint w), hswap]
  exact hrightEven

/-- When `m` is even, every equality-size even exterior configuration has
total defect-hole mass at least two. -/
theorem c4Free_binarySquare_pureEndpoint_evenConfiguration_eq_succ_holeMass_two_le
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
    ∀ T : Finset W,
      (∀ y : P, Even ((T.filter fun w => G.Adj w.1 y.1).card)) →
      T.card = m + 1 →
      2 ≤ ∑ w ∈ T,
        ((secondOrderDefectGraph G).neighborFinset w.1 ∩ F).card := by
  classical
  dsimp only
  intro T heven hTcard
  have hpos :=
    c4Free_binarySquare_pureEndpoint_evenConfiguration_eq_succ_exists_hole
      G hfree hq hqm hmEven hreg hcard S hempty hCcard hshore htri
      T heven hTcard
  have hsumPos : 0 < ∑ w ∈ T,
      ((secondOrderDefectGraph G).neighborFinset w.1 ∩
        fullLineCenters G S q).card := by
    obtain ⟨w, hwT, hwPos⟩ := hpos
    exact Finset.sum_pos' (fun _ _ => Nat.zero_le _)
      ⟨w, hwT, hwPos⟩
  have hsumEven :=
    c4Free_binarySquare_pureEndpoint_even_exteriorRowConfiguration_holeParity
      G hfree hq hqm hreg hcard S hempty hCcard hshore htri T heven
  rcases hsumEven with ⟨k, hk⟩
  omega

end

end Erdos85

#print axioms
  Erdos85.c4Free_binarySquare_pureEndpoint_even_exteriorRowConfiguration_holeParity
#print axioms
  Erdos85.c4Free_binarySquare_pureEndpoint_exists_large_even_exteriorRowConfiguration_holeParity
#print axioms
  Erdos85.c4Free_binarySquare_pureEndpoint_evenConfiguration_eq_succ_holeMass_two_le
