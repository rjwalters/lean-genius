import Proofs.Erdos85PureEndpointExteriorEvenConfigurationCenterHoleParity
import Proofs.Erdos85PureEndpointExteriorEvenConfigurationEquality

/-!
# Private support of an equality circuit

Equality rigidity says that every shore point used by an exterior circuit is
used by exactly two circuit rows.  Since the holes of a row are exactly its
singleton-owner shore points, total hole mass is twice the number of distinct
private shore points met by the circuit.  Centerwise hole parity then forces
the circuit to meet at least half of the private layer.
-/

open Finset SimpleGraph BigOperators

namespace Erdos85

noncomputable section

/-- In an even-`m` equality circuit, hole mass is exactly twice the number of
distinct singleton-owner shore points used by the circuit; consequently at
least `m` such points are used. -/
theorem c4Free_binarySquare_pureEndpoint_evenConfiguration_eq_succ_privateSupport
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
      T.card = m + 1 →
      let U := R₁.filter fun y => (T.filter fun w => G.Adj w.1 y).Nonempty
      R₁.card = q ∧
        (∑ w ∈ T,
          ((secondOrderDefectGraph G).neighborFinset w.1 ∩ F).card) =
            2 * U.card ∧
        m ≤ U.card := by
  classical
  dsimp only
  let F := fullLineCenters G S q
  let W := {w : V // w ∈ Fᶜ}
  let P := {y : V // y ∈ S}
  let owner : V → Finset V := fun y => G.neighborFinset y ∩ F
  let R₁ := S.filter fun y => (owner y).card = 1
  intro T heven hTcard
  let B : W → Finset V := fun w => G.neighborFinset w.1 ∩ S
  let U := R₁.filter fun y => (T.filter fun w => G.Adj w.1 y).Nonempty
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
  have husedTwo : ∀ y ∈ R₁,
      (T.filter fun w => G.Adj w.1 y).Nonempty →
      (T.filter fun w => G.Adj w.1 y).card = 2 := by
    intro y hyR hyUsed
    have hyS : y ∈ S := (Finset.mem_filter.mp hyR).1
    have hsame : (T.filter fun w => G.Adj w.1 y) =
        T.filter fun w => y ∈ B w := by
      ext w
      simp [B, hyS, SimpleGraph.mem_neighborFinset]
    rw [hsame]
    exact hrigid.2 y (hsame ▸ hyUsed)
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
  have hsupport : (∑ y ∈ R₁,
      (T.filter fun w => G.Adj w.1 y).card) = 2 * U.card := by
    rw [show U.card = ∑ y ∈ R₁,
        if (T.filter fun w => G.Adj w.1 y).Nonempty then 1 else 0 by
      rw [Finset.card_filter]]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro y hyR
    by_cases hyUsed : (T.filter fun w => G.Adj w.1 y).Nonempty
    · simp [hyUsed, husedTwo y hyR hyUsed]
    · have hyEmpty : T.filter (fun w => G.Adj w.1 y) = ∅ :=
        Finset.not_nonempty_iff_eq_empty.mp hyUsed
      simp [hyUsed, hyEmpty]
  have hmassEq : (∑ w ∈ T,
      ((secondOrderDefectGraph G).neighborFinset w.1 ∩ F).card) =
        2 * U.card := by
    rw [Finset.sum_congr rfl (fun w _hw => hpoint w), hswap, hsupport]
  have hR₁card : R₁.card = q := by
    simpa [R₁, owner, F] using
      (c4Free_binarySquare_pureEndpoint_fullLineCenters_exactReplicationProfile
        G hfree hq hqm hreg hcard S hempty hCcard hshore htri).2.1
  refine ⟨hR₁card, hmassEq, ?_⟩
  have hmassLower :=
    (c4Free_binarySquare_pureEndpoint_evenConfiguration_eq_succ_centerHoleParity
      G hfree hq hqm hmEven hreg hcard S hempty hCcard hshore htri
      T heven hTcard).2
  rw [hmassEq, hqm] at hmassLower
  change m ≤ U.card
  omega

end

end Erdos85

#print axioms
  Erdos85.c4Free_binarySquare_pureEndpoint_evenConfiguration_eq_succ_privateSupport
