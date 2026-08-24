import Proofs.Erdos85PureEndpointOffShorePairRouting

/-!
# Partner-center routing of off-shore endpoint centers

The replication-two point on the private triangle of an off-shore center
has one further exceptional owner.  This file exposes that owner explicitly
as a distinct partner center.
-/

open Finset SimpleGraph

namespace Erdos85

noncomputable section

/-- Every off-shore full center has a private shore point and a pair shore
point whose exceptional owners are exactly the center and one distinct
partner center. -/
theorem c4Free_binarySquare_pureEndpoint_offShore_partnerCenter_route
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
    ∀ i : {i // i ∈ fullLineCenters G S q}, i.1 ∉ S →
      ∃ j : {j // j ∈ fullLineCenters G S q}, ∃ p z,
        j ≠ i ∧ p ∈ S ∧ z ∈ S ∧
        G.Adj i.1 p ∧
        G.neighborFinset p ∩ fullLineCenters G S q = {i.1} ∧
        G.Adj i.1 z ∧ G.Adj p z ∧
        G.neighborFinset z ∩ fullLineCenters G S q = {i.1, j.1} := by
  classical
  intro i hiOff
  obtain ⟨p, z, hpS, hzS, hip, hpPrivate, hiz, hpz, hzTwo⟩ :=
    c4Free_binarySquare_pureEndpoint_offShore_pairPoint_route
      G hfree hq hqm hreg hcard S hempty hCcard hshore htri i hiOff
  let C := fullLineCenters G S q
  have hiMem : i.1 ∈ G.neighborFinset z ∩ C :=
    Finset.mem_inter.mpr ⟨by
      simpa [SimpleGraph.mem_neighborFinset] using hiz.symm, i.2⟩
  obtain ⟨a, b, hab, hzPair⟩ := Finset.card_eq_two.mp (by simpa [C] using hzTwo)
  have hiPair : i.1 = a ∨ i.1 = b := by
    rw [hzPair] at hiMem
    simpa using hiMem
  rcases hiPair with hia | hib
  · let j : {j // j ∈ C} := ⟨b, by
      have hb : b ∈ G.neighborFinset z ∩ C := by rw [hzPair]; simp
      exact (Finset.mem_inter.mp hb).2⟩
    have hji : j ≠ i := by
      intro hji
      have hbi : b = i.1 := congrArg Subtype.val hji
      exact hab (hia.symm.trans hbi.symm)
    refine ⟨j, p, z, hji, hpS, hzS, hip, hpPrivate, hiz, hpz, ?_⟩
    simpa [C, j, hia] using hzPair
  · let j : {j // j ∈ C} := ⟨a, by
      have ha : a ∈ G.neighborFinset z ∩ C := by rw [hzPair]; simp
      exact (Finset.mem_inter.mp ha).2⟩
    have hji : j ≠ i := by
      intro hji
      have hai : a = i.1 := congrArg Subtype.val hji
      exact hab (hai.trans hib)
    refine ⟨j, p, z, hji, hpS, hzS, hip, hpPrivate, hiz, hpz, ?_⟩
    rw [show G.neighborFinset z ∩ fullLineCenters G S q = {a, b} by
      simpa [C] using hzPair]
    simp [j, hib, Finset.pair_comm]

end

end Erdos85

#print axioms Erdos85.c4Free_binarySquare_pureEndpoint_offShore_partnerCenter_route
