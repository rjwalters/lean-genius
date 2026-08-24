import Proofs.Erdos85PureEndpointExteriorNearParallelDesign

/-!
# The exterior block design at a pure endpoint

Exterior vertices define uniform half-size blocks on the shore.  C4-freeness
makes these blocks a two-packing, while the one/two owner profile gives the
exact replication number of every shore point.
-/

open Finset SimpleGraph

namespace Erdos85

noncomputable section

/-- The exterior neighbor rows form a `q/2`-uniform packing on the shore.
Every shore point of owner multiplicity `r ∈ {1,2}` occurs in exactly `q-r`
exterior rows. -/
theorem c4Free_binarySquare_pureEndpoint_exterior_blockDesign
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
    let B := fun w => G.neighborFinset w ∩ S
    let owner := fun y => G.neighborFinset y ∩ F
    (∀ w ∉ F, (B w).card = m) ∧
    (∀ w ∉ F, ∀ w' ∉ F, w ≠ w' →
      ((B w) ∩ (B w')).card ≤ 1) ∧
    ∀ y ∈ S,
      ((owner y).card = 1 ∨ (owner y).card = 2) ∧
      (G.neighborFinset y ∩ Fᶜ).card = q - (owner y).card := by
  classical
  dsimp only
  let F := fullLineCenters G S q
  let B : V → Finset V := fun w => G.neighborFinset w ∩ S
  let owner : V → Finset V := fun y => G.neighborFinset y ∩ F
  have hprofile :=
    (c4Free_binarySquare_pureEndpoint_fullLineCenters_exactReplicationProfile
      G hfree hq hqm hreg hcard S hempty hCcard hshore htri).1
  refine ⟨?_, ?_, ?_⟩
  · intro w hwF
    rcases htri w with hzero | hhalf | hfull
    · have hwEmpty : w ∈ emptyLineCenters G S :=
        (mem_emptyLineCenters G S w).mpr hzero
      rw [hempty] at hwEmpty
      simp at hwEmpty
    · simpa [B] using hhalf
    · exact (hwF ((mem_fullLineCenters G S q w).mpr hfull)).elim
  · intro w _hwF w' _hw'F hww'
    apply Finset.card_le_one.mpr
    intro y hy z hz
    by_contra hyz
    apply hfree
    apply containsC4_of_two_common hww' hyz
    · exact (G.mem_neighborFinset w y).mp
        (Finset.mem_inter.mp (Finset.mem_inter.mp hy).1).1 |>.symm
    · exact (G.mem_neighborFinset w' y).mp
        (Finset.mem_inter.mp (Finset.mem_inter.mp hy).2).1 |>.symm
    · exact (G.mem_neighborFinset w z).mp
        (Finset.mem_inter.mp (Finset.mem_inter.mp hz).1).1 |>.symm
    · exact (G.mem_neighborFinset w' z).mp
        (Finset.mem_inter.mp (Finset.mem_inter.mp hz).2).1 |>.symm
  · intro y hyS
    have hyProfile := (hprofile y).mp hyS
    refine ⟨by simpa [owner, F] using hyProfile, ?_⟩
    have hdisj : Disjoint (G.neighborFinset y ∩ F)
        (G.neighborFinset y ∩ Fᶜ) := by
      exact Finset.disjoint_left.mpr fun x hxF hxFc =>
        (Finset.mem_compl.mp (Finset.mem_inter.mp hxFc).2)
          (Finset.mem_inter.mp hxF).2
    have hunion : (G.neighborFinset y ∩ F) ∪
        (G.neighborFinset y ∩ Fᶜ) = G.neighborFinset y := by
      ext x
      by_cases hx : x ∈ F <;> simp [hx]
    have hcards := Finset.card_union_of_disjoint hdisj
    rw [hunion, G.card_neighborFinset_eq_degree, hreg] at hcards
    simpa [owner, F] using (show
      (G.neighborFinset y ∩ Fᶜ).card =
        q - (G.neighborFinset y ∩ F).card by omega)

end

end Erdos85

#print axioms Erdos85.c4Free_binarySquare_pureEndpoint_exterior_blockDesign
