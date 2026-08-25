import Proofs.Erdos85PureEndpointStrictPrivateCutGap
import Proofs.Erdos85BinarySquareAdjacencySquareAction

/-!
# The strict-boundary trade is a defect-cut Laplacian

At equality in the private-cut gap, private replication is exactly zero,
one, or two.  Consequently its signed zero/heavy trade is not merely a
local incidence balance: globally it is the negative defect-Laplacian of
the private-shore indicator.
-/

open Finset SimpleGraph Matrix BigOperators

namespace Erdos85

noncomputable section

set_option maxHeartbeats 800000 in
theorem c4Free_binarySquare_pureEndpoint_privateCut_boundary_signedLaplacian
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) {q m : ℕ}
    (hq : 8 ≤ q) (hqm : q = 2 * m)
    (hreg : ∀ v, G.degree v = q)
    (hcard : Fintype.card V = q * q)
    (hconn : (secondOrderDefectGraph G).Preconnected)
    (S : Finset V) (hempty : emptyLineCenters G S = ∅)
    (hCcard : (fullLineCenters G S q).card = q)
    (hshore : 2 * S.card = q * q + q)
    (htri : ∀ v, (G.neighborFinset v ∩ S).card = 0 ∨
      (G.neighborFinset v ∩ S).card = m ∨
      (G.neighborFinset v ∩ S).card = q)
    (hcut : finsetGraphCutSize (secondOrderDefectGraph G)
      (S.filter fun p =>
        (G.neighborFinset p ∩ fullLineCenters G S q).card = 1) = 2 * q - 4) :
    let F := fullLineCenters G S q
    let P := S.filter fun p => (G.neighborFinset p ∩ F).card = 1
    let B := Fᶜ
    let r := fun b => (G.neighborFinset b ∩ P).card
    let Z := B.filter fun b => r b = 0
    let H := B.filter fun b => 1 < r b
    let p : V → ℤ := fun x => if x ∈ P then 1 else 0
    let v : V → ℤ := fun x =>
      (if x ∈ Z then 1 else 0) - (if x ∈ H then 1 else 0)
    (G.adjMatrix ℤ).mulVec p = (fun x => 1 - v x) ∧
      (G.adjMatrix ℤ).mulVec v =
        -((secondOrderDefectGraph G).lapMatrix ℤ).mulVec p := by
  classical
  dsimp only
  let F := fullLineCenters G S q
  let P := S.filter fun p => (G.neighborFinset p ∩ F).card = 1
  let B := Fᶜ
  let r := fun b => (G.neighborFinset b ∩ P).card
  let Z := B.filter fun b => r b = 0
  let H := B.filter fun b => 1 < r b
  let p : V → ℤ := fun x => if x ∈ P then 1 else 0
  let v : V → ℤ := fun x =>
    (if x ∈ Z then 1 else 0) - (if x ∈ H then 1 else 0)
  have hs :=
    (c4Free_binarySquare_pureEndpoint_privateCut_gap_boundary_rowProfile_and_saturation
      G hfree hq hqm hreg hcard hconn S hempty hCcard hshore htri).2 hcut
  have hfull : ∀ f ∈ F, r f = 1 := by
    intro f hf
    simpa [F, P, r] using
      c4Free_binarySquare_pureEndpoint_fullCenter_privateOccupancy_one
        G hfree hq hqm hreg hcard S hempty hCcard hshore htri f hf
  have hindicator : ∀ x,
      (G.adjMatrix ℤ).mulVec p x = (r x : ℤ) := by
    intro x
    rw [SimpleGraph.adjMatrix_mulVec_apply]
    change (∑ y ∈ G.neighborFinset x, if y ∈ P then (1 : ℤ) else 0) = _
    rw [← Finset.sum_filter]
    simp only [Finset.sum_const, nsmul_eq_mul, mul_one]
    congr 1
  have hfirst : (G.adjMatrix ℤ).mulVec p = fun x => 1 - v x := by
    funext x
    rw [hindicator]
    by_cases hxF : x ∈ F
    · have hxNotB : x ∉ B := by simpa [B] using hxF
      have hxNotZ : x ∉ Z := fun hx => hxNotB (Finset.mem_filter.mp hx).1
      have hxNotH : x ∉ H := fun hx => hxNotB (Finset.mem_filter.mp hx).1
      simp [v, hxNotZ, hxNotH, hfull x hxF]
    · have hxB : x ∈ B := by simpa [B] using hxF
      by_cases hr0 : r x = 0
      · have hxZ : x ∈ Z := Finset.mem_filter.mpr ⟨hxB, hr0⟩
        have hxNotH : x ∉ H := by simp [H, hr0]
        simp [v, hxZ, hxNotH, hr0]
      · by_cases hr1 : r x = 1
        · have hxNotZ : x ∉ Z := by simp [Z, hr1]
          have hxNotH : x ∉ H := by simp [H, hr1]
          simp [v, hxNotZ, hxNotH, hr1]
        · have hrgt : 1 < r x := by omega
          have hxH : x ∈ H := Finset.mem_filter.mpr ⟨hxB, hrgt⟩
          have hxNotZ : x ∉ Z := by
            intro hxZ
            exact hr0 (Finset.mem_filter.mp hxZ).2
          have hr2 : r x = 2 := by
            simpa [F, P, B, r, H] using hs.2.2.1 x hxH
          simp [v, hxH, hxNotZ, hr2]
  refine ⟨hfirst, ?_⟩
  let D := secondOrderDefectGraph G
  have hDreg : ∀ x, D.degree x = q - 1 := by
    intro x
    exact binarySquare_regular_secondOrderDefect_degree_eq
      G hfree (by omega) hreg hcard x
  funext x
  have hvpoint : ∀ y, v y = 1 - (G.adjMatrix ℤ).mulVec p y := by
    intro y
    have := congrFun hfirst y
    omega
  rw [SimpleGraph.adjMatrix_mulVec_apply]
  rw [show (∑ y ∈ G.neighborFinset x, v y) =
      ∑ y ∈ G.neighborFinset x,
        (1 - (G.adjMatrix ℤ).mulVec p y) by
    apply Finset.sum_congr rfl
    intro y _hy
    exact hvpoint y]
  rw [Finset.sum_sub_distrib]
  have hsq := binarySquare_regular_adjMatrix_sq_mulVec_apply
    G hfree hreg p x
  have hsumP : ∑ y, p y = (q : ℤ) := by
    simp [p]
    simpa [P, F] using
      (c4Free_binarySquare_pureEndpoint_fullLineCenters_exactReplicationProfile
        G hfree hq hqm hreg hcard S hempty hCcard hshore htri).2.1
  have hAA :
      ∑ y ∈ G.neighborFinset x, (G.adjMatrix ℤ).mulVec p y =
        ((G.adjMatrix ℤ * G.adjMatrix ℤ).mulVec p) x := by
    rw [← Matrix.mulVec_mulVec, SimpleGraph.adjMatrix_mulVec_apply]
  rw [hAA, hsq, hsumP]
  simp only [Finset.sum_const, nsmul_eq_mul,
    G.card_neighborFinset_eq_degree, hreg x]
  change _ = -((D.lapMatrix ℤ).mulVec p x)
  rw [D.lapMatrix_mulVec_apply, hDreg]
  dsimp only [D]
  rw [Nat.cast_sub (by omega : 1 ≤ q)]
  ring

end

end Erdos85

#print axioms Erdos85.c4Free_binarySquare_pureEndpoint_privateCut_boundary_signedLaplacian
