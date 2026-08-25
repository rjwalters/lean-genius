import Proofs.Erdos85MinimumDefectCutBalancedCenteredRow
import Proofs.Erdos85PureEndpointFinalLayerPrivateMatching

/-!
# Private-row profile at a minimum pure-endpoint defect cut

The replication-one shore points form the canonical private set of size `q`.
If its second-order-defect boundary has the minimum possible even size `q`,
the generic centered-row classifier says that exactly half of all rows miss
the private set and exactly half contain two private points.
-/

open Finset SimpleGraph

namespace Erdos85

noncomputable section

/-- At a pure endpoint whose private set has defect cut `q`, precisely `q/2`
rows contain zero private points and precisely `q/2` rows contain two. -/
theorem c4Free_binarySquare_pureEndpoint_minimumPrivateCut_rowProfile
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) {q m : ℕ}
    (hq : 8 ≤ q) (hqm : q = 2 * m) (hfour : 4 ∣ q)
    (hreg : ∀ v, G.degree v = q)
    (hcard : Fintype.card V = q * q)
    (S : Finset V)
    (hempty : emptyLineCenters G S = ∅)
    (hCcard : (fullLineCenters G S q).card = q)
    (hshore : 2 * S.card = q * q + q)
    (htri : ∀ v,
      (G.neighborFinset v ∩ S).card = 0 ∨
      (G.neighborFinset v ∩ S).card = m ∨
      (G.neighborFinset v ∩ S).card = q)
    (hcut : finsetGraphCutSize (secondOrderDefectGraph G)
      (S.filter fun x =>
        (G.neighborFinset x ∩ fullLineCenters G S q).card = 1) = q) :
    let P := S.filter fun x =>
      (G.neighborFinset x ∩ fullLineCenters G S q).card = 1
    2 * (Finset.univ.filter fun v =>
      (G.neighborFinset v ∩ P).card = 0).card = q ∧
    2 * (Finset.univ.filter fun v =>
      (G.neighborFinset v ∩ P).card = 2).card = q := by
  classical
  let P := S.filter fun x =>
    (G.neighborFinset x ∩ fullLineCenters G S q).card = 1
  let y := (G.adjMatrix ℤ).mulVec (finsetIndicatorInt P) -
    (1 : V → ℤ)
  have hPcard : P.card = q := by
    simpa [P] using
      (c4Free_binarySquare_pureEndpoint_fullLineCenters_exactReplicationProfile
        G hfree hq hqm hreg hcard S hempty hCcard hshore htri).2.1
  have hclass := binarySquare_minimumDefectCut_centeredRow_balanced
    G hfree hq hfour hreg hcard P hPcard (by simpa [P] using hcut)
  dsimp only at hclass
  have hyapply : ∀ v, y v =
      ((G.neighborFinset v ∩ P).card : ℤ) - 1 := by
    intro v
    simp only [y, Pi.sub_apply]
    rw [adjMatrix_mulVec_finsetIndicatorInt_apply]
    rfl
  have hzero : (Finset.univ.filter fun v => y v = -1) =
      Finset.univ.filter fun v =>
        (G.neighborFinset v ∩ P).card = 0 := by
    ext v
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rw [hyapply v]
    constructor
    · intro hv
      omega
    · intro hv
      omega
  have htwo : (Finset.univ.filter fun v => y v = 1) =
      Finset.univ.filter fun v =>
        (G.neighborFinset v ∩ P).card = 2 := by
    ext v
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rw [hyapply v]
    constructor
    · intro hv
      omega
    · intro hv
      omega
  change
    2 * (Finset.univ.filter fun v =>
      (G.neighborFinset v ∩ P).card = 0).card = q ∧
    2 * (Finset.univ.filter fun v =>
      (G.neighborFinset v ∩ P).card = 2).card = q
  rw [← hzero, ← htwo]
  exact ⟨hclass.2.2, hclass.2.1⟩

end

end Erdos85

#print axioms
  Erdos85.c4Free_binarySquare_pureEndpoint_minimumPrivateCut_rowProfile
