import Proofs.Erdos85BinarySquareAdjacencySquareAction

/-!
# Sparse signed terminal for the binary square-order branch

This file formalizes the load-bearing algebraic core of the final dyadic
occupancy layer.  If a sign vector `x` satisfies `A x = q z`, then the exact
square-order identity transports it to a pointwise equation for the defect
graph.  The support and sign restrictions on `z` are separate combinatorial
inputs; this theorem certifies the matrix-to-defect transport they consume.
-/

open SimpleGraph Matrix

namespace Erdos85

noncomputable section

/-- Multiplying the adjacency matrix by the `±1` sign vector of a shore is
twice the local shore occupancy minus the degree. -/
theorem cutSign_adjMatrix_mulVec_apply
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {q : ℕ} (hreg : ∀ v, G.degree v = q)
    (S : Finset V) (v : V) :
    (G.adjMatrix ℤ).mulVec (fun w => if w ∈ S then (1 : ℤ) else -1) v =
      2 * ((G.neighborFinset v ∩ S).card : ℤ) - q := by
  rw [SimpleGraph.adjMatrix_mulVec_apply]
  have hpoint (w : V) :
      (if w ∈ S then (1 : ℤ) else -1) =
        2 * (if w ∈ S then (1 : ℤ) else 0) - 1 := by
    by_cases hw : w ∈ S <;> simp [hw]
  simp_rw [hpoint]
  rw [Finset.sum_sub_distrib]
  simp [G.card_neighborFinset_eq_degree, hreg]
  ring

/-- If every local shore occupancy is empty, balanced, or full, then the
shore sign vector has a sparse signed adjacency image.  The value `+1`
marks full lines, `-1` marks empty lines, and zero marks balanced lines. -/
theorem cutSign_adjMatrix_mulVec_eq_sparseSigned
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {q : ℕ} (hq : 0 < q) (hreg : ∀ v, G.degree v = q)
    (S : Finset V)
    (htri : ∀ v,
      (G.neighborFinset v ∩ S).card = 0 ∨
      2 * (G.neighborFinset v ∩ S).card = q ∨
      (G.neighborFinset v ∩ S).card = q) :
    (G.adjMatrix ℤ).mulVec (fun w => if w ∈ S then (1 : ℤ) else -1) =
      (q : ℤ) • fun v =>
        if (G.neighborFinset v ∩ S).card = q then (1 : ℤ)
        else if (G.neighborFinset v ∩ S).card = 0 then -1 else 0 := by
  funext v
  rw [cutSign_adjMatrix_mulVec_apply G hreg S v]
  change
    2 * ((G.neighborFinset v ∩ S).card : ℤ) - q =
      (q : ℤ) *
        (if (G.neighborFinset v ∩ S).card = q then 1
         else if (G.neighborFinset v ∩ S).card = 0 then -1 else 0)
  rcases htri v with hzero | hhalf | hfull
  · have h0q : 0 ≠ q := by omega
    simp [hzero, h0q]
  · have hneZero : (G.neighborFinset v ∩ S).card ≠ 0 := by omega
    have hneFull : (G.neighborFinset v ∩ S).card ≠ q := by omega
    have hhalfZ :
        (2 : ℤ) * (G.neighborFinset v ∩ S).card = q := by
      exact_mod_cast hhalf
    simp [hneZero, hneFull, hhalfZ]
  · simp [hfull]
    ring

/-- The coordinate sum of a shore sign vector records its displacement from
half the ambient order. -/
theorem sum_cutSign
    {V : Type*} [Fintype V] [DecidableEq V] (S : Finset V) :
    ∑ v : V, (if v ∈ S then (1 : ℤ) else -1) =
      2 * (S.card : ℤ) - Fintype.card V := by
  have hpoint (v : V) :
      (if v ∈ S then (1 : ℤ) else -1) =
        2 * (if v ∈ S then (1 : ℤ) else 0) - 1 := by
    by_cases hv : v ∈ S <;> simp [hv]
  simp_rw [hpoint]
  rw [Finset.sum_sub_distrib]
  simp
  ring

/-- The sparse signed equation `A x = q z`, together with the coordinate sum
of `x`, gives the companion defect equation pointwise. -/
theorem binarySquare_sparseSigned_companionDefect_apply
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) {q : ℕ}
    (hreg : ∀ v, G.degree v = q)
    (x z : V → ℤ) (d : ℤ)
    (hAx : (G.adjMatrix ℤ).mulVec x = (q : ℤ) • z)
    (hsum : ∑ v, x v = 2 * d) (v : V) :
    ∑ w ∈ (secondOrderDefectGraph G).neighborFinset v, x w =
      ((q : ℤ) - 1) * x v + 2 * d -
        (q : ℤ) * ∑ w ∈ G.neighborFinset v, z w := by
  have hsq := binarySquare_regular_adjMatrix_sq_mulVec_apply
    G hfree hreg x v
  have hAA := congrArg (fun u => (G.adjMatrix ℤ).mulVec u) hAx
  have hleft :
      ((G.adjMatrix ℤ * G.adjMatrix ℤ) *ᵥ x) v =
        (q : ℤ) * ∑ w ∈ G.neighborFinset v, z w := by
    rw [← Matrix.mulVec_mulVec]
    calc
      (G.adjMatrix ℤ).mulVec ((G.adjMatrix ℤ).mulVec x) v =
          (G.adjMatrix ℤ).mulVec ((q : ℤ) • z) v := by
            rw [hAx]
      _ = (q : ℤ) * ∑ w ∈ G.neighborFinset v, z w := by
            rw [Matrix.mulVec_smul]
            simp [SimpleGraph.adjMatrix_mulVec_apply]
  rw [hsum] at hsq
  linarith

/-- Capstone form: an empty/half/full occupancy shore at square order obeys
the canonical sparse signed defect equation, with `d` its displacement from
half the vertex set. -/
theorem binarySquare_trichotomy_companionDefect_apply
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) {q : ℕ} (hq : 0 < q)
    (hreg : ∀ v, G.degree v = q) (hcard : Fintype.card V = q * q)
    (S : Finset V) (d : ℤ)
    (hd : 2 * (S.card : ℤ) - (q * q : ℕ) = 2 * d)
    (htri : ∀ v,
      (G.neighborFinset v ∩ S).card = 0 ∨
      2 * (G.neighborFinset v ∩ S).card = q ∨
      (G.neighborFinset v ∩ S).card = q)
    (v : V) :
    ∑ w ∈ (secondOrderDefectGraph G).neighborFinset v,
        (if w ∈ S then (1 : ℤ) else -1) =
      ((q : ℤ) - 1) * (if v ∈ S then (1 : ℤ) else -1) + 2 * d -
        (q : ℤ) * ∑ w ∈ G.neighborFinset v,
          (if (G.neighborFinset w ∩ S).card = q then (1 : ℤ)
           else if (G.neighborFinset w ∩ S).card = 0 then -1 else 0) := by
  let x : V → ℤ := fun w => if w ∈ S then 1 else -1
  let z : V → ℤ := fun w =>
    if (G.neighborFinset w ∩ S).card = q then 1
    else if (G.neighborFinset w ∩ S).card = 0 then -1 else 0
  have hAx : (G.adjMatrix ℤ).mulVec x = (q : ℤ) • z := by
    simpa [x, z] using
      cutSign_adjMatrix_mulVec_eq_sparseSigned G hq hreg S htri
  have hsum : ∑ w, x w = 2 * d := by
    rw [show (∑ w, x w) = 2 * (S.card : ℤ) - Fintype.card V by
      simpa [x] using sum_cutSign S]
    rw [hcard]
    exact hd
  simpa [x, z] using
    binarySquare_sparseSigned_companionDefect_apply
      G hfree hreg x z d hAx hsum v

/-- Arithmetic capstone behind the mixed exceptional-support bound.  At
`q = 4m`, write the two line-type sizes as `u` and `u + 2a`; the minority
replication bound and the complete bipartite defect core force total support
at most `3q/2 - 2 = 6m - 2`. -/
theorem binarySquare_mixedExceptional_card_le
    {m a u c : ℕ} (hm : 1 ≤ m)
    (hc : c = 2 * (u + a))
    (huBalanced : a = 0 → u ≤ 2 * m)
    (huUnbalanced : 0 < a → u ≤ 2 * m - 1)
    (hcore : u + 2 * a ≤ 4 * m - 1) :
    c ≤ 6 * m - 2 := by
  by_cases ha : a = 0
  · have hu := huBalanced ha
    omega
  · have haPos : 0 < a := Nat.pos_of_ne_zero ha
    have hu := huUnbalanced haPos
    omega

end

end Erdos85

#print axioms Erdos85.cutSign_adjMatrix_mulVec_apply
#print axioms Erdos85.cutSign_adjMatrix_mulVec_eq_sparseSigned
#print axioms Erdos85.sum_cutSign
#print axioms Erdos85.binarySquare_sparseSigned_companionDefect_apply
#print axioms Erdos85.binarySquare_trichotomy_companionDefect_apply
#print axioms Erdos85.binarySquare_mixedExceptional_card_le
