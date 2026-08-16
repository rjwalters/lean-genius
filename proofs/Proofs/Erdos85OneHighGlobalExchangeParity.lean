import Proofs.Erdos85OneHighGlobalMissLabelCounting

/-! # Unconditional global parity of exchanged miss labels -/

namespace Erdos85

noncomputable section

/-- By symmetry of the square-order miss matrix, every far-column sum is a
dirty row sum and hence an even matched-vertex count.  This parity does not
assume same-miss or emptiness of the nonconstant source set. -/
theorem even_sum_far_highBranchMissCount_column
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G) {d : ℕ} (hd : 2 ≤ d) {v : V}
    (hv : G.degree v = d + 1)
    (hneigh : ∀ y, G.Adj v y → G.degree y = d)
    (hlocal : ∀ u : {z : V // z ∈ G.neighborSet v},
      (G.induce (G.neighborSet v)).degree u = 1)
    (hexternal : externalRepairCandidates G v = ∅)
    (rootMate : {z : V // z ∈ G.neighborSet v} →
      {z : V // z ∈ G.neighborSet v})
    (hrootAdj : ∀ s, G.Adj s.1 (rootMate s).1)
    (houterDegree : ∀ {a : V}, a ∈ secondLayer G v → G.degree a = d)
    (u : {z : V // z ∈ G.neighborSet v}) :
    Even (∑ s ∈ ((Finset.univ.erase u).erase (rootMate u)),
      highBranchMissCount G v s u) := by
  have hcolrow :
      (∑ s ∈ ((Finset.univ.erase u).erase (rootMate u)),
        highBranchMissCount G v s u) =
      ∑ s ∈ ((Finset.univ.erase u).erase (rootMate u)),
        highBranchMissCount G v u s := by
    apply Finset.sum_congr rfl
    intro s _
    exact squareOrder_highBranchMissCount_comm
      G hfree hd hv hneigh hlocal s u
  have hrow := sum_far_highBranchMissCount_eq_matchedCount
    G hfree hv hexternal u (rootMate u) (hrootAdj u) (by
      intro a ha
      apply houterDegree
      rw [secondLayer]
      exact Finset.mem_biUnion.mpr ⟨u, Finset.mem_univ _, ha⟩)
  rw [hcolrow, hrow]
  exact even_highBranchMatchedCount G hfree u

end

end Erdos85
