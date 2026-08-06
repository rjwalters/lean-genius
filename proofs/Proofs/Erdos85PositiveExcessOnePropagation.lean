import Proofs.Erdos85PositiveExcessOneOperator

/-!
# Propagation of excess-one serving multiplicity

The entrywise conservation law `AD = DA` turns double use of a potential
serving arc into a new adjacency on the antipodal two-factor.  This is the
operator-discharge step needed for the global canonical-isolate count.
-/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- Entrywise `AD = DA` for an arbitrary regular `C₄`-free graph. -/
theorem card_filter_adj_secondOrderDefect_comm_of_regular
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) {d : ℕ}
    (hreg : ∀ z, G.degree z = d) (x y : V) :
    (((secondOrderDefectGraph G).neighborFinset y).filter
          (fun z => G.Adj x z)).card =
      (((secondOrderDefectGraph G).neighborFinset x).filter
          (fun z => G.Adj z y)).card := by
  let D := secondOrderDefectGraph G
  have hcomm := adjMatrix_comm_secondOrderDefect_of_regular G hfree hreg
  have hentry := congrFun (congrFun hcomm x) y
  change (G.adjMatrix ℤ * D.adjMatrix ℤ) x y =
    (D.adjMatrix ℤ * G.adjMatrix ℤ) x y at hentry
  rw [D.mul_adjMatrix_apply, D.adjMatrix_mul_apply] at hentry
  simp only [SimpleGraph.adjMatrix_apply, Finset.sum_boole,
    Int.ofNat_inj] at hentry
  simpa [D] using hentry

/-- **Double-service propagation.**  Suppose two distinct defect-neighbors
of `X` are both adjacent to `u`.  If `u` has only one triangle-free partner,
commutation forces an antipodal neighbor of `u` to be adjacent to `X` as
well. -/
theorem exists_adj_antipodal_of_two_adj_defectNeighbors
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) {d : ℕ}
    (hreg : ∀ z, G.degree z = d)
    (u X x y : V) (hxy : x ≠ y)
    (hxD : x ∈ (secondOrderDefectGraph G).neighborFinset X)
    (hyD : y ∈ (secondOrderDefectGraph G).neighborFinset X)
    (hux : G.Adj u x) (huy : G.Adj u y)
    (hTFone : (triangleFreeNeighbors G u).card = 1) :
    ∃ w ∈ antipodalNeighbors G u, G.Adj w X := by
  classical
  let L := ((secondOrderDefectGraph G).neighborFinset X).filter
    (fun z => G.Adj u z)
  let R := ((secondOrderDefectGraph G).neighborFinset u).filter
    (fun z => G.Adj z X)
  have hxL : x ∈ L := Finset.mem_filter.mpr ⟨hxD, hux⟩
  have hyL : y ∈ L := Finset.mem_filter.mpr ⟨hyD, huy⟩
  have hLtwo : 2 ≤ L.card := by
    have hp : ({x, y} : Finset V).card = 2 := by simp [hxy]
    rw [← hp]
    apply Finset.card_le_card
    intro z hz
    simp only [Finset.mem_insert, Finset.mem_singleton] at hz
    rcases hz with rfl | rfl
    · exact hxL
    · exact hyL
  have hLR : L.card = R.card := by
    simpa [L, R] using
      card_filter_adj_secondOrderDefect_comm_of_regular
        G hfree hreg u X
  have hRtwo : 2 ≤ R.card := by omega
  by_contra hnone
  push_neg at hnone
  have hsub : R ⊆ triangleFreeNeighbors G u := by
    intro z hz
    have hzD := (Finset.mem_filter.mp hz).1
    rw [secondOrderDefectGraph_neighborFinset G u] at hzD
    rcases Finset.mem_union.mp hzD with hzAnti | hzTF
    · exact (hnone z hzAnti (Finset.mem_filter.mp hz).2).elim
    · exact hzTF
  have hRle : R.card ≤ (triangleFreeNeighbors G u).card :=
    Finset.card_le_card hsub
  rw [hTFone] at hRle
  omega

end

end Erdos85
