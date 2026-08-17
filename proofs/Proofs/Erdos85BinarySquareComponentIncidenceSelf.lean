import Proofs.Erdos85BinarySquareComponentIncidence

/-!
# Diagonal Gram block of component incidence

The existing cross-component identity gives `B_c^T B_d = J` for `c != d`.
This file supplies the matching diagonal identity: the Gram matrix of one
component's ambient-neighbor incidence is the complement of the induced
second-order defect block, with its diagonal corrected to the ambient degree.
-/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- **Component-incidence self Gram.**  For a regular square-order core,
`B_c^T B_c = (q-1)I + J - D[c]`.  For a normalized size-two component this
is precisely the unsigned incidence Gram of the `q`-regular selector graph
`complement(D[c])`. -/
theorem transpose_defectComponentNeighborIncidenceMatrix_mul_self
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) {q : ℕ} (hq : 1 ≤ q)
    (hreg : ∀ x, G.degree x = q)
    (c : (secondOrderDefectGraph G).ConnectedComponent) :
    (defectComponentNeighborIncidenceMatrix (K := ℤ) G c).transpose *
        defectComponentNeighborIncidenceMatrix (K := ℤ) G c =
      ((q - 1 : ℕ) : ℤ) • (1 : Matrix c.supp c.supp ℤ) +
        Matrix.of (fun _ _ => (1 : ℤ)) -
          ((secondOrderDefectGraph G).induce c.supp).adjMatrix ℤ := by
  ext x y
  have hentry :
      ((defectComponentNeighborIncidenceMatrix (K := ℤ) G c).transpose *
          defectComponentNeighborIncidenceMatrix (K := ℤ) G c) x y =
        ((G.neighborFinset x.1 ∩ G.neighborFinset y.1).card : ℤ) := by
    rw [Matrix.mul_apply]
    simp only [Matrix.transpose_apply, defectComponentNeighborIncidenceMatrix,
      ite_mul, one_mul, zero_mul]
    calc
      (∑ z : V, if G.Adj z x.1 then if G.Adj z y.1 then (1 : ℤ) else 0 else 0) =
          ∑ z : V, if G.Adj x.1 z ∧ G.Adj y.1 z then (1 : ℤ) else 0 := by
        apply Finset.sum_congr rfl
        intro z _hz
        by_cases hzx : G.Adj z x.1 <;> by_cases hzy : G.Adj z y.1 <;>
          simp [hzx, hzy, G.adj_comm]
      _ = ((G.neighborFinset x.1 ∩ G.neighborFinset y.1).card : ℤ) := by
        rw [Finset.sum_boole]
        have hfilt : (Finset.univ : Finset V).filter
            (fun z => G.Adj x.1 z ∧ G.Adj y.1 z) =
            G.neighborFinset x.1 ∩ G.neighborFinset y.1 := by
          ext z
          simp [SimpleGraph.mem_neighborFinset]
        rw [hfilt]
  rw [hentry]
  by_cases hxy : x = y
  · subst y
    simp [Matrix.natCast_apply, SimpleGraph.adjMatrix_apply,
      SimpleGraph.card_neighborFinset_eq_degree, hreg,
      Nat.cast_sub hq]
  · have hxyVal : x.1 ≠ y.1 := by
      intro h
      exact hxy (Subtype.ext h)
    have hcard := card_common_eq_if_secondOrderDefect G hfree x.1 y.1 hxyVal
    by_cases hD : (secondOrderDefectGraph G).Adj x.1 y.1
    · have hmem : y.1 ∈ (secondOrderDefectGraph G).neighborFinset x.1 :=
        ((secondOrderDefectGraph G).mem_neighborFinset x.1 y.1).mpr hD
      rw [hcard, if_pos hmem]
      simp [Matrix.natCast_apply, SimpleGraph.adjMatrix_apply, hxy, hD]
    · have hmem : y.1 ∉ (secondOrderDefectGraph G).neighborFinset x.1 := by
        simpa [SimpleGraph.mem_neighborFinset] using hD
      rw [hcard, if_neg hmem]
      simp [Matrix.natCast_apply, SimpleGraph.adjMatrix_apply, hxy, hD]

end

end Erdos85
