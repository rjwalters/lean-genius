import Proofs.Erdos85RestrictedOwnerResolution

/-! # Operator reduction of local two-color cubic terms -/

namespace Erdos85

noncomputable section

/-- For one fixed color `i`, summing the cubic traces in which `i` is
repeated and the third color is different is the single operator trace
`tr(Aᵢ² (K - Aᵢ))`, where `K` is the sum of all colors. -/
theorem sum_other_trace_sq_mul_eq_trace_sq_mul_sub
    {I V R : Type*} [Fintype I] [DecidableEq I] [Fintype V] [CommRing R]
    (A : I → Matrix V V R) (K : Matrix V V R)
    (hsum : ∑ i, A i = K) (i : I) :
    (∑ j ∈ (Finset.univ.erase i),
      Matrix.trace (A i * A i * A j)) =
        Matrix.trace (A i * A i * (K - A i)) := by
  classical
  have hothers : ∑ j ∈ (Finset.univ.erase i), A j = K - A i := by
    have hi : i ∈ (Finset.univ : Finset I) := Finset.mem_univ i
    have hsplit := Finset.sum_erase_add (s := (Finset.univ : Finset I))
      (f := A) hi
    rw [hsum] at hsplit
    exact eq_sub_of_add_eq hsplit
  calc
    (∑ j ∈ (Finset.univ.erase i), Matrix.trace (A i * A i * A j)) =
        Matrix.trace (∑ j ∈ (Finset.univ.erase i), A i * A i * A j) := by
          simp only [Matrix.trace_sum]
    _ = Matrix.trace (A i * A i *
        (∑ j ∈ (Finset.univ.erase i), A j)) := by
      congr 1
      simp_rw [Finset.mul_sum]
    _ = Matrix.trace (A i * A i * (K - A i)) := by rw [hothers]

/-- Local restricted-owner specialization, with `K` the selector complement
on the source defect component. -/
theorem sum_other_restrictedOwner_trace_sq_mul_eq_complement_sub
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G)
    (source i : (secondOrderDefectGraph G).ConnectedComponent) :
    let A := fun owner : (secondOrderDefectGraph G).ConnectedComponent =>
      (restrictedComponentOwnerGraph G source owner).adjMatrix ℤ
    let K := (((secondOrderDefectGraph G).induce source.supp)ᶜ).adjMatrix ℤ
    (∑ j ∈ (Finset.univ.erase i), Matrix.trace (A i * A i * A j)) =
      Matrix.trace (A i * A i * (K - A i)) := by
  dsimp
  exact sum_other_trace_sq_mul_eq_trace_sq_mul_sub _ _
    (sum_restrictedComponentOwnerGraph_adjMatrix_eq_inducedDefect_compl
      G hfree source) i

end

end Erdos85
