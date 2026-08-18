import Proofs.Erdos85LocalOwnerCubeExpansion

/-! # Equality-pattern split of local owner cubic terms -/

namespace Erdos85

abbrev ownerTripleMonochromatic {I : Type*} (i j k : I) : Prop :=
  i = j ∧ j = k

abbrev ownerTripleRainbow {I : Type*} (i j k : I) : Prop :=
  i ≠ j ∧ i ≠ k ∧ j ≠ k

abbrev ownerTripleExactlyTwo {I : Type*} (i j k : I) : Prop :=
  ¬ ownerTripleMonochromatic i j k ∧ ¬ ownerTripleRainbow i j k

/-- Every ordered triple contributes to exactly one of the monochromatic,
exactly-two-color, and pairwise-distinct sums. -/
theorem orderedTriple_sum_pattern_split
    {I R : Type*} [Fintype I] [DecidableEq I] [CommRing R]
    (f : I → I → I → R) :
    (∑ k, ∑ j, ∑ i, f i j k) =
      (∑ k, ∑ j, ∑ i,
        if ownerTripleMonochromatic i j k then f i j k else 0) +
      (∑ k, ∑ j, ∑ i,
        if ownerTripleExactlyTwo i j k then f i j k else 0) +
      (∑ k, ∑ j, ∑ i,
        if ownerTripleRainbow i j k then f i j k else 0) := by
  classical
  simp_rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro k _hk
  apply Finset.sum_congr rfl
  intro j _hj
  apply Finset.sum_congr rfl
  intro i _hi
  by_cases hm : ownerTripleMonochromatic i j k
  · rcases hm with ⟨rfl, rfl⟩
    simp [ownerTripleExactlyTwo]
  · by_cases hr : ownerTripleRainbow i j k
    · simp [ownerTripleExactlyTwo, hm, hr]
    · simp [ownerTripleExactlyTwo, hm, hr]

/-- Apply the abstract pattern partition to the local restricted-owner cube
expansion on a fixed defect component. -/
theorem trace_inducedDefect_compl_cube_eq_ownerPattern_sums
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G)
    (source : (secondOrderDefectGraph G).ConnectedComponent) :
    let A := fun owner : (secondOrderDefectGraph G).ConnectedComponent =>
      (restrictedComponentOwnerGraph G source owner).adjMatrix ℤ
    let tr := fun i j k => Matrix.trace (A i * A j * A k)
    Matrix.trace
        (((((secondOrderDefectGraph G).induce source.supp)ᶜ).adjMatrix ℤ) *
          ((((secondOrderDefectGraph G).induce source.supp)ᶜ).adjMatrix ℤ) *
          ((((secondOrderDefectGraph G).induce source.supp)ᶜ).adjMatrix ℤ)) =
      (∑ k, ∑ j, ∑ i,
        if ownerTripleMonochromatic i j k then tr i j k else 0) +
      (∑ k, ∑ j, ∑ i,
        if ownerTripleExactlyTwo i j k then tr i j k else 0) +
      (∑ k, ∑ j, ∑ i,
        if ownerTripleRainbow i j k then tr i j k else 0) := by
  classical
  dsimp
  rw [trace_inducedDefect_compl_cube_eq_sum_restrictedOwner_ordered_traces
    G hfree source]
  exact orderedTriple_sum_pattern_split _

end Erdos85
