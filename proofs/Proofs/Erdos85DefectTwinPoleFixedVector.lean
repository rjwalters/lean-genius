import Proofs.Erdos85EvenExcessOneDefectKernel

/-!
# Adjacent twin poles fix their binary pair indicator

This is the graph-facing provenance of the hypothesis `Dh=h` in
`(73rnz_bs)`: adjacent poles whose neighborhoods agree away from the two
poles fix the vector `e₁+e₂` over `F₂`.
-/

open SimpleGraph

namespace Erdos85

/-- Adjacent off-pole twins fix their two-coordinate indicator. -/
theorem adjMatrix_mulVec_twoCoordinate_eq_self_of_adjacent_twins
    {V : Type*} [Fintype V] [DecidableEq V]
    (D : SimpleGraph V) [DecidableRel D.Adj]
    (pole₁ pole₂ : V) (hpoles : pole₁ ≠ pole₂)
    (hadj : D.Adj pole₁ pole₂)
    (htwin : ∀ v, v ≠ pole₁ → v ≠ pole₂ →
      (D.Adj v pole₁ ↔ D.Adj v pole₂)) :
    (D.adjMatrix (ZMod 2)).mulVec
        (Pi.single pole₁ 1 + Pi.single pole₂ 1) =
      Pi.single pole₁ 1 + Pi.single pole₂ 1 := by
  rw [Matrix.mulVec_add, Matrix.mulVec_single_one,
    Matrix.mulVec_single_one]
  funext v
  simp only [Pi.add_apply, Pi.single_apply]
  by_cases hv₁ : v = pole₁
  · subst v
    simp [SimpleGraph.adjMatrix_apply, hadj, hpoles]
  · by_cases hv₂ : v = pole₂
    · subst v
      simp [SimpleGraph.adjMatrix_apply, hadj.symm, hpoles.symm]
    · have hiff := htwin v hv₁ hv₂
      by_cases h₁ : D.Adj v pole₁
      · have h₂ := hiff.mp h₁
        simp [SimpleGraph.adjMatrix_apply, h₁, h₂, hv₁, hv₂,
          zmodTwo_add_self]
      · have h₂ : ¬ D.Adj v pole₂ := fun h => h₁ (hiff.mpr h)
        simp [SimpleGraph.adjMatrix_apply, h₁, h₂, hv₁, hv₂]

/-- `secondOrderDefectGraph` specialization, directly discharging the fixed
two-pole hypothesis used by the exceptional-line transport theorem. -/
theorem secondOrderDefect_mulVec_twoCoordinate_eq_self_of_adjacent_twins
    {V : Type*} [Fintype V] [DecidableEq V]
    (A : SimpleGraph V) [DecidableRel A.Adj]
    [DecidableRel (antipodalGraph A).Adj]
    (pole₁ pole₂ : V) (hpoles : pole₁ ≠ pole₂)
    (hadj : (secondOrderDefectGraph A).Adj pole₁ pole₂)
    (htwin : ∀ v, v ≠ pole₁ → v ≠ pole₂ →
      ((secondOrderDefectGraph A).Adj v pole₁ ↔
        (secondOrderDefectGraph A).Adj v pole₂)) :
    ((secondOrderDefectGraph A).adjMatrix (ZMod 2)).mulVec
        (Pi.single pole₁ 1 + Pi.single pole₂ 1) =
      Pi.single pole₁ 1 + Pi.single pole₂ 1 := by
  exact adjMatrix_mulVec_twoCoordinate_eq_self_of_adjacent_twins
    (secondOrderDefectGraph A) pole₁ pole₂ hpoles hadj htwin

end Erdos85

#print axioms Erdos85.adjMatrix_mulVec_twoCoordinate_eq_self_of_adjacent_twins
#print axioms Erdos85.secondOrderDefect_mulVec_twoCoordinate_eq_self_of_adjacent_twins
