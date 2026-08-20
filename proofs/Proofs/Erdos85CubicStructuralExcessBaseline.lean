import Proofs.Erdos85SameShoreNonantipodalCubicFiberBounds
import Proofs.Erdos85CubicDiagonalParity

/-! # Structural baseline for the global cubic histogram excess -/

open Finset SimpleGraph Matrix

namespace Erdos85

noncomputable section

/-- Every row contribution to the cubic histogram excess is nonnegative. -/
theorem cubicRowHistogramExcess_nonnegative
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G) (hreg : ∀ x, G.degree x = 6)
    (a : V) :
    0 ≤ cubicRowHistogramExcess G a := by
  let A3 := G.adjMatrix ℤ * G.adjMatrix ℤ * G.adjMatrix ℤ
  have hq := sixRegular_c4Free_adjMatrix_cube_apply_self_cases
    G hfree hreg a
  have hcorr := sum_integer_three_four_excess_nonnegative
    (cubicNonneighborFinset G a) (fun b ↦ A3 a b)
  change 0 ≤ (A3 a a) ^ 2 - 7 * A3 a a + 12 +
    ∑ b ∈ cubicNonneighborFinset G a,
      (A3 a b - 3) * (A3 a b - 4)
  change A3 a a = 0 ∨ A3 a a = 2 ∨ A3 a a = 4 ∨ A3 a a = 6 at hq
  rcases hq with hq | hq | hq | hq <;> rw [hq] <;> norm_num <;> omega

/-- Forty rows contributing at least four, with every remaining row
nonnegative, force total histogram excess at least `160`. -/
theorem sum_cubicRowHistogramExcess_ge_160_of_forty_good
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G) (hreg : ∀ x, G.degree x = 6)
    (N : Finset V) (hNcard : N.card = 40)
    (hgood : ∀ a ∈ N, 4 ≤ cubicRowHistogramExcess G a) :
    160 ≤ ∑ a : V, cubicRowHistogramExcess G a := by
  let F := fun a : V ↦ cubicRowHistogramExcess G a
  have hNsum : 160 ≤ ∑ a ∈ N, F a := by
    calc
      160 = ∑ _a ∈ N, 4 := by simp [hNcard]
      _ ≤ ∑ a ∈ N, F a := Finset.sum_le_sum fun a ha ↦ hgood a ha
  let M := (Finset.univ : Finset V) \ N
  have hMsum : 0 ≤ ∑ a ∈ M, F a := by
    apply Finset.sum_nonneg
    intro a ha
    exact cubicRowHistogramExcess_nonnegative G hfree hreg a
  have hdisj : Disjoint N M := Finset.disjoint_sdiff
  have hcover : N ∪ M = Finset.univ := by
    rw [Finset.union_sdiff_of_subset (Finset.subset_univ N)]
  calc
    160 ≤ (∑ a ∈ N, F a) + ∑ a ∈ M, F a := by omega
    _ = ∑ a ∈ N ∪ M, F a := (Finset.sum_union hdisj).symm
    _ = ∑ a : V, cubicRowHistogramExcess G a := by rw [hcover]

/-- The global excess used in the sixth-trace ledger is definitionally the
sum of the row contributions. -/
theorem sum_cubicRowHistogramExcess_eq_histogramExcess
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    let A3 := G.adjMatrix ℤ * G.adjMatrix ℤ * G.adjMatrix ℤ
    (∑ a : V, cubicRowHistogramExcess G a) =
      ∑ a, ((A3 a a) ^ 2 - 7 * A3 a a + 12 +
        ∑ b ∈ cubicNonneighborFinset G a,
          (A3 a b - 3) * (A3 a b - 4)) := by
  rfl

end

end Erdos85

#print axioms Erdos85.cubicRowHistogramExcess_nonnegative
#print axioms Erdos85.sum_cubicRowHistogramExcess_ge_160_of_forty_good
