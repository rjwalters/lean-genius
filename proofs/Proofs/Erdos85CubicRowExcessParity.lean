import Proofs.Erdos85CubicStructuralExcessBaseline

/-! # Parity and gaps in the cubic row excess -/

open Finset SimpleGraph Matrix

namespace Erdos85

noncomputable section

theorem even_integer_three_four_excess (x : ℤ) :
    Even ((x - 3) * (x - 4)) := by
  rcases Int.even_or_odd x with ⟨k, rfl⟩ | ⟨k, rfl⟩
  · refine ⟨(k + k - 3) * (k - 2), ?_⟩
    ring
  · refine ⟨(k - 1) * (k + k - 3), ?_⟩
    ring

/-- In a six-regular C4-free graph, every cubic row histogram contribution
is even. -/
theorem even_cubicRowHistogramExcess
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G) (hreg : ∀ x, G.degree x = 6)
    (a : V) :
    Even (cubicRowHistogramExcess G a) := by
  let A3 := G.adjMatrix ℤ * G.adjMatrix ℤ * G.adjMatrix ℤ
  have hq := sixRegular_c4Free_adjMatrix_cube_apply_self_cases
    G hfree hreg a
  change A3 a a = 0 ∨ A3 a a = 2 ∨ A3 a a = 4 ∨ A3 a a = 6 at hq
  have hdiag : Even ((A3 a a) ^ 2 - 7 * A3 a a + 12) := by
    rcases hq with hq | hq | hq | hq
    · refine ⟨6, by rw [hq]; norm_num⟩
    · refine ⟨1, by rw [hq]; norm_num⟩
    · refine ⟨0, by rw [hq]; norm_num⟩
    · refine ⟨3, by rw [hq]; norm_num⟩
  have hcorr : Even (∑ b ∈ cubicNonneighborFinset G a,
      (A3 a b - 3) * (A3 a b - 4)) := by
    exact Finset.even_sum _ fun b hb ↦
      even_integer_three_four_excess (A3 a b)
  change Even ((A3 a a) ^ 2 - 7 * A3 a a + 12 +
    ∑ b ∈ cubicNonneighborFinset G a,
      (A3 a b - 3) * (A3 a b - 4))
  exact hdiag.add hcorr

/-- A nonantipodal row already known to contribute at least four is either
sharp at four or jumps to at least six. -/
theorem cubicRowHistogramExcess_eq_four_or_ge_six
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G) (hreg : ∀ x, G.degree x = 6)
    (a : V) (hfour : 4 ≤ cubicRowHistogramExcess G a) :
    cubicRowHistogramExcess G a = 4 ∨
      6 ≤ cubicRowHistogramExcess G a := by
  rcases even_cubicRowHistogramExcess G hfree hreg a with ⟨k, hk⟩
  omega

/-- Likewise, any nonzero row contribution is at least two. -/
theorem cubicRowHistogramExcess_eq_zero_or_ge_two
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G) (hreg : ∀ x, G.degree x = 6)
    (a : V) :
    cubicRowHistogramExcess G a = 0 ∨
      2 ≤ cubicRowHistogramExcess G a := by
  have hnonneg := cubicRowHistogramExcess_nonnegative G hfree hreg a
  rcases even_cubicRowHistogramExcess G hfree hreg a with ⟨k, hk⟩
  omega

end

end Erdos85

#print axioms Erdos85.even_cubicRowHistogramExcess
#print axioms Erdos85.cubicRowHistogramExcess_eq_four_or_ge_six
#print axioms Erdos85.cubicRowHistogramExcess_eq_zero_or_ge_two
