import Proofs.Erdos85PositiveExcessLocalParity

/-!
# Canonical color split at even-degree excess one

At excess one the combined defect graph is three-regular.  When the
original degree is even, local triangle parity makes the triangle-free
color degree even.  Hence its only possible values are zero and two, and
the complementary antipodal degree is respectively three and one.
-/

open SimpleGraph

namespace Erdos85

/-- At even degree and excess one, the triangle-free color has local degree
zero or two. -/
theorem excessOne_even_triangleFree_degree_zero_or_two
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) {d : ℕ} (heven : Even d)
    (hreg : ∀ x, G.degree x = d)
    (hcard : Fintype.card V = d * (d - 1) + 4) (x : V) :
    (triangleFreeEdgeGraph G).degree x = 0 ∨
      (triangleFreeEdgeGraph G).degree x = 2 := by
  have hpar := triangleFreeNeighbors_card_mod_two_eq_degree
    G hfree hreg x
  have hD : (secondOrderDefectGraph G).degree x = 3 := by
    simpa using secondOrderDefectGraph_degree_eq_excess_add_two
      G hfree hreg (e := 1) (by simpa using hcard) x
  have hsum : (antipodalNeighbors G x).card +
      (triangleFreeNeighbors G x).card = 3 := by
    rw [← hD, ← (secondOrderDefectGraph G).card_neighborFinset_eq_degree,
      secondOrderDefectGraph_neighborFinset,
      Finset.card_union_of_disjoint
        (disjoint_antipodal_triangleFreeNeighbors G x)]
  have hTpar : (triangleFreeNeighbors G x).card % 2 = 0 := by
    rcases heven with ⟨k, hk⟩
    rw [hpar, hk]
    omega
  rw [← (triangleFreeEdgeGraph G).card_neighborFinset_eq_degree,
    triangleFreeEdgeGraph_neighborFinset]
  omega

/-- Full local color classification: `(T,C)` is `(0,3)` or `(2,1)`. -/
theorem excessOne_even_color_degree_classification
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) {d : ℕ} (heven : Even d)
    (hreg : ∀ x, G.degree x = d)
    (hcard : Fintype.card V = d * (d - 1) + 4) (x : V) :
    ((triangleFreeEdgeGraph G).degree x = 0 ∧
        (antipodalGraph G).degree x = 3) ∨
      ((triangleFreeEdgeGraph G).degree x = 2 ∧
        (antipodalGraph G).degree x = 1) := by
  have hD : (secondOrderDefectGraph G).degree x = 3 := by
    simpa using secondOrderDefectGraph_degree_eq_excess_add_two
      G hfree hreg (e := 1) (by simpa using hcard) x
  have hsum : (antipodalGraph G).degree x +
      (triangleFreeEdgeGraph G).degree x = 3 := by
    rw [← (antipodalGraph G).card_neighborFinset_eq_degree,
      antipodalGraph_neighborFinset,
      ← (triangleFreeEdgeGraph G).card_neighborFinset_eq_degree,
      triangleFreeEdgeGraph_neighborFinset,
      ← hD, ← (secondOrderDefectGraph G).card_neighborFinset_eq_degree,
      secondOrderDefectGraph_neighborFinset,
      Finset.card_union_of_disjoint
        (disjoint_antipodal_triangleFreeNeighbors G x)]
  rcases excessOne_even_triangleFree_degree_zero_or_two
      G hfree heven hreg hcard x with hx | hx
  · left
    omega
  · right
    omega

/-- The first mixed trace is twice the size of the degree-two color sector. -/
theorem trace_adjMatrix_mul_secondOrderDefect_even_excessOne
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) {d : ℕ} (heven : Even d)
    (hreg : ∀ x, G.degree x = d)
    (hcard : Fintype.card V = d * (d - 1) + 4) :
    Matrix.trace (G.adjMatrix ℤ *
        (secondOrderDefectGraph G).adjMatrix ℤ) =
      2 * ((Finset.univ.filter fun x : V =>
        (triangleFreeEdgeGraph G).degree x = 2).card : ℤ) := by
  rw [trace_adjMatrix_mul_secondOrderDefect_eq_sum_triangleFreeDegrees]
  have hdeg : ∀ x : V, (triangleFreeEdgeGraph G).degree x = 0 ∨
      (triangleFreeEdgeGraph G).degree x = 2 :=
    excessOne_even_triangleFree_degree_zero_or_two
      G hfree heven hreg hcard
  calc
    (∑ x : V, ((triangleFreeEdgeGraph G).degree x : ℤ)) =
        ∑ x : V, if (triangleFreeEdgeGraph G).degree x = 2
          then 2 else 0 := by
      apply Finset.sum_congr rfl
      intro x _
      rcases hdeg x with hx | hx <;> simp [hx]
    _ = 2 * ((Finset.univ.filter fun x : V =>
        (triangleFreeEdgeGraph G).degree x = 2).card : ℤ) := by
      rw [← Finset.sum_filter]
      simp [mul_comm]

end Erdos85
