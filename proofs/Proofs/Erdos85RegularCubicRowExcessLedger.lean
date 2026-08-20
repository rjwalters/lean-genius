import Proofs.Erdos85RegularCubicRowSquareSplit

/-! # Arbitrary-center cubic row excess ledger

Node: F.3 GENERALIZATION.  The familiar `(x-3)(x-4)` histogram correction
is one instance of an exact identity valid at every integer center and for
every regular degree and order.
-/

open Finset SimpleGraph Matrix

namespace Erdos85

noncomputable section

/-- Exact cubic row-square ledger for a C4-free `d`-regular graph, centered
at any pair of consecutive integers `c,c+1`. -/
theorem regular_c4Free_cube_row_square_eq_baseline_add_excess
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G) (d : ℕ)
    (hreg : ∀ x, G.degree x = d) (c : ℤ) (a : V) :
    let A3 := G.adjMatrix ℤ * G.adjMatrix ℤ * G.adjMatrix ℤ
    let Q := cubicNonneighborFinset G a
    (∑ b, (A3 a b) ^ 2) =
      (d : ℤ) * (2 * (d : ℤ) - 1) ^ 2 + (A3 a a) ^ 2 +
      (2 * c + 1) *
        ((d : ℤ) ^ 3 - (d : ℤ) * (2 * (d : ℤ) - 1) - A3 a a) -
      c * (c + 1) * (Q.card : ℤ) +
      ∑ b ∈ Q, (A3 a b - c) * (A3 a b - (c + 1)) := by
  classical
  dsimp only
  let A3 := G.adjMatrix ℤ * G.adjMatrix ℤ * G.adjMatrix ℤ
  let Q := cubicNonneighborFinset G a
  have hsplit := regular_c4Free_cube_row_square_split G hfree d hreg a
  have hmass := c4Free_regular_cubicNonneighborMass_eq G hfree d hreg a
  change (∑ b ∈ Q, A3 a b) =
    (d : ℤ) ^ 3 - (d : ℤ) * (2 * (d : ℤ) - 1) - A3 a a at hmass
  have hexpand : (∑ b ∈ Q, (A3 a b) ^ 2) =
      (2 * c + 1) * (∑ b ∈ Q, A3 a b) -
        c * (c + 1) * (Q.card : ℤ) +
        ∑ b ∈ Q, (A3 a b - c) * (A3 a b - (c + 1)) := by
    calc
      _ = ∑ b ∈ Q,
          ((2 * c + 1) * A3 a b - c * (c + 1) +
            (A3 a b - c) * (A3 a b - (c + 1))) := by
              apply Finset.sum_congr rfl
              intro b _
              ring
      _ = (2 * c + 1) * (∑ b ∈ Q, A3 a b) -
          c * (c + 1) * (Q.card : ℤ) +
          ∑ b ∈ Q, (A3 a b - c) * (A3 a b - (c + 1)) := by
            simp_rw [Finset.sum_add_distrib, Finset.sum_sub_distrib]
            simp
            rw [Finset.mul_sum]
            ring
  rw [regular_c4Free_cube_row_square_split G hfree d hreg a]
  rw [hexpand, hmass]
  simp only [A3, Q]
  ring

/-- At center `3`, degree six and order 48, the general ledger is exactly the
service-row baseline `1272` plus the traditional diagonal and nonneighbor
excess terms. -/
theorem sixRegular_fortyEight_cube_row_square_eq_baseline_add_excess_of_general
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G)
    (hcard : Fintype.card V = 48)
    (hreg : ∀ x, G.degree x = 6) (a : V) :
    let A3 := G.adjMatrix ℤ * G.adjMatrix ℤ * G.adjMatrix ℤ
    (∑ b, (A3 a b) ^ 2) = 1272 +
      ((A3 a a) ^ 2 - 7 * A3 a a + 12 +
        ∑ b ∈ cubicNonneighborFinset G a,
          (A3 a b - 3) * (A3 a b - 4)) := by
  have hledger :=
    regular_c4Free_cube_row_square_eq_baseline_add_excess
      G hfree 6 hreg 3 a
  have hq := sixRegular_fortyEight_cubicNonneighborFinset_card
    G hcard hreg a
  norm_num [hq] at hledger ⊢
  linear_combination hledger

end


end Erdos85

#print axioms Erdos85.regular_c4Free_cube_row_square_eq_baseline_add_excess
#print axioms Erdos85.sixRegular_fortyEight_cube_row_square_eq_baseline_add_excess_of_general
