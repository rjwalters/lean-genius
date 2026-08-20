import Proofs.Erdos85RegularCubicSharpRowCensus

/-! # Diagonal interval forced by a two-level cubic row

Node: F.3 GENERALIZATION.  The exact upper-level census lies between zero
and the nonneighbor-sector size, forcing a sharp interval for `A³(a,a)`.
-/

open Finset SimpleGraph Matrix

namespace Erdos85

noncomputable section

/-- Two-level support `{c,c+1}` in a nonneighbor cubic row forces its
diagonal cubic entry into the interval obtained from the two extreme
histograms. -/
theorem regular_c4Free_twoLevel_cube_row_diag_interval
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G) (d : ℕ)
    (hreg : ∀ x, G.degree x = d) (c : ℤ) (a : V)
    (hlevels :
      let A3 := G.adjMatrix ℤ * G.adjMatrix ℤ * G.adjMatrix ℤ
      let Q := cubicNonneighborFinset G a
      ∀ b ∈ Q, A3 a b = c ∨ A3 a b = c + 1) :
    let A3 := G.adjMatrix ℤ * G.adjMatrix ℤ * G.adjMatrix ℤ
    let Q := cubicNonneighborFinset G a
    (d : ℤ) ^ 3 - (d : ℤ) * (2 * (d : ℤ) - 1) -
          (c + 1) * (Q.card : ℤ) ≤ A3 a a ∧
      A3 a a ≤
        (d : ℤ) ^ 3 - (d : ℤ) * (2 * (d : ℤ) - 1) -
          c * (Q.card : ℤ) := by
  classical
  dsimp only at hlevels ⊢
  let A3 := G.adjMatrix ℤ * G.adjMatrix ℤ * G.adjMatrix ℤ
  let Q := cubicNonneighborFinset G a
  have hcensus := twoLevel_upper_card_eq_sum_sub
    Q (fun b => A3 a b) c hlevels
  have hmass := c4Free_regular_cubicNonneighborMass_eq
    G hfree d hreg a
  change (∑ b ∈ Q, A3 a b) =
    (d : ℤ) ^ 3 - (d : ℤ) * (2 * (d : ℤ) - 1) - A3 a a at hmass
  have hcensus' :
      ((Q.filter fun b => A3 a b = c + 1).card : ℤ) =
        (d : ℤ) ^ 3 - (d : ℤ) * (2 * (d : ℤ) - 1) - A3 a a -
          c * (Q.card : ℤ) := by
    calc
      _ = (∑ b ∈ Q, A3 a b) - c * (Q.card : ℤ) := hcensus
      _ = _ := by rw [hmass]
  have hnonneg : (0 : ℤ) ≤
      ((Q.filter fun b => A3 a b = c + 1).card : ℤ) := by omega
  have hleNat : (Q.filter fun b => A3 a b = c + 1).card ≤ Q.card :=
    Finset.card_filter_le _ _
  have hle : ((Q.filter fun b => A3 a b = c + 1).card : ℤ) ≤
      (Q.card : ℤ) := by exact_mod_cast hleNat
  have hlocal :
      (d : ℤ) ^ 3 - (d : ℤ) * (2 * (d : ℤ) - 1) -
            (c + 1) * (Q.card : ℤ) ≤ A3 a a ∧
        A3 a a ≤
          (d : ℤ) ^ 3 - (d : ℤ) * (2 * (d : ℤ) - 1) -
            c * (Q.card : ℤ) := by
    constructor
    · rw [show (c + 1) * (Q.card : ℤ) =
          c * (Q.card : ℤ) + (Q.card : ℤ) by ring]
      omega
    · omega
  simpa only [A3, Q] using hlocal

/-- Equality in the arbitrary-center row lower bound therefore forces the
same explicit diagonal interval. -/
theorem regular_c4Free_sharp_cube_row_diag_interval
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G) (d : ℕ)
    (hreg : ∀ x, G.degree x = d) (c : ℤ) (a : V)
    (hsharp :
      let A3 := G.adjMatrix ℤ * G.adjMatrix ℤ * G.adjMatrix ℤ
      let Q := cubicNonneighborFinset G a
      (d : ℤ) * (2 * (d : ℤ) - 1) ^ 2 + (A3 a a) ^ 2 +
          (2 * c + 1) *
            ((d : ℤ) ^ 3 - (d : ℤ) * (2 * (d : ℤ) - 1) - A3 a a) -
          c * (c + 1) * (Q.card : ℤ) =
        ∑ b, (A3 a b) ^ 2) :
    let A3 := G.adjMatrix ℤ * G.adjMatrix ℤ * G.adjMatrix ℤ
    let Q := cubicNonneighborFinset G a
    (d : ℤ) ^ 3 - (d : ℤ) * (2 * (d : ℤ) - 1) -
          (c + 1) * (Q.card : ℤ) ≤ A3 a a ∧
      A3 a a ≤
        (d : ℤ) ^ 3 - (d : ℤ) * (2 * (d : ℤ) - 1) -
          c * (Q.card : ℤ) := by
  have hlevels :=
    (regular_c4Free_cube_row_square_baseline_eq_iff
      G hfree d hreg c a).mp hsharp
  exact regular_c4Free_twoLevel_cube_row_diag_interval
    G hfree d hreg c a hlevels

end


end Erdos85

#print axioms Erdos85.regular_c4Free_twoLevel_cube_row_diag_interval
#print axioms Erdos85.regular_c4Free_sharp_cube_row_diag_interval
