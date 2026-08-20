import Proofs.Erdos85RegularCubicGlobalExcessEquality

/-! # Exact census in a sharp cubic row

Node: F.3 GENERALIZATION.  Two-level support plus the first-moment ledger
determines the multiplicity of the upper level exactly.
-/

open Finset SimpleGraph Matrix

namespace Erdos85

noncomputable section

/-- On a finite two-level integer family `{c,c+1}`, the number of upper-level
entries is its total mass minus `c` times its cardinality. -/
theorem twoLevel_upper_card_eq_sum_sub
    {X : Type*} (s : Finset X) (f : X → ℤ) (c : ℤ)
    (hlevels : ∀ x ∈ s, f x = c ∨ f x = c + 1) :
    ((s.filter fun x => f x = c + 1).card : ℤ) =
      (∑ x ∈ s, f x) - c * (s.card : ℤ) := by
  classical
  have hpoint (x : X) (hx : x ∈ s) :
      f x = c + if f x = c + 1 then 1 else 0 := by
    rcases hlevels x hx with hxc | hxc
    · rw [hxc]
      by_cases hc : c = c + 1
      · omega
      · simp [hc]
    · simp [hxc]
  have hsum : (∑ x ∈ s, f x) =
      c * (s.card : ℤ) +
        ((s.filter fun x => f x = c + 1).card : ℤ) := by
    calc
      _ = ∑ x ∈ s, (c + if f x = c + 1 then 1 else 0) := by
        apply Finset.sum_congr rfl
        intro x hx
        exact hpoint x hx
      _ = c * (s.card : ℤ) +
          ((s.filter fun x => f x = c + 1).card : ℤ) := by
        rw [Finset.sum_add_distrib]
        have hbool : (∑ x ∈ s, if f x = c + 1 then (1 : ℤ) else 0) =
            ((s.filter fun x => f x = c + 1).card : ℤ) := by
          rw [Finset.sum_boole]
        rw [hbool]
        simp
        ring
  omega

/-- If a C4-free regular cubic row attains the arbitrary-center lower bound,
the exact number of nonneighbor entries equal to `c+1` is forced by its
diagonal cubic entry. -/
theorem regular_c4Free_sharp_cube_row_upper_card
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
    (((Q.filter fun b => A3 a b = c + 1).card : ℕ) : ℤ) =
      (d : ℤ) ^ 3 - (d : ℤ) * (2 * (d : ℤ) - 1) - A3 a a -
        c * (Q.card : ℤ) := by
  classical
  dsimp only at hsharp ⊢
  let A3 := G.adjMatrix ℤ * G.adjMatrix ℤ * G.adjMatrix ℤ
  let Q := cubicNonneighborFinset G a
  have hlevels :=
    (regular_c4Free_cube_row_square_baseline_eq_iff
      G hfree d hreg c a).mp hsharp
  have hcensus := twoLevel_upper_card_eq_sum_sub
    Q (fun b => A3 a b) c hlevels
  have hmass := c4Free_regular_cubicNonneighborMass_eq
    G hfree d hreg a
  change (∑ b ∈ Q, A3 a b) =
    (d : ℤ) ^ 3 - (d : ℤ) * (2 * (d : ℤ) - 1) - A3 a a at hmass
  rw [hmass] at hcensus
  exact hcensus

end


end Erdos85

#print axioms Erdos85.twoLevel_upper_card_eq_sum_sub
#print axioms Erdos85.regular_c4Free_sharp_cube_row_upper_card
