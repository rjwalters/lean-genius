import Proofs.Erdos85AntipodalCommutatorRows

/-!
# Global cut bound from antipodal commutator rows

The row support bounds aggregate into a global lower bound.  The quantity
`excessThreeCrossIncidence` counts opposite-sector ambient incidences; its
sum counts every cross-sector edge twice.
-/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- A filtered set of ordered pairs decomposes as the sum of its fibers. -/
theorem card_filter_univ_product_eq_sum_card_filter
    {α β : Type*} [Fintype α] [Fintype β]
    [DecidableEq α] [DecidableEq β] (P : α × β → Prop)
    [DecidablePred P] :
    ((Finset.univ.filter P).card : ℤ) =
      ∑ x : α, ((Finset.univ.filter fun y : β => P (x, y)).card : ℤ) := by
  rw [Finset.card_filter]
  push_cast
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro x _
  rw [Finset.card_filter]
  push_cast
  apply Finset.sum_congr rfl
  intro y _
  rfl

/-- The number of ambient incidences from `x` to the opposite
triangle-free-degree sector, expressed in the orientation convenient for
the row-sum formula. -/
def excessThreeCrossIncidence
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (d : ℕ) (x : V) : ℤ :=
  let ℓ := ((G.neighborFinset x).filter fun z =>
    (triangleFreeEdgeGraph G).degree z = 1).card
  if (triangleFreeEdgeGraph G).degree x = 1
    then (d : ℤ) - (ℓ : ℤ)
    else (ℓ : ℤ)

/-- **Global cross-incidence bound.**  The exact commutator support dominates
twice the total number of opposite-sector incidences. -/
theorem two_mul_sum_crossIncidence_le_commutator_support
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) {d : ℕ} (hd : 7 ≤ d) (hodd : Odd d)
    (hreg : ∀ z, G.degree z = d)
    (hcard : Fintype.card V = d * (d - 1) + 6) :
    let A := G.adjMatrix ℤ
    let C := (antipodalGraph G).adjMatrix ℤ
    2 * ∑ x : V, excessThreeCrossIncidence G d x ≤
      ((Finset.univ.filter fun p : V × V =>
        (A * C - C * A) p.1 p.2 ≠ 0).card : ℤ) := by
  dsimp only
  let A := G.adjMatrix ℤ
  let C := (antipodalGraph G).adjMatrix ℤ
  have hrow : ∀ x : V,
      2 * excessThreeCrossIncidence G d x ≤
        ((Finset.univ.filter fun y : V =>
          (A * C - C * A) x y ≠ 0).card : ℤ) := by
    intro x
    rcases excessThree_antipodal_commutator_row_support_lower
        G hfree hd hodd hreg hcard x with hx | hx
    · simpa [excessThreeCrossIncidence, hx.1, A, C] using hx.2
    · have hne : (triangleFreeEdgeGraph G).degree x ≠ 1 := by
        omega
      simpa [excessThreeCrossIncidence, hne, A, C] using hx.2
  calc
    2 * ∑ x : V, excessThreeCrossIncidence G d x =
        ∑ x : V, 2 * excessThreeCrossIncidence G d x := by
      rw [Finset.mul_sum]
    _ ≤ ∑ x : V, ((Finset.univ.filter fun y : V =>
          (A * C - C * A) x y ≠ 0).card : ℤ) :=
      Finset.sum_le_sum fun x _ => hrow x
    _ = ((Finset.univ.filter fun p : V × V =>
          (A * C - C * A) p.1 p.2 ≠ 0).card : ℤ) := by
      rw [card_filter_univ_product_eq_sum_card_filter]

/-- **Pinned cross-incidence budget.**  Substituting the exact global
commutator support count bounds the entire ambient cut between the two
triangle-free degree sectors. -/
theorem sum_crossIncidence_le_excessThree_gap
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) {d : ℕ} (hd : 7 ≤ d) (hodd : Odd d)
    (hreg : ∀ z, G.degree z = d)
    (hcard : Fintype.card V = d * (d - 1) + 6) :
    let a := (Finset.univ.filter fun x : V =>
      (triangleFreeEdgeGraph G).degree x = 3).card
    ∑ x : V, excessThreeCrossIncidence G d x ≤
      (d - 1 : ℤ) * (Fintype.card V : ℤ) +
        (2 * (d : ℤ) - 8) * (a : ℤ) := by
  dsimp only
  have hcut := two_mul_sum_crossIncidence_le_commutator_support
    G hfree hd hodd hreg hcard
  have hsupp := card_antipodal_commutator_support_excessThree
    G hfree hd hodd hreg hcard
  dsimp only at hcut hsupp
  rw [hsupp] at hcut
  omega

end

end Erdos85
