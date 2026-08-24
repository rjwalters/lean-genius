import Proofs.Erdos85CanonicalExceptionalPopulation
import Proofs.Erdos85BinarySquareSignedEigenvectorSupport

/-!
# Global mass balance for exceptional occupancies

Summing the named sparse equation `A(cutSign S)=q z` in a `q`-regular graph
shows that the exceptional signed mass equals the shore-sign mass.  This
determines the difference between the canonical full and empty populations.
-/

open SimpleGraph Matrix

namespace Erdos85

/-- The sparse exceptional sign has the same coordinate sum as the shore
sign from which it is produced. -/
theorem sum_exceptionalOccupancySign_eq_cutSign
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {q : ℕ} (hq : 0 < q) (hreg : ∀ x, G.degree x = q)
    (S : Finset V)
    (htri : ∀ v,
      (G.neighborFinset v ∩ S).card = 0 ∨
      2 * (G.neighborFinset v ∩ S).card = q ∨
      (G.neighborFinset v ∩ S).card = q) :
    ∑ x : V, exceptionalOccupancySign G S q x =
      2 * (S.card : ℤ) - Fintype.card V := by
  let cut : V → ℤ := fun x => if x ∈ S then 1 else -1
  let z : V → ℤ := exceptionalOccupancySign G S q
  have hAx : (G.adjMatrix ℤ).mulVec cut = (q : ℤ) • z := by
    simpa [cut, z] using
      cutSign_adjMatrix_mulVec_eq_exceptionalOccupancySign
        G hq hreg S htri
  have hsumEq := congrArg (fun f : V → ℤ => ∑ x, f x) hAx
  rw [sum_adjMatrix_mulVec_of_regular_int G q hreg cut] at hsumEq
  have hright : (∑ x, ((q : ℤ) • z) x) = (q : ℤ) * ∑ x, z x := by
    simp [Pi.smul_apply, Finset.mul_sum]
  rw [hright] at hsumEq
  have hqZ : (q : ℤ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hq)
  have hsumCut : ∑ x, cut x = 2 * (S.card : ℤ) - Fintype.card V := by
    simpa [cut] using sum_cutSign S
  have hcancel : ∑ x, cut x = ∑ x, z x := by
    exact (mul_left_cancel₀ hqZ hsumEq)
  rw [← hcancel, hsumCut]

/-- Consequently the full-minus-empty population is the shore displacement
`2|S|-|V|`. -/
theorem fullLineCenters_card_sub_emptyLineCenters_card_eq_cutDisplacement
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {q : ℕ} (hq : 0 < q) (hreg : ∀ x, G.degree x = q)
    (S : Finset V)
    (htri : ∀ v,
      (G.neighborFinset v ∩ S).card = 0 ∨
      2 * (G.neighborFinset v ∩ S).card = q ∨
      (G.neighborFinset v ∩ S).card = q) :
    ((fullLineCenters G S q).card : ℤ) -
        (emptyLineCenters G S).card =
      2 * (S.card : ℤ) - Fintype.card V := by
  rw [← sum_exceptionalOccupancySign_eq_full_sub_empty G S hq]
  exact sum_exceptionalOccupancySign_eq_cutSign G hq hreg S htri

end Erdos85

#print axioms Erdos85.sum_exceptionalOccupancySign_eq_cutSign
#print axioms Erdos85.fullLineCenters_card_sub_emptyLineCenters_card_eq_cutDisplacement
