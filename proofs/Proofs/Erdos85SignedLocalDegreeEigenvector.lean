import Mathlib.Combinatorics.SimpleGraph.AdjMatrix

/-! # Signed local degree profiles as graph eigenvectors -/

open Finset SimpleGraph Matrix

namespace Erdos85

/-- A `±1` signing with constant same-sign degree `a` and opposite-sign
degree `b` is an adjacency eigenvector of eigenvalue `a-b`.  This elementary
adapter lets structural sign censuses feed the spectral classification
without rebuilding filtered-sum arithmetic in every graph model. -/
theorem adjMatrix_mulVec_eq_same_sub_opposite
    {V : Type*} [Fintype V] [DecidableEq V]
    (R : SimpleGraph V) [DecidableRel R.Adj]
    (s : V → ℤ) (a b : ℕ)
    (hsign : ∀ x, s x = -1 ∨ s x = 1)
    (hsame : ∀ x,
      ((R.neighborFinset x).filter fun y ↦ s y = s x).card = a)
    (hopp : ∀ x,
      ((R.neighborFinset x).filter fun y ↦ s y ≠ s x).card = b) :
    (R.adjMatrix ℤ).mulVec s = fun x ↦ ((a : ℤ) - b) * s x := by
  funext x
  rw [SimpleGraph.adjMatrix_mulVec_apply]
  let N := R.neighborFinset x
  let Ns := N.filter fun y ↦ s y = s x
  let No := N.filter fun y ↦ s y ≠ s x
  have hsplit : ∑ y ∈ N, s y = (∑ y ∈ Ns, s y) + ∑ y ∈ No, s y := by
    rw [← Finset.sum_filter_add_sum_filter_not N (fun y ↦ s y = s x)]
  have hsameSum : ∑ y ∈ Ns, s y = (a : ℤ) * s x := by
    calc
      _ = ∑ _y ∈ Ns, s x := Finset.sum_congr rfl fun y hy ↦
        (Finset.mem_filter.mp hy).2
      _ = (Ns.card : ℤ) * s x := by simp
      _ = (a : ℤ) * s x := by rw [hsame x]
  have hoppSign : ∀ y ∈ No, s y = -s x := by
    intro y hy
    have hne := (Finset.mem_filter.mp hy).2
    rcases hsign x with hx | hx <;> rcases hsign y with hy | hy <;>
      simp_all
  have hoppSum : ∑ y ∈ No, s y = -(b : ℤ) * s x := by
    calc
      _ = ∑ _y ∈ No, -s x := Finset.sum_congr rfl hoppSign
      _ = -(No.card : ℤ) * s x := by simp
      _ = -(b : ℤ) * s x := by rw [hopp x]
  rw [hsplit, hsameSum, hoppSum]
  ring

end Erdos85

#print axioms Erdos85.adjMatrix_mulVec_eq_same_sub_opposite
