import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Data.Matrix.Basic
import Mathlib.Tactic

/-!
# Coefficient bounds in the exact square quotient

At the surviving square boundary write `p = N + 2s` and put `B = Q+sI`.
The weighted quotient identities become

* every row of `B` sums to `p`;
* `aᵢ Bᵢⱼ = aⱼ Bⱼᵢ` (detailed balance);
* `(B²)ᵢᵢ = 2s Bᵢᵢ + p aᵢ`;
* `∑ aᵢ = N`.

Weighted Cauchy--Schwarz then gives the sharp pointwise estimate
`p aᵢ ≤ N Bᵢᵢ`.  This is the Markov/PSD constraint needed to turn the
exact arithmetic factorization into bounds on individual component orders.
-/

namespace Erdos85

noncomputable section

/-- **Exact-square coefficient bound.**  A positive reversible kernel with
the exact square-boundary diagonal identity satisfies
`p * a i ≤ N * B i i` at every state. -/
theorem weightedKernel_coefficient_le_diagonal
    {I : Type*} [Fintype I]
    (B : I → I → ℚ) (a : I → ℚ) (p N s : ℚ)
    (ha : ∀ i, 0 < a i) (hN : 0 < N) (hs : 0 < s)
    (haSum : ∑ i, a i = N)
    (hrow : ∀ i, ∑ j, B i j = p)
    (hbalance : ∀ i j, a i * B i j = a j * B j i)
    (hdiag : ∀ i, ∑ j, B i j * B j i =
      2 * s * B i i + p * a i)
    (hp : p = N + 2 * s) (i : I) :
    p * a i ≤ N * B i i := by
  have hCS := Finset.sq_sum_div_le_sum_sq_div
    (Finset.univ : Finset I) (fun j ↦ B i j) (g := fun j ↦ a j)
    (fun j _ ↦ ha j)
  rw [hrow i, haSum] at hCS
  have hCS' : p ^ 2 ≤ N * ∑ j, B i j ^ 2 / a j :=
    by simpa [mul_comm] using (div_le_iff₀ hN).mp hCS
  have hweighted :
      a i * (∑ j, B i j ^ 2 / a j) =
        ∑ j, B i j * B j i := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    have haj : a j ≠ 0 := (ha j).ne'
    calc
      a i * (B i j ^ 2 / a j) =
          (B i j * (a i * B i j)) / a j := by ring
      _ = (B i j * (a j * B j i)) / a j := by rw [hbalance i j]
      _ = B i j * B j i := by field_simp
  have hai : 0 ≤ a i := (ha i).le
  have hmul := mul_le_mul_of_nonneg_left hCS' hai
  have hmul' : a i * p ^ 2 ≤
      N * (a i * (∑ j, B i j ^ 2 / a j)) := by
    calc
      a i * p ^ 2 ≤ a i * (N * ∑ j, B i j ^ 2 / a j) := hmul
      _ = N * (a i * (∑ j, B i j ^ 2 / a j)) := by ring
  rw [hweighted, hdiag i] at hmul'
  rw [hp] at hmul hmul' ⊢
  nlinarith [hmul']

end

end Erdos85
