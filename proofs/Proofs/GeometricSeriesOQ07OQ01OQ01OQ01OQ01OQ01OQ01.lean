/-
# Geometric series, open question oq-07-oq-01-oq-01-oq-01-oq-01-oq-01-oq-01:
# The third moment and vanishing skewness of the descent statistic

The Eulerian number `⟨n,k⟩` (`eulerian n k`) counts permutations of `{1,…,n}` with exactly `k`
descents, and the row `(⟨n,0⟩,…,⟨n,n−1⟩)` is the distribution of the descent statistic `X` of a
uniformly random permutation.  The parent entry
(`geometric-series-oq-07-oq-01-oq-01-oq-01-oq-01-oq-01`) computed the **mean** `(n−1)/2` and the
**variance** `(n+1)/12` — the first and second moments — using a single **moment-transfer engine**
(`moment_transfer`), which turns a weighted row-`(n+1)` sum into a weighted row-`n` sum.

This entry pushes the same engine to the **third moment** and extracts the *shape* consequence that
the descent distribution has **zero skewness**:

* `eulerian_M3_succ`      : the third-moment recurrence
  `M₃(n+1) = (n−2)·M₃(n) + 3(n−1)·M₂(n) + (3n−1)·M₁(n) + n·M₀(n)`, read straight off
  `moment_transfer` with weight `w(k) = k³` (the coefficient `i³(i+1)+(i+1)³(n−i)` simplifies to
  `(n−2)i³ + 3(n−1)i² + (3n−1)i + n`);
* `eulerian_third_moment` : the closed form `8·∑ₖ k³·⟨n,k⟩ = (n−1)(n²−n+2)·n!` for `n ≥ 2`, by
  induction from the base row `n = 2`, feeding in the row sum `M₀ = n!` and the parent's first and
  second moments;
* `eulerian_third_central_moment_zero` : `∑ₖ (2k−(n−1))³·⟨n,k⟩ = 0` for `n ≥ 1`.  Since `2k−(n−1)`
  is (twice) the deviation of `k` from the mean, this is the vanishing of the third central moment:
  the descent distribution is **symmetric**, so its skewness is `0`.  It follows purely from the
  palindromy `⟨n,k⟩ = ⟨n,n−1−k⟩`: reflecting `k ↦ n−1−k` negates the odd weight `(2k−(n−1))³` while
  fixing `⟨n,k⟩`, so the sum equals its own negative.

For example row `3` is `1,4,1`: `∑ k³·⟨3,k⟩ = 0+4+8 = 12`, and `8·12 = 96 = (3−1)(9−3+2)·3! = 2·8·6`;
while `∑ₖ (2k−2)³·⟨3,k⟩ = (−2)³·1 + 0³·4 + 2³·1 = −8+0+8 = 0`, confirming the symmetry.

Everything is `0`-axiom (`propext` / `Classical.choice` / `Quot.sound` only) and `sorry`-free.
-/
import Mathlib
import Proofs.GeometricSeriesOQ07OQ01OQ01OQ01OQ01
import Proofs.GeometricSeriesOQ07OQ01OQ01OQ01OQ05
import Proofs.GeometricSeriesOQ07OQ01OQ01OQ01OQ01OQ01

namespace GeometricSeriesOQ07OQ01OQ01OQ01OQ01OQ01OQ01

open Nat Finset GeometricSeriesOQ07OQ01OQ01OQ01 GeometricSeriesOQ07OQ01OQ01OQ01OQ01
  GeometricSeriesOQ07OQ01OQ01OQ01OQ05 GeometricSeriesOQ07OQ01OQ01OQ01OQ01OQ01

/-! ## The third moment via the moment recurrence -/

/-- The third-moment recurrence, read off `moment_transfer` with weight `w(k) = k³`:
`M₃(n+1) = (n−2)·M₃(n) + 3(n−1)·M₂(n) + (3n−1)·M₁(n) + n·M₀(n)`.  The transfer coefficient
`i³·(i+1) + (i+1)³·(n−i)` simplifies to `(n−2)i³ + 3(n−1)i² + (3n−1)i + n`. -/
theorem eulerian_M3_succ (n : ℕ) :
    ∑ k ∈ range (n + 2), (k : ℤ) ^ 3 * (eulerian (n + 1) k : ℤ)
      = ((n : ℤ) - 2) * (∑ k ∈ range (n + 1), (k : ℤ) ^ 3 * (eulerian n k : ℤ))
        + 3 * ((n : ℤ) - 1) * (∑ k ∈ range (n + 1), (k : ℤ) ^ 2 * (eulerian n k : ℤ))
        + (3 * (n : ℤ) - 1) * (∑ k ∈ range (n + 1), (k : ℤ) * (eulerian n k : ℤ))
        + (n : ℤ) * (∑ k ∈ range (n + 1), (eulerian n k : ℤ)) := by
  rw [moment_transfer (fun k => (k : ℤ) ^ 3) n]
  rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum,
    ← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  push_cast
  ring

/-- **Third moment of the descent statistic.**  `8·∑ₖ k³·⟨n,k⟩ = (n−1)(n²−n+2)·n!` for `n ≥ 2`.
Induction on `n` from the base row `n = 2`, stepping with `eulerian_M3_succ` and feeding in the row
sum `M₀ = n!`, the first moment `M₁`, and the second moment `M₂`. -/
theorem eulerian_third_moment (n : ℕ) (hn : 2 ≤ n) :
    8 * ∑ k ∈ range (n + 1), (k : ℤ) ^ 3 * (eulerian n k : ℤ)
      = ((n : ℤ) - 1) * ((n : ℤ) ^ 2 - n + 2) * (n ! : ℤ) := by
  induction n, hn using Nat.le_induction with
  | base => decide
  | succ n hn ih =>
    have hM0 : ∑ k ∈ range (n + 1), (eulerian n k : ℤ) = (n ! : ℤ) := eulerian_M0 n
    have hM1 : 2 * ∑ k ∈ range (n + 1), (k : ℤ) * (eulerian n k : ℤ) = ((n : ℤ) - 1) * (n ! : ℤ) :=
      eulerian_first_moment n (by omega)
    have hM2 : 12 * ∑ k ∈ range (n + 1), (k : ℤ) ^ 2 * (eulerian n k : ℤ)
        = (n ! : ℤ) * (3 * (n : ℤ) ^ 2 - 5 * n + 4) := eulerian_second_moment n hn
    rw [eulerian_M3_succ, hM0, Nat.factorial_succ]
    push_cast
    linear_combination ((n : ℤ) - 2) * ih + 2 * ((n : ℤ) - 1) * hM2 + 4 * (3 * (n : ℤ) - 1) * hM1

/-! ## Vanishing skewness: the descent distribution is symmetric -/

/-- **Third central moment of the descent statistic is zero.**  `∑ₖ (2k−(n−1))³·⟨n,k⟩ = 0` for
`n ≥ 1`.  As `2k−(n−1)` is twice the deviation of `k` from the mean `(n−1)/2`, this says the third
central moment — hence the skewness — vanishes: the descent distribution is symmetric.  Proof: the
reflection `k ↦ n−1−k` negates the odd weight `(2k−(n−1))³` and fixes `⟨n,k⟩` by palindromy, so the
sum equals its own negative. -/
theorem eulerian_third_central_moment_zero (n : ℕ) (hn : 1 ≤ n) :
    ∑ k ∈ range n, (2 * (k : ℤ) - ((n : ℤ) - 1)) ^ 3 * (eulerian n k : ℤ) = 0 := by
  set f : ℕ → ℤ := fun k => (2 * (k : ℤ) - ((n : ℤ) - 1)) ^ 3 * (eulerian n k : ℤ) with hf
  have hrefl : ∑ k ∈ range n, f (n - 1 - k) = ∑ k ∈ range n, f k :=
    Finset.sum_range_reflect f n
  have hodd : ∀ k ∈ range n, f (n - 1 - k) = - f k := by
    intro k hk
    rw [mem_range] at hk
    have hpal : eulerian n (n - 1 - k) = eulerian n k := (eulerian_palindrome' hn hk).symm
    have hcast : ((n - 1 - k : ℕ) : ℤ) = (n : ℤ) - 1 - (k : ℤ) := by
      rw [Nat.cast_sub (by omega : k ≤ n - 1), Nat.cast_sub (by omega : 1 ≤ n)]
      push_cast; ring
    simp only [hf]
    rw [hpal, hcast]; ring
  have hsum2 : ∑ k ∈ range n, f k + ∑ k ∈ range n, f k = 0 := by
    nth_rewrite 1 [← hrefl]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_eq_zero
    intro k hk
    rw [hodd k hk]; ring
  simp only [hf] at hsum2 ⊢
  linarith

/-! ## Corroboration on concrete rows -/

-- Third moment: row 3 `1,4,1` has `∑ k³·⟨3,k⟩ = 12`, and `8·12 = 96 = (3−1)(9−3+2)·3!`.
example : 8 * ∑ k ∈ range 4, (k : ℤ) ^ 3 * (eulerian 3 k : ℤ)
    = ((3 : ℤ) - 1) * ((3 : ℤ) ^ 2 - 3 + 2) * (3 ! : ℤ) := by decide
-- Third moment: row 4 `1,11,11,1` has `∑ k³·⟨4,k⟩ = 126`, and `8·126 = 1008 = (4−1)(16−4+2)·4!`.
example : 8 * ∑ k ∈ range 5, (k : ℤ) ^ 3 * (eulerian 4 k : ℤ)
    = ((4 : ℤ) - 1) * ((4 : ℤ) ^ 2 - 4 + 2) * (4 ! : ℤ) := by decide
-- Vanishing skewness: row 4 has `∑ₖ (2k−3)³·⟨4,k⟩ = 0`.
example : ∑ k ∈ range 4, (2 * (k : ℤ) - ((4 : ℤ) - 1)) ^ 3 * (eulerian 4 k : ℤ) = 0 := by decide

end GeometricSeriesOQ07OQ01OQ01OQ01OQ01OQ01OQ01
