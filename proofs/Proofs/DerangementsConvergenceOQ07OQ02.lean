/-
  Binomial (Möbius) inversion of the fixed-point convolution:
  the closed-form derangement count

      D(n) = Σ_{k=0}^{n} (−1)^k · C(n,k) · (n−k)!.

  Open question: derangements-convergence-oq-07-oq-02

  ## Context

  The parent file `DerangementsConvergenceOQ07.lean` proves the *fixed-point
  convolution identity*

      n! = Σ_{k=0}^{n} C(n,k) · D(n−k),                         (parent)

  where `D = Nat.numDerangements`.  Reindexing `k ↦ n−k` turns this into the
  statement that the factorial sequence is the **binomial transform** of the
  derangement sequence:

      n! = Σ_{i=0}^{n} C(n,i) · D(i).

  This file *inverts* that relation.  Binomial (a.k.a. Möbius) inversion of the
  binomial transform yields the classical closed form

      D(n) = Σ_{k=0}^{n} (−1)^k · C(n,k) · (n−k)!.

  Mathlib already contains a closed form for `numDerangements`
  (`Nat.numDerangements_sum`, phrased with `ascFactorial`), but it is proved from
  the *recursion* `D(n+2) = (n+1)(D(n+1) + D(n))`, not by inverting the
  convolution.  The content added here is:

  * `binomial_inversion` — a general, self-contained binomial-inversion theorem
    over `ℤ`: if `G` is the binomial transform of `F`, then `F` is recovered by
    the signed inverse transform.  This is the reusable piece.
  * `alternating_choose_mul_choose` — the orthogonality relation
    `Σ_i (−1)^{n−i} C(n,i) C(i,j) = [j = n]` that powers the inversion.
  * `numDerangements_eq_alternating_sum` / `numDerangements_closed_form` — the
    derangement closed form obtained by applying the inversion theorem to the
    parent convolution.

  ## Main results
  - `alternating_choose_mul_choose` : orthogonality of the binomial kernel
  - `binomial_inversion`            : `G = binom transform F ⟹ F = signed inverse`
  - `numDerangements_eq_alternating_sum` : `D(n) = Σ (−1)^k C(n,k)(n−k)!`
-/
import Proofs.DerangementsConvergenceOQ07
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic

open Finset Nat
open scoped BigOperators

namespace DerangementsInversion

/-! ### Orthogonality of the binomial kernel -/

/-- **Orthogonality relation.**  For `j ≤ n`,
`Σ_{i=j}^{n} (−1)^{n−i} · C(n,i) · C(i,j) = [j = n]`.

This is the statement that the signed binomial matrix is the inverse of the
binomial matrix.  The proof uses the subset-of-a-subset identity
`C(n,i)·C(i,j) = C(n,j)·C(n−j, i−j)` (`Nat.choose_mul`) to factor out `C(n,j)`,
reindexes `i = j + t`, and finishes with the alternating binomial sum
`Σ_t (−1)^t C(m,t) = [m = 0]` (`Int.alternating_sum_range_choose`). -/
theorem alternating_choose_mul_choose (n j : ℕ) (hj : j ≤ n) :
    ∑ i ∈ Finset.Icc j n, (-1 : ℤ) ^ (n - i) * (n.choose i : ℤ) * (i.choose j : ℤ)
      = if j = n then 1 else 0 := by
  -- Factor `C(n,i)·C(i,j) = C(n,j)·C(n−j, i−j)` on each term.
  have step1 : ∑ i ∈ Finset.Icc j n,
        (-1 : ℤ) ^ (n - i) * (n.choose i : ℤ) * (i.choose j : ℤ)
      = (n.choose j : ℤ) *
          ∑ i ∈ Finset.Icc j n, (-1 : ℤ) ^ (n - i) * ((n - j).choose (i - j) : ℤ) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    have hji : j ≤ i := (Finset.mem_Icc.mp hi).1
    have hcast : (n.choose i : ℤ) * (i.choose j : ℤ)
        = (n.choose j : ℤ) * ((n - j).choose (i - j) : ℤ) := by
      exact_mod_cast Nat.choose_mul hji
    rw [mul_assoc, hcast]; ring
  rw [step1]
  -- Reindex `i = j + t`, `t ∈ range (n + 1 - j)`.
  have hIco : Finset.Icc j n = Finset.Ico j (n + 1) := by
    ext x; simp [Finset.mem_Icc, Finset.mem_Ico, Nat.lt_succ_iff]
  rw [hIco, Finset.sum_Ico_eq_sum_range]
  -- Simplify the summand: `n − (j + t) = (n − j) − t` and `(j + t) − j = t`.
  have step2 : ∑ t ∈ range (n + 1 - j),
        (-1 : ℤ) ^ (n - (j + t)) * ((n - j).choose (j + t - j) : ℤ)
      = ∑ t ∈ range ((n - j) + 1),
        (-1 : ℤ) ^ ((n - j) - t) * ((n - j).choose t : ℤ) := by
    have hlen : n + 1 - j = (n - j) + 1 := by omega
    rw [hlen]
    apply Finset.sum_congr rfl
    intro t _
    have e1 : n - (j + t) = (n - j) - t := by omega
    have e2 : j + t - j = t := by omega
    rw [e1, e2]
  rw [step2]
  -- Pull `(−1)^{(n−j)−t} = (−1)^{n−j} · (−1)^t` and use the alternating sum.
  set m := n - j with hm
  have step3 : ∑ t ∈ range (m + 1), (-1 : ℤ) ^ (m - t) * (m.choose t : ℤ)
      = (-1 : ℤ) ^ m * ∑ t ∈ range (m + 1), ((-1 : ℤ) ^ t * (m.choose t : ℤ)) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro t ht
    have ht' : t ≤ m := Nat.lt_succ_iff.mp (Finset.mem_range.mp ht)
    have key : (-1 : ℤ) ^ m * (-1 : ℤ) ^ t = (-1 : ℤ) ^ (m - t) := by
      rw [← pow_add, show m + t = (m - t) + 2 * t by omega, pow_add, pow_mul,
        neg_one_sq, one_pow, mul_one]
    rw [← key]; ring
  rw [step3, Int.alternating_sum_range_choose]
  -- Case on whether `j = n` (equivalently `m = 0`).
  by_cases hjn : j = n
  · subst hjn
    simp [hm]
  · have hm0 : m ≠ 0 := by omega
    rw [if_neg hm0, if_neg hjn]
    ring

/-! ### General binomial inversion -/

/-- **Binomial inversion.**  If `G` is the binomial transform of `F`, i.e.
`G m = Σ_{i=0}^{m} C(m,i)·F i` for all `m`, then `F` is recovered by the signed
inverse transform: `F n = Σ_{i=0}^{n} (−1)^{n−i}·C(n,i)·G i`.

The proof expands `G` inside the inverse transform, swaps the order of summation,
and collapses the inner sum with the orthogonality relation
`alternating_choose_mul_choose`. -/
theorem binomial_inversion {F G : ℕ → ℤ}
    (h : ∀ m, G m = ∑ i ∈ range (m + 1), (m.choose i : ℤ) * F i) (n : ℕ) :
    F n = ∑ i ∈ range (n + 1), (-1 : ℤ) ^ (n - i) * (n.choose i : ℤ) * G i := by
  symm
  calc
    ∑ i ∈ range (n + 1), (-1 : ℤ) ^ (n - i) * (n.choose i : ℤ) * G i
        = ∑ i ∈ range (n + 1), ∑ j ∈ range (i + 1),
            (-1 : ℤ) ^ (n - i) * (n.choose i : ℤ) * (i.choose j : ℤ) * F j := by
          apply Finset.sum_congr rfl
          intro i _
          rw [h i, Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro j _
          ring
    _ = ∑ j ∈ range (n + 1), ∑ i ∈ Finset.Icc j n,
            (-1 : ℤ) ^ (n - i) * (n.choose i : ℤ) * (i.choose j : ℤ) * F j := by
          apply Finset.sum_comm'
          intro i j
          simp only [Finset.mem_range, Finset.mem_Icc, Nat.lt_succ_iff]
          omega
    _ = ∑ j ∈ range (n + 1), (if j = n then (1 : ℤ) else 0) * F j := by
          apply Finset.sum_congr rfl
          intro j hj
          rw [← Finset.sum_mul,
            alternating_choose_mul_choose n j (Nat.lt_succ_iff.mp (Finset.mem_range.mp hj))]
    _ = F n := by
          rw [Finset.sum_eq_single n]
          · rw [if_pos rfl, one_mul]
          · intro j _ hjn; rw [if_neg hjn, zero_mul]
          · intro hn; exact absurd (Finset.mem_range.mpr (Nat.lt_succ_self n)) hn

/-! ### The derangement closed form -/

/-- The parent convolution `n! = Σ C(n,k)·D(n−k)`, cast to `ℤ` and reindexed
`k ↦ n−k`, exhibits `n!` as the **binomial transform** of `numDerangements`:
`n! = Σ_{i=0}^{n} C(n,i)·D(i)`. -/
theorem factorial_eq_sum_choose_mul_numDerangements_aligned (m : ℕ) :
    (m ! : ℤ) = ∑ i ∈ range (m + 1), (m.choose i : ℤ) * (numDerangements i : ℤ) := by
  have hℕ := DerangementsConvolution.factorial_eq_sum_choose_mul_numDerangements m
  have hcast : (m ! : ℤ)
      = ∑ k ∈ range (m + 1), (m.choose k : ℤ) * (numDerangements (m - k) : ℤ) := by
    rw [hℕ]; push_cast; rfl
  rw [hcast, ← Finset.sum_range_reflect
        (fun i => (m.choose i : ℤ) * (numDerangements i : ℤ)) (m + 1)]
  apply Finset.sum_congr rfl
  intro k hk
  have hk' : k ≤ m := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
  have h1 : m + 1 - 1 - k = m - k := by omega
  rw [h1, Nat.choose_symm hk']

/-- **Derangement closed form via binomial inversion.**
`D(n) = Σ_{k=0}^{n} (−1)^k · C(n,k) · (n−k)!`, where `D = Nat.numDerangements`.

Obtained by inverting the fixed-point convolution of the parent file
(`factorial_eq_sum_choose_mul_numDerangements_aligned`) with `binomial_inversion`,
then reflecting the summation index `i ↦ n − i`. -/
theorem numDerangements_eq_alternating_sum (n : ℕ) :
    (numDerangements n : ℤ)
      = ∑ k ∈ range (n + 1), (-1 : ℤ) ^ k * (n.choose k : ℤ) * ((n - k)! : ℤ) := by
  have hinv := binomial_inversion
      (F := fun i => (numDerangements i : ℤ))
      (G := fun m => (m ! : ℤ))
      (fun m => factorial_eq_sum_choose_mul_numDerangements_aligned m) n
  rw [hinv, ← Finset.sum_range_reflect
        (fun k => (-1 : ℤ) ^ k * (n.choose k : ℤ) * ((n - k)! : ℤ)) (n + 1)]
  apply Finset.sum_congr rfl
  intro i hi
  have hi' : i ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
  have h1 : n + 1 - 1 - i = n - i := by omega
  have h2 : n - (n - i) = i := by omega
  rw [h1, Nat.choose_symm hi', h2]

/-- The closed form, restated with the exact phrasing of the open question. -/
theorem numDerangements_closed_form (n : ℕ) :
    (numDerangements n : ℤ)
      = ∑ k ∈ range (n + 1), (-1 : ℤ) ^ k * (n.choose k : ℤ) * ((n - k)! : ℤ) :=
  numDerangements_eq_alternating_sum n

/-! ### Sanity checks -/

/-- The `n = 4` instance of the closed form. -/
example :
    (numDerangements 4 : ℤ)
      = ∑ k ∈ range 5, (-1 : ℤ) ^ k * ((4 : ℕ).choose k : ℤ) * ((4 - k)! : ℤ) :=
  numDerangements_eq_alternating_sum 4

/-- The right-hand side of the closed form evaluates to `9 = D(4)`:
`24 − 24 + 12 − 4 + 1 = 9`. -/
example :
    (∑ k ∈ range 5, (-1 : ℤ) ^ k * ((4 : ℕ).choose k : ℤ) * ((4 - k)! : ℤ)) = 9 := by
  norm_num [Finset.sum_range_succ, Nat.factorial, Nat.choose]

/-- Hence `D(4) = 9`, derived from the inversion formula rather than the
recursion. -/
example : (numDerangements 4 : ℤ) = 9 := by
  rw [numDerangements_eq_alternating_sum 4]
  norm_num [Finset.sum_range_succ, Nat.factorial, Nat.choose]

end DerangementsInversion
