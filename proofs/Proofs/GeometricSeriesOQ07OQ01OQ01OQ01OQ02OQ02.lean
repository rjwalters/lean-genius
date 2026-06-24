import Mathlib
import Proofs.GeometricSeriesOQ07OQ01OQ01OQ01OQ02

/-
# Palindromic symmetry of the Eulerian numbers, from the explicit alternating sum

The parent entry **geometric-series-oq-07-oq-01-oq-01-oq-01-oq-02** established the explicit
inclusion–exclusion closed form of the Eulerian numbers,

  `⟨n,k⟩ = eulerianExplicit n k = ∑_{i=0}^{k} (-1)ⁱ · C(n+1,i) · (k+1-i)ⁿ`     (`eulerian_eq_explicit`).

This entry settles its declared open question **oq-02**: derive the **palindromic symmetry**

  `⟨n,k⟩ = ⟨n, n-1-k⟩`        (for `k < n`)

directly from the alternating sum, by the substitution `i ↦ n+1-i`.  This is an *analytic*
proof, complementary to the coefficient-extraction proof of palindromy recorded elsewhere in the
Eulerian lineage (sibling oq-05): it manipulates the explicit finite sum rather than the
generating polynomial.

## Method

The engine is the **finite-difference vanishing lemma** (`full_alt_sum_zero`):

  `∑_{i=0}^{n+1} (-1)ⁱ · C(n+1,i) · (k+1-i)ⁿ = 0`.

This is the `(n+1)`-st forward difference of the degree-`n` polynomial `x ↦ (k+1-x)ⁿ`, which
vanishes because the differencing order exceeds the degree
(`Polynomial.fwdDiff_iter_eq_zero_of_degree_lt`, expanded via `fwdDiff_iter_eq_sum_shift`).  The
*full* alternating sum runs `i = 0 … n+1`; its head `i = 0 … k` is exactly `eulerianExplicit n k`.
Splitting the sum at `k+1` and reflecting the tail `i ↦ n+1-i` (`Finset.sum_range_reflect`) turns
the tail into `-eulerianExplicit n (n-1-k)` — the binomial symmetry `C(n+1,n+1-i)=C(n+1,i)`
supplies the reflected coefficients, `(k+1-(n+1-i)) = -((n-1-k)+1-i)` supplies the reflected base,
the parity factors collapse, and the single overhang term carries a factor `0ⁿ = 0` (using
`1 ≤ n`).  Hence `eulerianExplicit n k - eulerianExplicit n (n-1-k) = 0`.

As immediate corollaries we obtain the **non-negativity** of the explicit alternating sum
(`eulerianExplicit_nonneg`, the easy half of the sibling open question oq-01, since the sum equals
the cast of the natural-number count `⟨n,k⟩`), and the palindromy of the combinatorial Eulerian
numbers themselves (`eulerian_palindrome`).

Everything is machine-checked with no `sorry` and no new axioms.
-/

open Finset
open GeometricSeriesOQ07OQ01OQ01OQ01 GeometricSeriesOQ07OQ01OQ01OQ01OQ02

namespace GeometricSeriesOQ07OQ01OQ01OQ01OQ02OQ02

/-- **Non-negativity of the explicit Eulerian sum.** The alternating inclusion–exclusion sum
`∑_{i=0}^{k} (-1)ⁱ C(n+1,i)(k+1-i)ⁿ` is `≥ 0`, because it equals the cast of the combinatorial
count `⟨n,k⟩ : ℕ` (`eulerian_eq_explicit`). This is the easy half of the sibling open question
oq-01: the deeper "equals the number of permutations with `k` descents" remains a separate
combinatorial statement. -/
theorem eulerianExplicit_nonneg (n k : ℕ) : 0 ≤ eulerianExplicit n k := by
  rw [← eulerian_eq_explicit]
  exact_mod_cast Nat.zero_le _

/-- **Finite-difference vanishing.** The *full* alternating binomial sum (running all the way to
`i = n+1`, one past the support of `eulerianExplicit`) vanishes:

  `∑_{i=0}^{n+1} (-1)ⁱ · C(n+1,i) · (k+1-i)ⁿ = 0`.

It is the `(n+1)`-st forward difference of the degree-`n` polynomial `x ↦ (k+1-x)ⁿ`. -/
theorem full_alt_sum_zero (n k : ℕ) :
    ∑ i ∈ range (n + 2),
        (-1 : ℤ) ^ i * ((n + 1).choose i : ℤ) * ((k : ℤ) + 1 - i) ^ n = 0 := by
  -- The polynomial `P x = (k+1 - x)ⁿ`, of degree `n < n+1`.
  set P : Polynomial ℤ := (Polynomial.C ((k : ℤ) + 1) - Polynomial.X) ^ n with hP
  have hdeg : P.natDegree < n + 1 := by
    have hlin : (Polynomial.C ((k : ℤ) + 1) - Polynomial.X).natDegree = 1 := by
      rw [show Polynomial.C ((k : ℤ) + 1) - Polynomial.X
            = -(Polynomial.X - Polynomial.C ((k : ℤ) + 1)) from by ring,
          Polynomial.natDegree_neg, Polynomial.natDegree_X_sub_C]
    rw [hP, Polynomial.natDegree_pow, hlin, mul_one]
    omega
  -- Its `(n+1)`-st forward difference is the zero function.
  have hzero : (fwdDiff (1 : ℤ))^[n + 1] P.eval = 0 :=
    Polynomial.fwdDiff_iter_eq_zero_of_degree_lt hdeg
  -- Expand that difference at `0` as the alternating shift-sum.
  have hsum := fwdDiff_iter_eq_sum_shift (h := (1 : ℤ)) P.eval (n + 1) 0
  -- Identify the shift-sum (with sign `(-1)^(n+1-i)`) with a clean alternating sum.
  have hS' : (∑ i ∈ range (n + 2),
      (-1 : ℤ) ^ (n + 1 - i) * ((n + 1).choose i : ℤ) * ((k : ℤ) + 1 - i) ^ n) = 0 := by
    have hval : (fwdDiff (1 : ℤ))^[n + 1] P.eval 0 = 0 := by rw [hzero]; rfl
    rw [hsum] at hval
    refine Eq.trans ?_ hval
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [hP]
    simp only [zero_add, nsmul_eq_mul, mul_one, smul_eq_mul, Polynomial.eval_pow,
      Polynomial.eval_sub, Polynomial.eval_C, Polynomial.eval_X]
  -- Reinsert the global sign `(-1)^(n+1)` to recover the target sign `(-1)^i`.
  have hconv : (∑ i ∈ range (n + 2),
        (-1 : ℤ) ^ i * ((n + 1).choose i : ℤ) * ((k : ℤ) + 1 - i) ^ n)
      = (-1 : ℤ) ^ (n + 1) * ∑ i ∈ range (n + 2),
        (-1 : ℤ) ^ (n + 1 - i) * ((n + 1).choose i : ℤ) * ((k : ℤ) + 1 - i) ^ n := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun i hi => ?_)
    have hile : i ≤ n + 1 := by simp only [mem_range] at hi; omega
    have hsign : (-1 : ℤ) ^ (n + 1) * (-1 : ℤ) ^ (n + 1 - i) = (-1 : ℤ) ^ i := by
      rw [← pow_add, show n + 1 + (n + 1 - i) = i + 2 * (n + 1 - i) from by omega,
        pow_add, pow_mul]
      norm_num
    rw [← hsign]; ring
  rw [hconv, hS', mul_zero]

/-- **Palindromy of the explicit Eulerian sum** (the analytic, reindexing proof of oq-02).
For `k < n`, the explicit alternating sum is symmetric under `k ↦ n-1-k`:

  `eulerianExplicit n k = eulerianExplicit n (n-1-k)`. -/
theorem eulerianExplicit_palindrome (n k : ℕ) (hk : k < n) :
    eulerianExplicit n k = eulerianExplicit n (n - 1 - k) := by
  -- Abbreviate the summand.
  set T : ℕ → ℤ := fun i => (-1 : ℤ) ^ i * ((n + 1).choose i : ℤ) * ((k : ℤ) + 1 - i) ^ n with hT
  -- The full sum vanishes; split it at `k+1`.
  have hfull : (∑ i ∈ range (n + 2), T i) = 0 := full_alt_sum_zero n k
  rw [show n + 2 = (k + 1) + (n + 1 - k) from by omega, Finset.sum_range_add] at hfull
  -- Head sum is exactly `eulerianExplicit n k`.
  have hhead : (∑ i ∈ range (k + 1), T i) = eulerianExplicit n k := rfl
  -- Tail sum, after reflecting `i ↦ (n-k) - i` (i.e. the summand index `↦ n+1-i`).
  have htail : (∑ i ∈ range (n + 1 - k), T (k + 1 + i))
      = - eulerianExplicit n (n - 1 - k) := by
    rw [← Finset.sum_range_reflect (fun i => T (k + 1 + i)) (n + 1 - k)]
    -- The top reflected term (`i = n-k`) carries a factor `0ⁿ = 0`; drop it.
    rw [show n + 1 - k = (n - k) + 1 from by omega, Finset.sum_range_succ]
    have hdrop : T (k + 1 + ((n - k) + 1 - 1 - (n - k))) = 0 := by
      have : k + 1 + ((n - k) + 1 - 1 - (n - k)) = k + 1 := by omega
      rw [this, hT]
      simp only []
      have : ((k : ℤ) + 1 - (k + 1 : ℕ)) = 0 := by push_cast; ring
      rw [this, zero_pow (by omega : n ≠ 0), mul_zero]
    rw [hdrop, add_zero]
    -- Match the reflected tail with `- eulerianExplicit n (n-1-k)` termwise.
    rw [eulerianExplicit, show n - 1 - k + 1 = n - k from by omega, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl (fun i hi => ?_)
    have hin : i ≤ n - k := by simp only [mem_range] at hi; omega
    have hile : i ≤ n + 1 := by omega
    -- Reduce the reflected index `k + 1 + ((n-k)+1-1-i)` to `n + 1 - i`.
    have hidx : k + 1 + ((n - k) + 1 - 1 - i) = n + 1 - i := by omega
    rw [hT]
    simp only [hidx]
    -- Binomial reflection `C(n+1,n+1-i) = C(n+1,i)`.
    have hchoose : (n + 1).choose (n + 1 - i) = (n + 1).choose i := Nat.choose_symm hile
    -- Base reflection `(k+1) - (n+1-i) = -((n-1-k)+1-i)`.
    have hbase : ((k : ℤ) + 1 - ((n + 1 - i : ℕ) : ℤ))
        = -(((n - 1 - k : ℕ) : ℤ) + 1 - i) := by
      have h1 : ((n + 1 - i : ℕ) : ℤ) = (n : ℤ) + 1 - i := by
        push_cast [Nat.cast_sub hile]; ring
      have h2 : ((n - 1 - k : ℕ) : ℤ) = (n : ℤ) - 1 - k := by
        have e1 : (1 : ℕ) ≤ n := by omega
        have e2 : k ≤ n - 1 := by omega
        push_cast [Nat.cast_sub e2, Nat.cast_sub e1]
        ring
      rw [h1, h2]; ring
    -- Combined parity collapse `(-1)^(n+1-i) · (-1)ⁿ = -(-1)ⁱ`.
    have hsign2 : (-1 : ℤ) ^ (n + 1 - i) * (-1 : ℤ) ^ n = -((-1 : ℤ) ^ i) := by
      rw [← pow_add, show (n + 1 - i) + n = (i + 1) + 2 * (n - i) from by omega,
        pow_add, pow_mul, pow_succ]
      simp
    -- Expand the reflected base power `(-β)ⁿ = (-1)ⁿ · βⁿ` (targeting the base, not the sign).
    have hbpow : (-(((n - 1 - k : ℕ) : ℤ) + 1 - (i : ℤ))) ^ n
        = (-1 : ℤ) ^ n * (((n - 1 - k : ℕ) : ℤ) + 1 - (i : ℤ)) ^ n := neg_pow _ _
    rw [hchoose, hbase, hbpow]
    linear_combination
      (((n + 1).choose i : ℤ) * (((n - 1 - k : ℕ) : ℤ) + 1 - (i : ℤ)) ^ n) * hsign2
  rw [hhead, htail] at hfull
  linarith

/-- **Palindromy of the combinatorial Eulerian numbers.** For `k < n`,

  `⟨n,k⟩ = ⟨n, n-1-k⟩`,

obtained from the alternating-sum palindromy via the parent identity `eulerian_eq_explicit`. -/
theorem eulerian_palindrome (n k : ℕ) (hk : k < n) :
    eulerian n k = eulerian n (n - 1 - k) := by
  have h : (eulerian n k : ℤ) = (eulerian n (n - 1 - k) : ℤ) := by
    rw [eulerian_eq_explicit, eulerian_eq_explicit, eulerianExplicit_palindrome n k hk]
  exact_mod_cast h

end GeometricSeriesOQ07OQ01OQ01OQ01OQ02OQ02
