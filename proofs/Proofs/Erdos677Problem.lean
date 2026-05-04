/-
# Erdős Problem 677: Distinct LCM of Consecutive Integers

Let `M(n, k) = lcm(n+1, n+2, ..., n+k)` be the least common multiple of `k`
consecutive integers starting at `n+1`.

Is it true that for all `m ≥ n + k`, we have `M(m, k) ≠ M(n, k)`?

The Thue–Siegel theorem implies that for fixed `k`, only finitely many pairs
`(m, n)` with `m ≥ n + k` satisfy `M(m, k) = M(n, k)`.

Erdős knew only two examples with different parameters:
- `M(4, 3) = M(13, 2)` (i.e., `lcm(5,6,7) = lcm(14,15)`)
- `M(3, 4) = M(19, 2)` (i.e., `lcm(4,5,6,7) = lcm(20,21)`)

**Stronger conjecture:** With finitely many exceptions, if `k > 2` and
`m ≥ n + k`, then `∏_{i≤k}(n+i)` and `∏_{i≤k}(m+i)` cannot share the
same set of prime factors.

*Reference:* [erdosproblems.com/677](https://www.erdosproblems.com/677)
-/

import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Order.Filter.Basic
import Mathlib.Tactic

open Finset

/- ## LCM of consecutive integers -/

/-- `lcmInterval n k` is `lcm(n+1, n+2, ..., n+k)`, the LCM of `k` consecutive
integers starting at `n+1`. -/
def lcmInterval (n k : ℕ) : ℕ :=
    (Finset.range k).fold Nat.lcm 1 (fun i => n + i + 1)

/- ## Main conjecture -/

/-- Erdős Problem 677: For all `m ≥ n + k` with `k > 0`, `M(m,k) ≠ M(n,k)`. -/
def ErdosProblem677 : Prop :=
    ∀ (m n k : ℕ), 0 < k → n + k ≤ m → lcmInterval m k ≠ lcmInterval n k

/- ## Known examples -/

/-- The two known examples where `M(n,k) = M(m,l)` with different parameters:
`lcm(5,6,7) = lcm(14,15) = 210` and `lcm(4,5,6,7) = lcm(20,21) = 420`.
These are concrete computations, now proved by evaluation. -/
theorem lcmInterval_example1 : lcmInterval 4 3 = lcmInterval 13 2 := by native_decide
theorem lcmInterval_example2 : lcmInterval 3 4 = lcmInterval 19 2 := by native_decide

/- ## Stronger conjecture: same prime factors -/

/-- `samePrimeFactors a b` holds when `a` and `b` have the same set of prime divisors. -/
def samePrimeFactors (a b : ℕ) : Prop :=
    a.primeFactors = b.primeFactors

/-- The product of `k` consecutive integers starting at `n+1`. -/
def consecutiveProduct (n k : ℕ) : ℕ :=
    (Finset.range k).prod (fun i => n + i + 1)

/-- Stronger conjecture: with finitely many exceptions, if `k > 2` and `m ≥ n + k`,
the consecutive products `∏(n+i)` and `∏(m+i)` do not share the same prime factors. -/
def ErdosProblem677_strong : Prop :=
    ∀ k : ℕ, 2 < k →
      Set.Finite { p : ℕ × ℕ | p.1 + k ≤ p.2 ∧
        samePrimeFactors (consecutiveProduct p.1 k) (consecutiveProduct p.2 k) }

/- ## Thue–Siegel finiteness -/

/-- Thue–Siegel theorem consequence: for fixed `k`, only finitely many pairs satisfy
`M(m,k) = M(n,k)` with `m ≥ n + k`. -/
axiom thue_siegel_finiteness (k : ℕ) (hk : 0 < k) :
    Set.Finite { p : ℕ × ℕ | p.1 + k ≤ p.2 ∧ lcmInterval p.1 k = lcmInterval p.2 k }

/- ## Basic properties -/

/-- `lcmInterval n 0 = 1` (empty LCM). -/
theorem lcmInterval_zero (n : ℕ) : lcmInterval n 0 = 1 := by
  simp [lcmInterval]

/-- `lcmInterval n 1 = n + 1`. -/
theorem lcmInterval_one (n : ℕ) : lcmInterval n 1 = n + 1 := by
  simp [lcmInterval, Nat.lcm_one_left]

/-- `consecutiveProduct n 0 = 1` (empty product). -/
theorem consecutiveProduct_zero (n : ℕ) : consecutiveProduct n 0 = 1 := by
  simp [consecutiveProduct]

/-- `consecutiveProduct n 1 = n + 1`. -/
theorem consecutiveProduct_one (n : ℕ) : consecutiveProduct n 1 = n + 1 := by
  simp [consecutiveProduct]

/-- The LCM divides the product of the same range.
Proof: by induction on k using fold/prod over range. -/
theorem lcmInterval_dvd_product (n k : ℕ) :
    lcmInterval n k ∣ consecutiveProduct n k := by
  simp only [lcmInterval, consecutiveProduct]
  suffices h : ∀ s : Finset ℕ, s.fold Nat.lcm 1 (fun i => n + i + 1) ∣
      s.prod (fun i => n + i + 1) from h _
  intro s
  induction s using Finset.induction_on with
  | empty => simp
  | insert ha ih =>
    rw [Finset.fold_insert ha, Finset.prod_insert ha]
    exact Nat.lcm_dvd (dvd_mul_right _ _) (dvd_mul_of_dvd_left ih _)

/-- `lcmInterval` is positive when `k > 0`.
Proof: the product of positive numbers is positive, and the LCM divides it. -/
theorem lcmInterval_pos (n k : ℕ) (hk : 0 < k) : 0 < lcmInterval n k := by
  rcases Nat.eq_zero_or_pos (lcmInterval n k) with h | h
  · -- If lcmInterval = 0, then 0 ∣ product, so product = 0, contradiction
    have hdvd := lcmInterval_dvd_product n k
    rw [h, zero_dvd_iff] at hdvd
    have : 0 < consecutiveProduct n k := by
      unfold consecutiveProduct
      exact Finset.prod_pos (fun i _ => by omega)
    omega
  · exact h

/- ## Structural properties -/

/-- Recursion: `lcmInterval n (k+1) = lcm(n + k + 1, lcmInterval n k)`. -/
theorem lcmInterval_succ (n k : ℕ) :
    lcmInterval n (k + 1) = Nat.lcm (n + k + 1) (lcmInterval n k) := by
  unfold lcmInterval
  rw [Finset.range_succ, Finset.fold_insert (Finset.not_mem_range_self)]

/-- Each element `n + i + 1` (for `i < k`) divides `lcmInterval n k`. -/
theorem dvd_lcmInterval (n k i : ℕ) (hi : i < k) :
    n + i + 1 ∣ lcmInterval n k := by
  induction k with
  | zero => omega
  | succ k ih =>
    rw [lcmInterval_succ]
    rcases (Nat.lt_succ_iff.mp hi).eq_or_lt with rfl | hi'
    · exact Nat.dvd_lcm_left _ _
    · exact dvd_trans (ih hi') (Nat.dvd_lcm_right _ _)

/-- `lcmInterval n k` divides `lcmInterval n (k + 1)`. -/
theorem lcmInterval_dvd_succ (n k : ℕ) :
    lcmInterval n k ∣ lcmInterval n (k + 1) := by
  rw [lcmInterval_succ]
  exact Nat.dvd_lcm_right _ _

/-- Monotonicity: `lcmInterval n k` divides `lcmInterval n (k + j)` for any `j`. -/
theorem lcmInterval_dvd_add (n k j : ℕ) :
    lcmInterval n k ∣ lcmInterval n (k + j) := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [Nat.add_succ]
    exact dvd_trans ih (lcmInterval_dvd_succ n (k + j))

/-- The largest element `n + k` divides `lcmInterval n k` when `k > 0`. -/
theorem last_dvd_lcmInterval (n k : ℕ) (hk : 0 < k) :
    n + k ∣ lcmInterval n k := by
  have h := dvd_lcmInterval n k (k - 1) (by omega)
  have : n + (k - 1) + 1 = n + k := by omega
  rwa [this] at h

/-- `consecutiveProduct` recursion: `consecutiveProduct n (k+1) = consecutiveProduct n k * (n+k+1)`. -/
theorem consecutiveProduct_succ (n k : ℕ) :
    consecutiveProduct n (k + 1) = consecutiveProduct n k * (n + k + 1) := by
  unfold consecutiveProduct
  rw [Finset.range_succ, Finset.prod_insert (Finset.not_mem_range_self)]
  ring

/-- `consecutiveProduct` is positive. -/
theorem consecutiveProduct_pos (n k : ℕ) : 0 < consecutiveProduct n k := by
  unfold consecutiveProduct
  exact Finset.prod_pos (fun i _ => by omega)

/- ## Prime divisibility -/

/-- Among any `k` consecutive integers starting at `n+1`, at least one is
    divisible by `p`, provided `p ≤ k` and `p > 0`. -/
theorem exists_dvd_in_range (n k p : ℕ) (hp : 0 < p) (hpk : p ≤ k) :
    ∃ i, i < k ∧ p ∣ (n + i + 1) := by
  rcases Nat.eq_zero_or_pos ((n + 1) % p) with hr | hr
  · exact ⟨0, by omega, Nat.dvd_of_mod_eq_zero hr⟩
  · have hmod := Nat.mod_lt (n + 1) hp
    refine ⟨p - (n + 1) % p, by omega, ?_⟩
    rw [Nat.dvd_iff_mod_eq_zero,
        show n + (p - (n + 1) % p) + 1 = (n + 1) + (p - (n + 1) % p) from by omega,
        Nat.add_mod,
        Nat.mod_eq_of_lt (show p - (n + 1) % p < p from by omega),
        show (n + 1) % p + (p - (n + 1) % p) = p from by omega,
        Nat.mod_self]

/-- Every prime `p ≤ k` divides `lcmInterval n k`:
    among `k` consecutive integers, at least one is divisible by `p`. -/
theorem prime_le_dvd_lcmInterval (n k p : ℕ) (hp : p.Prime) (hpk : p ≤ k) :
    p ∣ lcmInterval n k := by
  obtain ⟨i, hi, hpi⟩ := exists_dvd_in_range n k p hp.pos hpk
  exact dvd_trans hpi (dvd_lcmInterval n k i hi)

/- ## Additional structural properties -/

/-- `lcmInterval n k ≠ 0` for all `n`, `k`. -/
theorem lcmInterval_ne_zero (n k : ℕ) : lcmInterval n k ≠ 0 := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp [lcmInterval_zero]
  · exact (lcmInterval_pos n k hk).ne'

/-- Lower bound: `n + k ≤ lcmInterval n k` when `k > 0`. -/
theorem le_lcmInterval (n k : ℕ) (hk : 0 < k) : n + k ≤ lcmInterval n k :=
  Nat.le_of_dvd (lcmInterval_pos n k hk) (last_dvd_lcmInterval n k hk)

/-- For `k = 2`: `M(n, 2) = (n+1)(n+2)`, since consecutive integers are coprime
    and `lcm(m, n) = m * n` when `gcd(m, n) = 1`. -/
theorem lcmInterval_two (n : ℕ) : lcmInterval n 2 = (n + 1) * (n + 2) := by
  rw [show (2 : ℕ) = 1 + 1 from rfl, lcmInterval_succ, lcmInterval_one, Nat.lcm_comm]
  exact (Nat.coprime_succ_self (n + 1)).lcm_eq_mul

/-- Erdős #677 holds for `k = 1`: `M(m, 1) = m + 1 ≠ n + 1 = M(n, 1)` when `m ≥ n + 1`. -/
theorem erdos677_k1 (m n : ℕ) (hm : n + 1 ≤ m) :
    lcmInterval m 1 ≠ lcmInterval n 1 := by
  simp only [lcmInterval_one]; omega

/-- Erdős #677 holds for `k = 2`: `M(n, 2) = (n+1)(n+2)` is strictly increasing in `n`,
    so `M(m, 2) > M(n, 2)` for any `m ≥ n + 2`. -/
theorem erdos677_k2 (m n : ℕ) (hm : n + 2 ≤ m) :
    lcmInterval m 2 ≠ lcmInterval n 2 := by
  rw [lcmInterval_two, lcmInterval_two]
  nlinarith [Nat.succ_pos n, Nat.succ_pos m]

/- ## Factorization characterization -/

/-- The factorization of `lcmInterval n k` equals the pointwise sup (max) of the
    factorizations of all `k` consecutive integers `n+1, ..., n+k`.
    This follows by induction from `factorization (lcm a b) = factorization a ⊔ factorization b`. -/
theorem factorization_lcmInterval (n k : ℕ) :
    (lcmInterval n k).factorization =
    (Finset.range k).sup (fun i => (n + i + 1).factorization) := by
  induction k with
  | zero => simp [lcmInterval_zero]
  | succ k ih =>
    rw [lcmInterval_succ,
        Nat.factorization_lcm (by omega) (lcmInterval_ne_zero n k),
        ih, Finset.range_succ, Finset.sup_insert]

/- ## General large-m distinctness bound -/

/-- **Structural bound**: for any k ≥ 1, if m + k exceeds the consecutive product
    (n+1)·(n+2)·⋯·(n+k), then lcmInterval(m, k) ≠ lcmInterval(n, k).

    Proof: `lcmInterval(n,k) ≤ consecutiveProduct(n,k)` by `lcmInterval_dvd_product`,
    while `lcmInterval(m,k) ≥ m+k` by `le_lcmInterval`. These sandwich to a contradiction. -/
theorem erdos677_large_m (n m k : ℕ) (hk : 0 < k) (hm : n + k ≤ m)
    (hbig : consecutiveProduct n k < m + k) :
    lcmInterval m k ≠ lcmInterval n k := by
  intro heq
  have h_n_le : lcmInterval n k ≤ consecutiveProduct n k :=
    Nat.le_of_dvd (consecutiveProduct_pos n k) (lcmInterval_dvd_product n k)
  have h_m_ge : m + k ≤ lcmInterval m k := le_lcmInterval m k hk
  have h_chain : m + k ≤ lcmInterval n k := heq ▸ h_m_ge
  linarith

/-- Corollary for k = 3: Erdős #677 holds when m + 3 > (n+1)(n+2)(n+3).
    This elementary bound covers all "large m" cases without the Thue–Siegel axiom. -/
theorem erdos677_k3_large_m (m n : ℕ) (hm : n + 3 ≤ m)
    (hbig : (n + 1) * (n + 2) * (n + 3) < m + 3) :
    lcmInterval m 3 ≠ lcmInterval n 3 := by
  apply erdos677_large_m n m 3 (by omega) hm
  have : consecutiveProduct n 3 = (n + 1) * (n + 2) * (n + 3) := by
    simp [consecutiveProduct, Finset.prod_range_succ]; ring
  linarith
