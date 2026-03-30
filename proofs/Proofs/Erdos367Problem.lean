/-
Erdős Problem #367: Products of 2-Full Parts

**Problem Statement (OPEN)**

For a positive integer n, the 2-full part B₂(n) is n/n', where n' is the
product of primes dividing n exactly once (the squarefree part).
Equivalently, B₂(n) = ∏_{p² | n} p^{v_p(n)}.

For every fixed k ≥ 1, is it true that
  ∏_{n ≤ m < n+k} B₂(m) ≪ n^{2+o(1)} ?

Or perhaps even ≪_k n²?

**Known Results:**
- For k ≤ 2, the bound ≪ n² holds trivially (since B₂(n) ≤ n)
- For k ≥ 3, the strong bound ≪ n² fails (van Doorn)
- There exist infinitely many n with ∏_{n ≤ m < n+3} B₂(m) ≫ n²·log n

**Status**: OPEN

Reference: https://erdosproblems.com/367

Adapted from formal-conjectures (Apache 2.0 License)
-/

import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Nat.Squarefree
import Mathlib.Tactic

open Nat Finset

namespace Erdos367

/-
# Part 1: The 2-Full Part

The 2-full part B₂(n) captures prime powers p² and higher in
the factorization of n. It equals n divided by its squarefree part.
-/

/--
**Squarefree Part of n**

The product of primes dividing n exactly once (with exponent 1).
-/
noncomputable def squarefreePart (n : ℕ) : ℕ :=
  ∏ p ∈ n.primeFactors.filter (fun p => n.factorization p = 1), p

/--
**The 2-Full Part B₂(n)**

B₂(n) = n / squarefreePart(n). This is the product of all prime
powers p^{v_p(n)} where v_p(n) ≥ 2.
-/
noncomputable def twoFullPart (n : ℕ) : ℕ :=
  if h : squarefreePart n ∣ n ∧ squarefreePart n ≠ 0
  then n / squarefreePart n
  else n

/--
**Alternative Definition via Prime Factorization**

B₂(n) = ∏_{v_p(n) ≥ 2} p^{v_p(n)}.
-/
noncomputable def twoFullPartAlt (n : ℕ) : ℕ :=
  ∏ p ∈ n.primeFactors.filter (fun p => n.factorization p ≥ 2),
    p ^ (n.factorization p)

/-
# Part 2: Product over Consecutive Integers

The main object of study: the product of 2-full parts over k
consecutive integers starting at n.
-/

/--
**Product of 2-Full Parts over [n, n+k)**

∏_{n ≤ m < n+k} B₂(m)
-/
noncomputable def productTwoFullParts (n k : ℕ) : ℕ :=
  ∏ m ∈ Finset.Ico n (n + k), twoFullPart m

/-
# Part 3: The Bounds

Two versions of the bound: weak (n^{2+ε}) and strong (n²).
-/

/--
**Weak Bound: n^{2+o(1)}**

For fixed k, ∏_{n ≤ m < n+k} B₂(m) ≤ C · n^{2+ε} for all ε > 0.
-/
def weakBound (k : ℕ) : Prop :=
  ∀ ε > 0, ∃ C : ℝ, C > 0 ∧
    ∀ n ≥ 1, (productTwoFullParts n k : ℝ) ≤ C * (n : ℝ) ^ (2 + ε)

/--
**Strong Bound: n²**

For fixed k, ∏_{n ≤ m < n+k} B₂(m) ≤ C_k · n².
-/
def strongBound (k : ℕ) : Prop :=
  ∃ C : ℝ, C > 0 ∧
    ∀ n ≥ 1, (productTwoFullParts n k : ℝ) ≤ C * (n : ℝ) ^ 2

/-
# Part 4: The Erdős Conjecture

The main open question: does the weak bound hold for all k?
-/

/--
**Erdős Problem #367 (OPEN)**

Does weakBound(k) hold for all k ≥ 1?

That is, for every fixed k, is ∏_{n ≤ m < n+k} B₂(m) ≪ n^{2+o(1)}?
-/
def erdos_367_conjecture : Prop :=
  ∀ k : ℕ, k ≥ 1 → weakBound k

/-
# Part 5: Known Results — Trivial Cases

For k ≤ 2, the strong bound holds because B₂(n) ≤ n.
-/

/--
**Trivial Case: k = 1**

B₂(n) ≤ n ≤ n², so strongBound(1) holds.
-/
theorem strong_bound_k1 : strongBound 1 := by
  refine ⟨1, one_pos, fun n hn => ?_⟩
  unfold productTwoFullParts
  have hIco : Finset.Ico n (n + 1) = {n} := by
    ext m; simp only [Finset.mem_Ico, Finset.mem_singleton]; omega
  rw [hIco, Finset.prod_singleton]
  have h1 : (twoFullPart n : ℝ) ≤ (n : ℝ) := by exact_mod_cast twoFullPart_le n
  have hn' : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  nlinarith [sq_nonneg ((n : ℝ) - 1)]

/--
**Trivial Case: k = 2**

B₂(n) · B₂(n+1) ≤ n · (n+1) < 2n², so strongBound(2) holds.
-/
theorem strong_bound_k2 : strongBound 2 := by
  refine ⟨2, by norm_num, fun n hn => ?_⟩
  unfold productTwoFullParts
  have hIco : Finset.Ico n (n + 2) = {n, n + 1} := by
    ext m; simp only [Finset.mem_Ico, Finset.mem_insert, Finset.mem_singleton]; omega
  rw [hIco, Finset.prod_insert (show n ∉ ({n + 1} : Finset ℕ) by simp; omega),
      Finset.prod_singleton]
  simp only [Nat.cast_mul]
  have h1 : (twoFullPart n : ℝ) ≤ (n : ℝ) := by exact_mod_cast twoFullPart_le n
  have h2 : (twoFullPart (n + 1) : ℝ) ≤ (n : ℝ) + 1 := by exact_mod_cast twoFullPart_le (n + 1)
  have hn' : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  nlinarith [mul_le_mul h1 h2 (Nat.cast_nonneg (twoFullPart (n + 1)))
               (by linarith : (0 : ℝ) ≤ (n : ℝ)),
             sq_nonneg ((n : ℝ) - 1)]

/-
# Part 6: Known Results — Failure of Strong Bound

van Doorn showed the strong bound fails for k ≥ 3.
-/

/--
**Strong Bound Fails for k = 3**

There exist infinitely many n with ∏_{n ≤ m < n+3} B₂(m) ≫ n² · log n,
so no constant C can satisfy ∏B₂(m) ≤ C · n² for all n.

Proof: van Doorn's lower bound gives product ≥ c·n²·log(n) for infinitely
many n. If strongBound 3 held (product ≤ C·n² for all n ≥ 1), then
C ≥ c·log(n) for arbitrarily large n, contradicting C being fixed. -/
theorem strong_bound_fails_k3 : ¬ strongBound 3 := by
  intro ⟨C, hC, hbound⟩
  obtain ⟨c, hc, hvan⟩ := van_doorn_lower_bound
  -- Choose M large enough that log(n) > C/c for n ≥ M
  set M := Nat.ceil (Real.exp (C / c + 1)) + 1 with hM_def
  obtain ⟨n, hn_ge, hprod⟩ := hvan M
  have hn1 : (1 : ℕ) ≤ n := by omega
  have hstrong := hbound n hn1
  -- Key: c·n²·log(n) ≤ product ≤ C·n²
  have h_ineq : c * (n : ℝ) ^ 2 * Real.log n ≤ C * (n : ℝ) ^ 2 := by linarith
  have hnsq_pos : (0 : ℝ) < (n : ℝ) ^ 2 := by positivity
  -- Dividing by n² > 0: c·log(n) ≤ C
  have h_clog : c * Real.log n ≤ C := by
    by_contra h; push_neg at h
    linarith [mul_lt_mul_of_pos_right h hnsq_pos]
  -- But n ≥ M ≥ exp(C/c + 1), so log(n) ≥ C/c + 1 > C/c
  have h_exp_le : Real.exp (C / c + 1) ≤ (n : ℝ) := by
    calc Real.exp (C / c + 1)
        ≤ ↑(Nat.ceil (Real.exp (C / c + 1))) :=
          Nat.le_ceil (Real.exp (C / c + 1))
      _ ≤ ↑(Nat.ceil (Real.exp (C / c + 1)) + 1) := by
          exact_mod_cast Nat.le_succ _
      _ = (M : ℝ) := by rfl
      _ ≤ (n : ℝ) := by exact_mod_cast hn_ge
  have h_log_large : C / c + 1 ≤ Real.log n := by
    calc C / c + 1
        = Real.log (Real.exp (C / c + 1)) := (Real.log_exp _).symm
      _ ≤ Real.log ↑n :=
          Real.log_le_log (Real.exp_pos _) h_exp_le
  -- So c·log(n) ≥ c·(C/c + 1) = C + c > C
  have h_clog_large : C < c * Real.log n := by
    have : c * (C / c + 1) ≤ c * Real.log n :=
      mul_le_mul_of_nonneg_left h_log_large hc.le
    linarith [mul_div_cancel₀ C (ne_of_gt hc)]
  linarith

/--
**van Doorn's Lower Bound**

For k = 3, there exist infinitely many n where the product
of 2-full parts exceeds n² by a logarithmic factor.
-/
axiom van_doorn_lower_bound :
    ∃ c : ℝ, c > 0 ∧ ∀ N : ℕ, ∃ n ≥ N,
      (productTwoFullParts n 3 : ℝ) ≥ c * (n : ℝ) ^ 2 * Real.log n

/-
# Part 7: Properties of the 2-Full Part

Basic properties of B₂(n) needed for the analysis.
-/

/- Note: twoFullPart_eq_one_iff (B₂(n) = 1 ↔ Squarefree n) was removed
   as it was unused in any proof. The fact is true but not needed. -/

/- Helper: For a prime p, p.primeFactors = {p} -/
private lemma primeFactors_prime_eq (p : ℕ) (hp : p.Prime) :
    p.primeFactors = {p} := by
  ext q
  simp only [Nat.mem_primeFactors, Finset.mem_singleton]
  constructor
  · rintro ⟨hq, hqp, -⟩
    exact (hp.eq_one_or_self_of_dvd q hqp).resolve_left hq.one_lt.ne'
  · rintro rfl
    exact ⟨hp, dvd_refl p, hp.ne_zero⟩

/- Helper: For a prime p, (p^2).primeFactors = {p} -/
private lemma primeFactors_prime_sq_eq (p : ℕ) (hp : p.Prime) :
    (p ^ 2).primeFactors = {p} := by
  ext q
  simp only [Nat.mem_primeFactors, Finset.mem_singleton]
  constructor
  · rintro ⟨hq, hqp2, -⟩
    exact (hp.eq_one_or_self_of_dvd q (hq.dvd_of_dvd_pow hqp2)).resolve_left hq.one_lt.ne'
  · rintro rfl
    exact ⟨hp, dvd_pow_self p (by omega), pow_ne_zero 2 hp.ne_zero⟩

/- Helper: squarefreePart of a prime equals the prime itself -/
private lemma squarefreePart_prime_eq (p : ℕ) (hp : p.Prime) :
    squarefreePart p = p := by
  unfold squarefreePart
  rw [primeFactors_prime_eq p hp]
  have hfilt : ({p} : Finset ℕ).filter (fun q => p.factorization q = 1) = {p} := by
    apply Finset.filter_true_of_mem
    intro q hq
    rw [Finset.mem_singleton.mp hq]
    simp [Nat.factorization_prime hp, Finsupp.single_eq_same]
  rw [hfilt]
  exact Finset.prod_singleton

/- Helper: squarefreePart of p² is 1 (no primes with exponent exactly 1) -/
private lemma squarefreePart_prime_sq_eq (p : ℕ) (hp : p.Prime) :
    squarefreePart (p ^ 2) = 1 := by
  unfold squarefreePart
  rw [primeFactors_prime_sq_eq p hp]
  have hfilt : ({p} : Finset ℕ).filter
      (fun q => (p ^ 2).factorization q = 1) = ∅ := by
    rw [Finset.filter_eq_empty]
    intro q hq
    rw [Finset.mem_singleton.mp hq]
    simp [Nat.factorization_prime_pow hp, Finsupp.single_eq_same]
  rw [hfilt]
  exact Finset.prod_empty

/--
**B₂(p) = 1 for Primes**

Primes are squarefree, so their 2-full part is 1.
-/
theorem twoFullPart_prime (p : ℕ) (hp : p.Prime) : twoFullPart p = 1 := by
  have hsf := squarefreePart_prime_eq p hp
  unfold twoFullPart
  have h : squarefreePart p ∣ p ∧ squarefreePart p ≠ 0 := by
    constructor
    · rw [hsf]
    · rw [hsf]; exact hp.ne_zero
  rw [dif_pos h, hsf, Nat.div_self hp.pos]

/--
**B₂(p²) = p² for Primes**

Perfect squares of primes are entirely 2-full.
-/
theorem twoFullPart_prime_sq (p : ℕ) (hp : p.Prime) :
    twoFullPart (p ^ 2) = p ^ 2 := by
  have hsf := squarefreePart_prime_sq_eq p hp
  unfold twoFullPart
  have h : squarefreePart (p ^ 2) ∣ p ^ 2 ∧ squarefreePart (p ^ 2) ≠ 0 := by
    constructor
    · rw [hsf]; exact one_dvd _
    · rw [hsf]; exact one_ne_zero
  rw [dif_pos h, hsf, Nat.div_one]

/- Note: twoFullPart_mul_coprime (B₂(mn) = B₂(m)·B₂(n) for coprime m,n)
   was removed as it was unused in any proof. The fact is true but not needed. -/

/--
**Upper Bound: B₂(n) ≤ n**

The 2-full part never exceeds n itself.
-/
theorem twoFullPart_le (n : ℕ) : twoFullPart n ≤ n := by
  unfold twoFullPart
  split
  next _ => exact Nat.div_le_self n _
  next _ => exact le_refl n

/--
**Divisibility: B₂(n) | n**

The 2-full part always divides n.
-/
theorem twoFullPart_dvd (n : ℕ) : twoFullPart n ∣ n := by
  unfold twoFullPart
  split
  next h => exact Nat.div_dvd_of_dvd h.1
  next _ => exact dvd_refl n

/-
# Part 8: Generalization to r-Full Parts

The problem generalizes to r-full parts for r ≥ 3.
-/

/--
**r-Full Part of n**

B_r(n) = ∏_{v_p(n) ≥ r} p^{v_p(n)}: the product of prime powers
where the exponent is at least r.
-/
noncomputable def rFullPart (r n : ℕ) : ℕ :=
  ∏ p ∈ n.primeFactors.filter (fun p => n.factorization p ≥ r),
    p ^ (n.factorization p)

/--
**Consistency: twoFullPartAlt = rFullPart 2**

The alternative 2-full definition is the r-full part with r = 2.
-/
theorem twoFullPart_eq_rFullPart (n : ℕ) : twoFullPartAlt n = rFullPart 2 n := rfl

/--
**Generalized Conjecture for r-Full Parts**

For r ≥ 3 and fixed k, does ∏_{n ≤ m < n+k} B_r(m) ≪ n^{r+o(1)}?
-/
def generalizedConjecture (r k : ℕ) : Prop :=
  ∀ ε > 0, ∃ C : ℝ, C > 0 ∧
    ∀ n ≥ 1, (∏ m ∈ Finset.Ico n (n + k), rFullPart r m : ℝ) ≤
      C * (n : ℝ) ^ (r + ε)

/-
# Part 9: Heuristic Analysis

The average behavior of B₂(n) and why the problem is subtle.
-/

/--
**Average Behavior**

On average, B₂(n) is bounded (most numbers are nearly squarefree).
But the product over consecutive integers can be large because
nearby integers can share high prime powers.
-/
axiom average_twoFullPart_bounded :
    ∃ C : ℝ, C > 0 ∧ ∀ N ≥ 1,
      (∑ n ∈ Finset.Icc 1 N, (twoFullPart n : ℝ)) / N ≤ C

/-
# Part 10: Summary
-/

/--
**Erdős Problem #367: Summary of Known Results**

Combines: strongBound holds for k ≤ 2, fails for k ≥ 3,
and the weak bound conjecture remains open.
-/
theorem erdos_367_summary :
    -- Strong bound holds for k = 1 and k = 2
    (strongBound 1 ∧ strongBound 2) ∧
    -- Strong bound fails for k = 3
    ¬ strongBound 3 ∧
    -- The weak bound conjecture is stated
    True :=
  ⟨⟨strong_bound_k1, strong_bound_k2⟩, strong_bound_fails_k3, trivial⟩

/-- The problem remains OPEN. -/
def erdos_367_status : String := "OPEN"

end Erdos367
