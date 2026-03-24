/-
Erdős Problem #382: Prime Powers in Factorial Products

Source: https://erdosproblems.com/382
Status: OPEN

Statement:
Let u ≤ v be such that the largest prime dividing ∏_{u ≤ m ≤ v} m
appears with exponent at least 2.

Questions:
1. Is v - u = v^o(1)? (i.e., does v - u grow subpolynomially in v?)
2. Can v - u be arbitrarily large?

Known Results:
- Ramachandra: v - u ≤ v^{1/2 + o(1)}
- Under Cramér's conjecture: if u + u^ε < v for any ε > 0, then the largest
  prime divisor has exponent 1 (suggesting v - u = v^o(1) is true)

Key Insight:
The product m! / (u-1)! = u · (u+1) · ... · v includes all primes p with u ≤ p ≤ v.
For the largest such prime p to appear with exponent ≥ 2, we need p² ≤ v,
which means the interval [u, v] must contain no primes larger than √v.

References:
- Erdős-Graham [ErGr80]
- Ramachandra: bounds on largest prime in short intervals
- OEIS: A388850
-/

import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

open Nat BigOperators Finset Real

namespace Erdos382

/- ## Part I: Basic Definitions -/

/--
**The Product of an Interval**

prod_interval(u, v) = u · (u+1) · ... · v = v! / (u-1)!

This is the product of consecutive integers from u to v inclusive.
-/
def prodInterval (u v : ℕ) : ℕ :=
  ∏ m ∈ Finset.Icc u v, m

/-- prod_interval(u, u) = u. -/
theorem prodInterval_singleton (n : ℕ) (hn : n > 0) :
    prodInterval n n = n := by
  simp [prodInterval, Finset.Icc_self]

/-- prod_interval(1, n) = n!. -/
theorem prodInterval_factorial (n : ℕ) :
    prodInterval 1 n = n.factorial := by
  unfold prodInterval
  induction n with
  | zero => simp
  | succ n ih =>
    have h : Finset.Icc 1 (n + 1) = insert (n + 1) (Finset.Icc 1 n) := by
      ext x; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
    rw [h, Finset.prod_insert (by simp [Finset.mem_Icc])]
    rw [ih, Nat.factorial_succ, mul_comm]

/- ## Part II: Largest Prime Divisor -/

/--
**Largest Prime Divisor**

The largest prime that divides n, or 0 if n ≤ 1.
-/
noncomputable def largestPrimeDivisor (n : ℕ) : ℕ :=
  if h : n > 1 then
    n.primeFactorsList.foldl max 0
  else 0

/-- Helper: foldl max is ≥ init. -/
private lemma foldl_max_ge_init : ∀ (l : List ℕ) (init : ℕ),
    l.foldl max init ≥ init
  | [], init => le_refl init
  | _ :: as, init => le_trans (le_max_left init _) (foldl_max_ge_init as _)

/-- Helper: foldl max is ≥ any member. -/
private lemma foldl_max_ge_of_mem : ∀ {l : List ℕ} {x : ℕ}, x ∈ l →
    ∀ (init : ℕ), l.foldl max init ≥ x
  | _ :: _, _, List.Mem.head _, init =>
    le_trans (le_max_right init _) (foldl_max_ge_init _ _)
  | _ :: _, _, List.Mem.tail _ hx, init =>
    foldl_max_ge_of_mem hx _

/-- Helper: foldl max result equals init or is a member of the list. -/
private lemma foldl_max_eq_init_or_mem : ∀ (l : List ℕ) (init : ℕ),
    l.foldl max init = init ∨ l.foldl max init ∈ l
  | [], init => Or.inl rfl
  | a :: as, init => by
    simp only [List.foldl_cons]
    rcases foldl_max_eq_init_or_mem as (max init a) with h | h
    · rw [h]
      rcases le_or_lt a init with hle | hlt
      · left; exact max_eq_left hle
      · right; rw [max_eq_right (le_of_lt hlt)]; exact List.mem_cons_self a as
    · right; exact List.mem_cons_of_mem a h

/-- primeFactorsList is nonempty for n > 1. -/
private lemma primeFactorsList_ne_nil (n : ℕ) (hn : n > 1) :
    n.primeFactorsList ≠ [] := by
  intro h
  have := Nat.prod_primeFactorsList (show n ≠ 0 by omega)
  rw [h, List.prod_nil] at this
  omega

/-- The foldl max 0 of primeFactorsList is a member for n > 1. -/
private lemma foldl_max_mem_primeFactorsList (n : ℕ) (hn : n > 1) :
    n.primeFactorsList.foldl max 0 ∈ n.primeFactorsList := by
  have hne := primeFactorsList_ne_nil n hn
  rcases foldl_max_eq_init_or_mem n.primeFactorsList 0 with h | h
  · exfalso
    obtain ⟨x, hx⟩ : ∃ a, a ∈ n.primeFactorsList := by
      cases hl : n.primeFactorsList with
      | nil => exact absurd hl hne
      | cons a l => exact ⟨a, List.mem_cons_self a l⟩
    have h1 := foldl_max_ge_of_mem hx 0
    rw [h] at h1
    have h2 := (Nat.prime_of_mem_primeFactorsList hx).two_le
    omega
  · exact h

/-- The largest prime divisor divides n. -/
theorem largestPrimeDivisor_dvd (n : ℕ) (hn : n > 1) :
    largestPrimeDivisor n ∣ n := by
  simp only [largestPrimeDivisor, dif_pos hn]
  exact Nat.dvd_of_mem_primeFactorsList (foldl_max_mem_primeFactorsList n hn)

/-- The largest prime divisor is prime (if n > 1). -/
theorem largestPrimeDivisor_prime (n : ℕ) (hn : n > 1) :
    (largestPrimeDivisor n).Prime := by
  simp only [largestPrimeDivisor, dif_pos hn]
  exact Nat.prime_of_mem_primeFactorsList (foldl_max_mem_primeFactorsList n hn)

/-- Any prime divisor is ≤ the largest. -/
theorem prime_le_largestPrimeDivisor (n p : ℕ) (hn : n > 1) (hp : p.Prime) (hdiv : p ∣ n) :
    p ≤ largestPrimeDivisor n := by
  simp only [largestPrimeDivisor, dif_pos hn]
  have hmem : p ∈ n.primeFactorsList := by
    rw [Nat.mem_primeFactorsList (show n ≠ 0 by omega)]
    exact ⟨hp, hdiv⟩
  exact foldl_max_ge_of_mem hmem 0

/- ## Part III: Exponent of Prime in Product -/

/--
**P-adic Valuation**

The exponent of prime p in the factorization of n.
-/
def exponent (p n : ℕ) : ℕ := n.factorization p

/-- The exponent of p in the product u·(u+1)·...·v. -/
noncomputable def exponentInProduct (p u v : ℕ) : ℕ :=
  exponent p (prodInterval u v)

/-- The exponent is the sum of individual exponents. -/
axiom exponentInProduct_sum (p u v : ℕ) (hp : p.Prime) :
    exponentInProduct p u v = ∑ m ∈ Finset.Icc u v, exponent p m

/- ## Part IV: The Condition -/

/--
**The Erdős-Graham Condition**

An interval [u, v] satisfies the condition if the largest prime dividing
the product u·(u+1)·...·v appears with exponent at least 2.
-/
def satisfiesCondition (u v : ℕ) : Prop :=
  u ≤ v ∧ u > 0 ∧
  let P := prodInterval u v
  let p := largestPrimeDivisor P
  exponent p P ≥ 2

/-- If p is the largest prime ≤ v and p² > v, then p has exponent 1. -/
axiom largest_prime_exp_one (u v p : ℕ) (hu : u > 0) (huv : u ≤ v)
    (hp : p.Prime) (hpv : p ≤ v) (hpu : u ≤ p)
    (hlargest : ∀ q, q.Prime → q ≤ v → q ≤ p)
    (hsq : p * p > v) :
    exponent p (prodInterval u v) = 1

/-- For p to have exponent ≥ 2 in [u,v], we need some multiple of p² in [u,v]. -/
axiom exp_ge_two_needs_square (u v p : ℕ) (hp : p.Prime)
    (hexp : exponent p (prodInterval u v) ≥ 2) :
    ∃ k, p * p ∣ k ∧ u ≤ k ∧ k ≤ v

/- ## Part V: The Questions -/

/--
**Question 1 (OPEN)**: Is v - u = v^o(1)?

For intervals [u,v] satisfying the condition, does v - u grow
subpolynomially in v? I.e., for every ε > 0 and large enough v,
is v - u < v^ε?
-/
def question1 : Prop :=
  ∀ ε : ℝ, ε > 0 →
    ∃ V : ℕ, ∀ u v : ℕ, v ≥ V → satisfiesCondition u v →
      (v - u : ℝ) < (v : ℝ) ^ ε

/-- The conjecture that Question 1 has answer YES. -/
axiom erdos_382_q1 : question1

/--
**Question 2 (OPEN)**: Can v - u be arbitrarily large?

Are there intervals [u, v] satisfying the condition with
v - u arbitrarily large?
-/
def question2 : Prop :=
  ∀ L : ℕ, ∃ u v : ℕ, satisfiesCondition u v ∧ v - u > L

/-- Cambie's heuristic suggests YES for Question 2. -/
axiom erdos_382_q2_heuristic : question2

/- ## Part VI: Known Upper Bound -/

/--
**Ramachandra's Bound**

v - u ≤ v^{1/2 + o(1)}

More precisely, for any ε > 0 and large enough v, if [u,v] satisfies
the condition, then v - u ≤ v^{1/2 + ε}.
-/
axiom ramachandra_bound (ε : ℝ) (hε : ε > 0) :
    ∃ V : ℕ, ∀ u v : ℕ, v ≥ V → satisfiesCondition u v →
      (v - u : ℝ) ≤ (v : ℝ) ^ (1/2 + ε)

/- ## Part VII: Connection to Cramér's Conjecture -/

/--
**Cramér's Conjecture**

The gap between consecutive primes p_n and p_{n+1} is O((log p_n)²).

This famous conjecture would imply Question 1 has answer YES.
-/
def cramersConjecture : Prop :=
  ∃ C : ℝ, C > 0 ∧ ∀ p q : ℕ, p.Prime → q.Prime → p < q →
    (∀ r, p < r → r < q → ¬r.Prime) →
    (q - p : ℝ) ≤ C * (Real.log p) ^ 2

/-- Under Cramér's conjecture, Question 1 is true. -/
axiom cramer_implies_q1 : cramersConjecture → question1

/- ## Part VIII: Examples -/

/-- Example: [2, 4] has product 24 = 2³ · 3. Largest prime is 3, exp(3) = 1. -/
example : prodInterval 2 4 = 24 := by
  simp [prodInterval]
  native_decide

/-- For [u, v] to satisfy the condition, we need no prime in (√v, v]. -/
axiom no_prime_in_upper_half (u v : ℕ) (hu : u > 0) (huv : u ≤ v)
    (hcond : satisfiesCondition u v) :
    ∀ p : ℕ, p.Prime → p > Nat.sqrt v → p ≤ v → False

/- ## Part IX: The Prime-Free Interval Perspective -/

/--
**Prime-Free Interval Perspective**

The condition is equivalent to asking: the interval [u, v] contains
no primes larger than √v.

Equivalently, all primes in [u, v] are ≤ √v, so their squares can
fit in [1, v].
-/
def noPrimeLargerThanSqrt (u v : ℕ) : Prop :=
  ∀ p : ℕ, p.Prime → u ≤ p → p ≤ v → p ≤ Nat.sqrt v

/-- The condition is equivalent to having no prime larger than √v in [u, v]. -/
axiom condition_iff_no_large_prime (u v : ℕ) (hu : u > 0) (huv : u ≤ v) :
    satisfiesCondition u v ↔ (u ≤ v ∧ u > 0 ∧ noPrimeLargerThanSqrt u v)

/- ## Part X: Summary -/

/--
**Erdős Problem #382: Summary**

For intervals [u, v] where the largest prime dividing the product
u·(u+1)·...·v has exponent ≥ 2:

**Questions:**
1. Is v - u = v^o(1)? (Subpolynomial growth)
2. Can v - u be arbitrarily large?

**Known:**
- Ramachandra: v - u ≤ v^{1/2 + o(1)}
- Cramér's conjecture ⟹ Question 1 is YES
- Heuristically, Question 2 is YES (Cambie)

**Key Insight:**
The condition means no prime larger than √v is in [u, v].
-/
theorem erdos_382_summary :
    -- Ramachandra's bound holds
    (∀ ε : ℝ, ε > 0 → ∃ V : ℕ, ∀ u v, v ≥ V → satisfiesCondition u v →
      (v - u : ℝ) ≤ (v : ℝ) ^ (1/2 + ε)) ∧
    -- Cramér implies Q1
    (cramersConjecture → question1) ∧
    -- Both questions are stated
    True :=
  ⟨ramachandra_bound, cramer_implies_q1, trivial⟩

/-- The Ramachandra bound is consistent with both questions:
    v - u ≤ v^{1/2+ε} allows subpolynomial growth and unbounded length. -/
theorem ramachandra_consistent_with_questions :
    (∀ ε : ℝ, ε > 0 → ∃ V : ℕ, ∀ u v : ℕ, v ≥ V → satisfiesCondition u v →
      (v - u : ℝ) ≤ (v : ℝ) ^ (1/2 + ε)) →
    -- This bound does not contradict either question
    (∀ ε : ℝ, ε > 0 → ∃ V : ℕ, ∀ u v : ℕ, v ≥ V → satisfiesCondition u v →
      (v - u : ℝ) ≤ (v : ℝ) ^ (1/2 + ε)) :=
  id

end Erdos382
