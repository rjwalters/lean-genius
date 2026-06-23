/-
  q-Binomial Coefficients (Gaussian Binomial Coefficients)
  Open Question: binomial-theorem-oq-02-oq-02-oq-01

  Builds the Gaussian binomial coefficient (q-binomial coefficient) from first
  principles, since Mathlib v4.26.0 has no `GaussianBinomial` API. Establishes
  the foundational identities and the q-Vandermonde base cases.

  Toward the q-Vandermonde identity:
    \binom{m+n}{r}_q = ∑_{k=0}^{r} q^{(m-k)(r-k)} · \binom{m}{k}_q · \binom{n}{r-k}_q

  ## Design

  We define `qBinomial (q : R) : ℕ → ℕ → R` over any `CommSemiring R` via the
  recurrence
    \binom{n+1}{k+1}_q = q^{k+1} · \binom{n}{k+1}_q + \binom{n}{k}_q
  with boundary \binom{n}{0}_q = 1 and \binom{0}{k+1}_q = 0.

  This makes the q-binomial computable and avoids division issues — no rational
  function or polynomial-quotient machinery needed.

  ## Key Results

  1. `qBinomial_zero_right`         : \binom{n}{0}_q = 1                    [boundary]
  2. `qBinomial_zero_succ`          : \binom{0}{k+1}_q = 0                  [boundary]
  3. `qBinomial_succ_succ`          : the q-Pascal recurrence (definitional)
  4. `qBinomial_eq_zero_of_lt`      : \binom{n}{k}_q = 0 when k > n
  5. `qBinomial_self`               : \binom{n}{n}_q = 1
  6. `qBinomial_at_one`             : at q = 1, recovers `Nat.choose` cast to R
  7. `qVandermonde_zero_left`      : q-Vandermonde for m = 0 (induction base)
  8. `qVandermonde_zero_right`     : q-Vandermonde for n = 0 (induction base)
  9. `vandermonde_zero_left`       : q = 1 specialization (classical Vandermonde, m=0)
  10. `vandermonde_zero_right`     : q = 1 specialization (classical Vandermonde, n=0)

  The full inductive q-Vandermonde proof is open future work; the base cases
  here are the foundation it builds on.

  ## References
  - Andrews, "The Theory of Partitions" (1976), Ch. 3
  - Kac & Cheung, "Quantum Calculus" (2002), §6
  - Stanley, "Enumerative Combinatorics" Vol. 1 (2nd ed., 2011), §1.7
-/

import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Tactic

namespace QBinomial

open Finset

variable {R : Type*} [CommSemiring R]

/-- The q-binomial (Gaussian binomial) coefficient `\binom{n}{k}_q` defined by
    the recurrence
      \binom{n+1}{k+1}_q = q^{k+1} · \binom{n}{k+1}_q + \binom{n}{k}_q
    with boundary `\binom{n}{0}_q = 1` and `\binom{0}{k+1}_q = 0`.

    At `q = 1` this reduces to the ordinary binomial coefficient `Nat.choose`. -/
def qBinomial (q : R) : ℕ → ℕ → R
  | _, 0 => 1
  | 0, _ + 1 => 0
  | n + 1, k + 1 => q ^ (k + 1) * qBinomial q n (k + 1) + qBinomial q n k

@[simp]
theorem qBinomial_zero_right (q : R) (n : ℕ) : qBinomial q n 0 = 1 := by
  cases n <;> rfl

@[simp]
theorem qBinomial_zero_succ (q : R) (k : ℕ) : qBinomial q 0 (k + 1) = 0 := rfl

/-- The q-Pascal recurrence (definitional from the recursive definition). -/
theorem qBinomial_succ_succ (q : R) (n k : ℕ) :
    qBinomial q (n + 1) (k + 1) =
      q ^ (k + 1) * qBinomial q n (k + 1) + qBinomial q n k := rfl

/-- Vanishing for k > n: `\binom{n}{k}_q = 0` when k strictly exceeds n. -/
theorem qBinomial_eq_zero_of_lt (q : R) :
    ∀ {n k : ℕ}, n < k → qBinomial q n k = 0
  | 0, 0, h => absurd h (Nat.lt_irrefl 0)
  | 0, _ + 1, _ => rfl
  | _ + 1, 0, h => absurd h (Nat.not_lt_zero _)
  | n + 1, k + 1, h => by
      have hn : n < k := Nat.lt_of_succ_lt_succ h
      have hn1 : n < k + 1 := Nat.lt_succ_of_lt hn
      rw [qBinomial_succ_succ, qBinomial_eq_zero_of_lt q hn1,
          qBinomial_eq_zero_of_lt q hn]
      ring

/-- `\binom{n}{n}_q = 1`. -/
@[simp]
theorem qBinomial_self (q : R) : ∀ n : ℕ, qBinomial q n n = 1
  | 0 => rfl
  | n + 1 => by
      rw [qBinomial_succ_succ, qBinomial_eq_zero_of_lt q (Nat.lt_succ_self n),
          qBinomial_self q n]
      ring

/-- The q-binomial coefficient at `q = 1` equals the ordinary binomial coefficient
    cast into `R`. -/
theorem qBinomial_at_one : ∀ n k : ℕ, qBinomial (1 : R) n k = (Nat.choose n k : R)
  | 0, 0 => by simp
  | 0, k + 1 => by simp [Nat.choose_zero_succ]
  | n + 1, 0 => by simp
  | n + 1, k + 1 => by
      rw [qBinomial_succ_succ, qBinomial_at_one n (k + 1), qBinomial_at_one n k,
          one_pow, one_mul, Nat.choose_succ_succ]
      push_cast
      ring

/-!
## q-Vandermonde Base Cases

The q-Vandermonde identity:
  \binom{m+n}{r}_q = ∑_{k=0}^{r} q^{(m-k)(r-k)} · \binom{m}{k}_q · \binom{n}{r-k}_q

We prove the two base cases (m = 0 and n = 0) explicitly. The full identity
follows by induction on m using the q-Pascal recurrence; that proof is left
as a future contribution.
-/

/-- q-Vandermonde, base case `m = 0`:
    `\binom{0+n}{r}_q = \binom{n}{r}_q`, with the sum collapsing to a single term.

    The only nonzero summand is k = 0 (since `\binom{0}{j}_q = 0` for j ≥ 1). -/
theorem qVandermonde_zero_left (q : R) (n r : ℕ) :
    qBinomial q n r = ∑ k ∈ range (r + 1), q ^ ((0 - k) * (r - k)) *
      qBinomial q 0 k * qBinomial q n (r - k) := by
  rw [Finset.sum_range_succ' _ r]
  -- simp simultaneously: (a) reduces the pulled-out k=0 term to `qBinomial q n r`
  -- and (b) collapses the q^((0-(i+1))*(r-(i+1))) factor inside the sum to 1.
  simp only [Nat.zero_sub, Nat.zero_mul, pow_zero, qBinomial_zero_right, one_mul,
             Nat.sub_zero]
  -- After the simp, summand reduces to `qBinomial q 0 (i+1) * qBinomial q n (r-(i+1))`,
  -- which vanishes because qBinomial q 0 (i+1) = 0.
  have hzero : ∀ i ∈ range r,
      qBinomial q 0 (i + 1) * qBinomial q n (r - (i + 1)) = 0 := by
    intro i _
    simp
  rw [Finset.sum_congr rfl hzero, Finset.sum_const_zero, zero_add]

/-- q-Vandermonde, base case `n = 0`:
    `\binom{m+0}{r}_q = \binom{m}{r}_q`, with the sum collapsing to a single term.

    The only nonzero summand is k = r (since `\binom{0}{j}_q = 0` for j ≥ 1). -/
theorem qVandermonde_zero_right (q : R) (m r : ℕ) :
    qBinomial q m r = ∑ k ∈ range (r + 1), q ^ ((m - k) * (r - k)) *
      qBinomial q m k * qBinomial q 0 (r - k) := by
  rw [Finset.sum_range_succ]
  -- The pulled-out k=r term simplifies to qBinomial q m r (need both `one_mul`
  -- and `mul_one` to clear the trailing `1 * _` after qBinomial_zero_right fires).
  simp only [Nat.sub_self, Nat.mul_zero, pow_zero, qBinomial_zero_right, one_mul,
             mul_one]
  -- The remaining sum (over k = 0, ..., r-1) vanishes because qBinomial q 0 (r-k) = 0
  have hzero : ∀ k ∈ range r,
      q ^ ((m - k) * (r - k)) * qBinomial q m k * qBinomial q 0 (r - k) = 0 := by
    intro k hk
    have hkr : k < r := Finset.mem_range.mp hk
    obtain ⟨j, hj⟩ : ∃ j, r - k = j + 1 := ⟨r - k - 1, by omega⟩
    rw [hj]
    simp
  rw [Finset.sum_congr rfl hzero, Finset.sum_const_zero, zero_add]

/-!
## Specialization at q = 1: Classical Vandermonde

At q = 1 the q-Vandermonde reduces to the classical Vandermonde identity
`(m+n).choose r = ∑_k (m.choose k) · (n.choose (r-k))`.

We give the corresponding base cases here, derived directly (not via the
q-Vandermonde base cases — the q^{(m-k)(r-k)} factor becomes 1 trivially).
-/

/-- Classical Vandermonde, `m = 0` base case (in ℕ):
    `\binom{n}{r} = ∑_k \binom{0}{k} · \binom{n}{r-k}`. -/
theorem vandermonde_zero_left_nat (n r : ℕ) :
    Nat.choose n r = ∑ k ∈ range (r + 1), Nat.choose 0 k * Nat.choose n (r - k) := by
  rw [Finset.sum_range_succ' _ r]
  simp [Nat.choose_zero_succ]

/-- Classical Vandermonde, `n = 0` base case (in ℕ):
    `\binom{m}{r} = ∑_k \binom{m}{k} · \binom{0}{r-k}`. -/
theorem vandermonde_zero_right_nat (m r : ℕ) :
    Nat.choose m r = ∑ k ∈ range (r + 1), Nat.choose m k * Nat.choose 0 (r - k) := by
  rw [Finset.sum_range_succ]
  simp only [Nat.sub_self, Nat.choose_zero_right, Nat.mul_one]
  have : ∀ k ∈ range r, Nat.choose m k * Nat.choose 0 (r - k) = 0 := by
    intro k hk
    have hkr : k < r := Finset.mem_range.mp hk
    obtain ⟨j, hj⟩ : ∃ j, r - k = j + 1 := ⟨r - k - 1, by omega⟩
    rw [hj, Nat.choose_zero_succ, Nat.mul_zero]
  rw [Finset.sum_congr rfl this, Finset.sum_const_zero, zero_add]

/-!
## Closed Form for k = 1: Geometric Sum

The q-binomial $\binom{n}{1}_q$ equals the geometric sum $\sum_{i=0}^{n-1} q^i$.
This is the q-analog of $\binom{n}{1} = n$, and is the simplest non-trivial
closed form: it instantiates the general principle that q-binomials are
"polynomials with $\binom{n}{k}$ terms in $q$".

Combined with the symmetric closed form $\binom{n+1}{n}_q = \sum_{i=0}^{n} q^i$,
this gives the simplest case of q-binomial reflection symmetry:
$\binom{n+1}{1}_q = \binom{n+1}{n}_q$.
-/

/-- **Closed form at k = 1**: `\binom{n}{1}_q = ∑_{i=0}^{n-1} q^i`.

    Proof by induction on n using the q-Pascal recurrence
    $\binom{n+1}{1}_q = q \binom{n}{1}_q + \binom{n}{0}_q = q \binom{n}{1}_q + 1$,
    so $\binom{n}{1}_q$ satisfies $a_{n+1} = q a_n + 1$, $a_0 = 0$,
    whose solution is the geometric sum. -/
theorem qBinomial_one_eq_geom_sum (q : R) :
    ∀ n : ℕ, qBinomial q n 1 = ∑ i ∈ range n, q ^ i
  | 0 => by simp
  | n + 1 => by
      rw [qBinomial_succ_succ, qBinomial_zero_right, qBinomial_one_eq_geom_sum q n,
          pow_one, Finset.sum_range_succ' (fun i => q ^ i) n]
      simp [Finset.mul_sum, pow_succ, mul_comm]

/-- **Closed form at k = n** for $\binom{n+1}{n}_q$:
    `\binom{n+1}{n}_q = ∑_{i=0}^{n} q^i`.

    Proof by induction on n using the q-Pascal recurrence
    $\binom{n+1}{n}_q = q^n \binom{n}{n}_q + \binom{n}{n-1}_q = q^n + \binom{n}{n-1}_q$
    (after handling the base case n = 0). -/
theorem qBinomial_succ_pred_eq_geom_sum (q : R) :
    ∀ n : ℕ, qBinomial q (n + 1) n = ∑ i ∈ range (n + 1), q ^ i
  | 0 => by
      -- qBinomial q 1 0 = 1; ∑ i ∈ range 1, q^i = q^0 = 1
      simp
  | n + 1 => by
      -- qBinomial q (n+2) (n+1) = q^(n+1) * qBinomial q (n+1) (n+1) + qBinomial q (n+1) n
      --                         = q^(n+1) + ∑_{i=0}^{n} q^i = ∑_{i=0}^{n+1} q^i
      rw [qBinomial_succ_succ, qBinomial_self,
          qBinomial_succ_pred_eq_geom_sum q n,
          Finset.sum_range_succ (fun i => q ^ i) (n + 1)]
      ring

/-- **Reflection symmetry at k = 1**: `\binom{n+1}{1}_q = \binom{n+1}{n}_q`.

    Both equal the geometric sum $\sum_{i=0}^{n} q^i$. This is the simplest
    non-trivial case of the reflection symmetry $\binom{n}{k}_q = \binom{n}{n-k}_q$
    for k ≤ n; the general statement requires the dual q-Pascal recurrence. -/
theorem qBinomial_reflection_at_one (q : R) (n : ℕ) :
    qBinomial q (n + 1) 1 = qBinomial q (n + 1) n := by
  rw [qBinomial_one_eq_geom_sum q (n + 1), qBinomial_succ_pred_eq_geom_sum q n]

end QBinomial

/-!
## Summary

This file develops the q-binomial coefficient API from scratch (Mathlib v4.26.0
has no Gaussian binomial — see `Mathlib.RingTheory.Polynomial.Pochhammer`,
which mentions q-binomials only as a TODO).

### Established results
- Definition via the q-Pascal recurrence:
  \binom{n+1}{k+1}_q = q^{k+1}\binom{n}{k+1}_q + \binom{n}{k}_q
- Boundary lemmas: \binom{n}{0}_q = 1, \binom{0}{k+1}_q = 0
- Vanishing: \binom{n}{k}_q = 0 for k > n
- Diagonal: \binom{n}{n}_q = 1
- Specialization: at q = 1, qBinomial = Nat.choose (cast to R)
- q-Vandermonde base cases (m = 0 and n = 0, with classical analogues)

### Open future work
1. **Full q-Vandermonde induction**: prove the identity
     \binom{m+n}{r}_q = ∑_{k=0}^{r} q^{(m-k)(r-k)} · \binom{m}{k}_q · \binom{n}{r-k}_q
   for all m, n, r by induction on m, using the q-Pascal recurrence and the
   base cases established here.
2. **Dual q-Pascal**: \binom{n+1}{k+1}_q = \binom{n}{k+1}_q + q^{n-k}\binom{n}{k}_q
   (requires the closed-form \binom{n}{1}_q = 1 + q + … + q^{n-1} as a stepping
   stone, or a sophisticated double induction).
3. **Reflection symmetry**: \binom{n}{k}_q = \binom{n}{n-k}_q for k ≤ n, which
   follows from the dual q-Pascal rule.
4. **q-binomial theorem (Cauchy)**:
     ∏_{i=0}^{n-1} (1 + q^i x) = ∑_{k=0}^{n} q^{k(k-1)/2} · \binom{n}{k}_q · x^k
5. **Subspace counting**: \binom{n}{k}_q counts k-dimensional subspaces of 𝔽_q^n,
   linking the algebraic definition above to its combinatorial interpretation.
   This requires Mathlib's `Module.rank` API for finite vector spaces.

### Mathlib upstream potential
The core API here is a candidate for Mathlib contribution; suggested location
`Mathlib/Combinatorics/Enumerative/QBinomial.lean`. The recurrence-based
definition and lemmas are entirely self-contained — they need only
`CommSemiring`, no quotients or analysis.

Theorems Proved: 10, Axioms: 0, Sorries: 0
-/

#check @QBinomial.qBinomial
#check @QBinomial.qBinomial_succ_succ
#check @QBinomial.qBinomial_eq_zero_of_lt
#check @QBinomial.qBinomial_at_one
#check @QBinomial.qVandermonde_zero_left
#check @QBinomial.qVandermonde_zero_right
