/-
  Erdős Problem #387: Divisors of Binomial Coefficients Near n

  Is there an absolute constant c > 0 such that, for all 1 ≤ k < n,
  the binomial coefficient C(n,k) has a divisor in the interval (cn, n]?

  **Status**: OPEN - The main conjecture remains unresolved.

  **Historical Context**:
  Erdős originally conjectured the stronger statement that C(n,k) must always
  have a divisor in (n-k, n]. This was disproved by Schinzel, who found that
  n = 99215 and k = 15 is a counterexample.

  **What We Formalize**:
  1. The counterexample: 99215 - i does not divide C(99215, 15) for all i < 15
  2. The "easy" result: C(n,k) always has a divisor in [n/k, n]

  References:
  - https://erdosproblems.com/387
  - Schinzel, A. "Sur un problème de P. Erdős" Colloq. Math. (1958), 198-204
  - Guy, R.K. "Unsolved Problems in Number Theory" (2004), Problems B33-B34
  - Faulkner, M. "On a theorem of Sylvester and Schur" J. London Math. Soc. (1966)
-/

import Mathlib

namespace Erdos387

/-!
## The Schinzel-Erdős Counterexample

Erdős originally conjectured that C(n,k) must always have a divisor in (n-k, n].
Schinzel disproved this by finding n = 99215 and k = 15.

We verify computationally that no integer in (99215 - 15, 99215] = (99200, 99215]
divides C(99215, 15). This means checking that 99215 - i does not divide C(99215, 15)
for i ∈ {0, 1, ..., 14}.
-/

/-- Schinzel's counterexample: For each i < 15, the value 99215 - i does not
divide C(99215, 15). This disproves Erdős's original conjecture that C(n,k)
always has a divisor in (n-k, n]. -/
theorem schinzel_counterexample : ∀ i : ℕ, i < 15 → ¬(99215 - i ∣ Nat.choose 99215 15) := by
  intro i hi
  interval_cases i <;> native_decide

/-!
## The Easy Bound

It is straightforward to show that C(n,k) always has a divisor in [n/k, n].
The key observation is that gcd(C(n,k), n) provides such a divisor.

This uses the identity: n · C(n-1, k-1) = k · C(n,k)
which implies n divides k · C(n,k), and hence gcd(C(n,k), n) ≥ n/k.
-/

/-- The binomial coefficient C(n,k) always has a divisor d with n/k ≤ d ≤ n.
This is the "easy" result mentioned in Guy's collection.
Adapted from formal-conjectures proof. -/
theorem easy_divisor_bound {n k : ℕ} (hn : 1 ≤ n) (hk : k ≤ n) :
    ∃ d : ℕ, (d : ℝ) ∈ Set.Icc (n / k : ℝ) n ∧ d ∣ Nat.choose n k := by
  by_cases hk0 : k = 0 <;> simp_all
  refine ⟨(n.choose k).gcd n, ⟨?_, ?_⟩, Nat.gcd_dvd_left _ _⟩
  · rw [div_le_iff₀ (by positivity)]
    norm_cast
    rw [← Nat.gcd_mul_right]
    refine Nat.le_of_dvd ?_ (Nat.dvd_gcd ⟨(n - 1).choose (k - 1), ?_⟩ (dvd_mul_right _ _))
    · exact Nat.gcd_pos_of_pos_right _ (by positivity)
    · cases n <;> cases k <;> simp_all [Nat.add_one_mul_choose_eq]
  · exact Nat.le_of_dvd (by linarith) (Nat.gcd_dvd_right _ _)

/-!
## The Main Open Problem

The central question remains: Does there exist an absolute constant c > 0 such that
C(n,k) has a divisor in (cn, n] for ALL pairs (n,k) with 1 ≤ k < n?

The easy bound gives [n/k, n], but this interval shrinks as k grows.
The question asks for a fixed lower bound cn independent of k.

Erdős conjectured this holds for any c < 1 when n is sufficiently large.
-/

/-- The main open conjecture: There exists c > 0 such that for all 1 ≤ k < n,
the binomial coefficient C(n,k) has a divisor in the interval (cn, n].

This remains OPEN. We state it as an axiom to enable reasoning about consequences. -/
axiom erdos_387_conjecture : ∃ c : ℝ, 0 < c ∧
  ∀ n k : ℕ, 1 ≤ k → k < n → ∃ d : ℕ, (d : ℝ) ∈ Set.Ioc (c * n) n ∧ d ∣ Nat.choose n k

/-!
## Related Conjectures

**Schinzel's Conjecture**: For all sufficiently large k that are not prime powers,
there exists n such that C(n,k) has no divisor in (n-k, n].

**Erdős's Variant**: For any c < 1, and all n sufficiently large, C(n,k) has a
divisor in (cn, n] for all 1 ≤ k < n.

Both remain open.
-/

end Erdos387
