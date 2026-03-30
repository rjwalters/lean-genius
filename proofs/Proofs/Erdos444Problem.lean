/-
Erdős Problem #444: Generalized Divisor Functions

Source: https://erdosproblems.com/444
Status: SOLVED (Erdős-Sárközy 1980)

Statement:
Let A ⊆ ℕ be infinite and d_A(n) count the divisors of n belonging to A.
Is it true that, for every k,
  limsup_{x→∞} max_{n<x} d_A(n) / (∑_{a∈A, a<x} 1/a)^k = ∞?

Resolution:
The answer is YES, proved by Erdős and Sárközy [ErSa80].

Historical Note:
From Erdős and Graham [ErGr80, p. 88]. This problem studies the relationship
between the growth of divisor counting functions restricted to A and the
harmonic sum over A.

References:
- Erdős-Graham [ErGr80]: Original problem (p. 88)
- Erdős-Sárközy [ErSa80]: Complete solution
-/

import Mathlib.Data.Nat.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Basic

namespace Erdos444

/-
## Part I: Basic Definitions
-/

/--
**Infinite subset of naturals:**
A ⊆ ℕ is an infinite set of positive integers.
-/
def InfiniteSubset (A : Set ℕ) : Prop :=
  Set.Infinite A

/--
**The generalized divisor function d_A(n):**
d_A(n) = |{a ∈ A : a | n}|, the number of divisors of n that belong to A.
-/
def d_A (A : Set ℕ) (n : ℕ) : ℕ :=
  (Finset.filter (fun a => a ∈ A ∧ a ∣ n) (Finset.range (n + 1))).card

/--
**The partial harmonic sum over A:**
H_A(x) = ∑_{a ∈ A, a < x} 1/a, the sum of reciprocals of elements of A up to x.
-/
noncomputable def H_A (A : Set ℕ) (x : ℕ) : ℝ :=
  ∑ a ∈ Finset.filter (· ∈ A) (Finset.range x), (1 : ℝ) / a

/--
**Maximum divisor count:**
M_A(x) = max_{n < x} d_A(n), the maximum of d_A over [1, x).
-/
def M_A (A : Set ℕ) (x : ℕ) : ℕ :=
  (Finset.range x).sup (d_A A)

/-
## Part II: The Main Conjecture (Proved)
-/

/--
**The Erdős-Graham Conjecture:**
For any infinite A ⊆ ℕ and any k ≥ 1,
limsup_{x→∞} M_A(x) / H_A(x)^k = ∞.

In other words, the maximum divisor count grows faster than
any fixed power of the partial harmonic sum.
-/
def erdos_graham_conjecture : Prop :=
  ∀ A : Set ℕ, InfiniteSubset A →
  ∀ k : ℕ, k ≥ 1 →
  ∀ C : ℝ, C > 0 →
  ∃ᶠ x in Filter.atTop, (M_A A x : ℝ) > C * (H_A A x)^k

/--
**The conjecture is TRUE:**
Proved by Erdős and Sárközy in 1980.
-/
axiom erdos_graham_conjecture_true : erdos_graham_conjecture

/-
## Part III: Special Cases
-/

/-- When A = ℕ, d_A(n) = d(n), the standard divisor function.
    H_A(x) ≈ log x. The maximum max_{n<x} d(n) grows like
    exp(c log x / log log x), much faster than any (log x)^k. -/
/-- When A = primes, d_A(n) = ω(n), the number of distinct prime factors.
    H_A(x) ≈ log log x (Mertens). max_{n<x} ω(n) ~ log x / log log x. -/
def IsPrime (n : ℕ) : Prop := Nat.Prime n

/-
## Part IV: Structural Properties
-/

/-- Highly composite numbers relative to A achieve large d_A values.
    For any A and any target, there exist n with d_A(n) exceeding
    any power of H_A. -/
/-- The maximum M_A grows at least exponentially relative to H_A:
    M_A(x) ≥ exp(c · H_A(x)) for some c > 0 depending on A. -/
/-- There is no universal function f bounding M_A(x) in terms of H_A(x)
    for all infinite A: for any f, some A violates M_A(x) ≤ f(H_A(x)). -/
/-
## Part V: Summary
-/

/--
**Summary of Erdős Problem #444:**

PROBLEM: Let A ⊆ ℕ be infinite and d_A(n) count divisors of n in A.
Is it true that for every k,
limsup_{x→∞} max_{n<x} d_A(n) / (∑_{a∈A, a<x} 1/a)^k = ∞?

STATUS: SOLVED (YES) by Erdős-Sárközy 1980

KNOWN:
- The maximum divisor count M_A(x) grows faster than any H_A(x)^k
- This holds for ALL infinite A ⊆ ℕ
- Special cases: A = ℕ gives d(n), A = primes gives ω(n)
- M_A grows at least exponentially in H_A for favorable A
-/
theorem erdos_444_summary :
    erdos_graham_conjecture := erdos_graham_conjecture_true

/-- The limsup is infinite for all k: direct consequence of the main theorem. -/
theorem limsup_infinite (A : Set ℕ) (hA : InfiniteSubset A) (k : ℕ) (hk : k ≥ 1) :
    ∀ C : ℝ, C > 0 → ∃ᶠ x in Filter.atTop, (M_A A x : ℝ) > C * (H_A A x)^k := by
  intro C hC
  exact erdos_graham_conjecture_true A hA k hk C hC

end Erdos444
