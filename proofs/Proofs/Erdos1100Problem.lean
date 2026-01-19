/-
Erdős Problem #1100: Coprime Consecutive Divisors

Source: https://erdosproblems.com/1100
Status: OPEN

Statement:
Let 1 = d₁ < d₂ < ... < d_τ(n) = n be the divisors of n.
Define τ⊥(n) = count of i where gcd(dᵢ, dᵢ₊₁) = 1.

Questions:
1. Does τ⊥(n)/ω(n) → ∞ for almost all n?
2. Is τ⊥(n) < exp((log n)^o(1)) for all n?
3. For squarefree n with ω(n) = k, what is g(k) = max τ⊥(n)?

Known Results:
- τ⊥(n) ≥ ω(n) trivially (with equality for infinitely many n)
- Erdős-Hall: max_{n<x} τ⊥(n) > exp((log log x)^(2-ε))
- Erdős-Simonovits: (√2 + o(1))^k < g(k) < (2-c)^k for some c > 0

References:
- Erdős, Hall (1978): "On some unconventional problems on the divisors of integers"
- Erdős (1981): Compilation [Er81h]
-/

import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Prime.Defs
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

open Real Nat Finset

namespace Erdos1100

/-
## Part I: Divisor Functions
-/

/--
**Divisors of n (sorted):**
The list of divisors of n in increasing order: 1 = d₁ < d₂ < ... < d_τ(n) = n.
-/
noncomputable def divisorList (n : ℕ) : List ℕ :=
  (Finset.filter (· ∣ n) (Finset.range (n + 1))).sort (· ≤ ·)

/--
**τ(n): Number of divisors**
-/
def tau (n : ℕ) : ℕ := (Finset.filter (· ∣ n) (Finset.range (n + 1))).card

/--
**ω(n): Number of distinct prime divisors**
-/
def omega (n : ℕ) : ℕ := n.primeFactors.card

/-
## Part II: Coprime Consecutive Divisors
-/

/--
**τ⊥(n): Count of coprime consecutive divisor pairs**
Count the number of indices i where gcd(dᵢ, dᵢ₊₁) = 1.
-/
noncomputable def tauPerp (n : ℕ) : ℕ :=
  let divs := divisorList n
  (List.range (divs.length - 1)).filter
    (fun i => Nat.gcd (divs.getD i 0) (divs.getD (i + 1) 0) = 1)
  |>.length

/--
**Basic property: τ⊥(n) ≥ ω(n)**
At minimum, consecutive prime powers contribute coprime pairs.
-/
axiom tau_perp_lower_bound (n : ℕ) (hn : n > 0) : tauPerp n ≥ omega n

/--
**Equality achieved infinitely often:**
There exist infinitely many n with τ⊥(n) = ω(n).
-/
axiom tau_perp_equality_infinitely_often :
  ∀ N : ℕ, ∃ n : ℕ, n > N ∧ tauPerp n = omega n

/-
## Part III: Question 1 - Almost All Growth
-/

/--
**Question 1 (OPEN):**
Does τ⊥(n)/ω(n) → ∞ for almost all n?

"Almost all" means the set of exceptions has density 0.
-/
def question1_almost_all_growth : Prop :=
  ∀ M : ℝ, M > 0 →
    -- The density of n with τ⊥(n)/ω(n) < M tends to 0
    ∀ ε > 0, ∃ X : ℕ, ∀ x : ℕ, x ≥ X →
      (Finset.filter
        (fun n => (tauPerp n : ℝ) / (omega n) < M ∧ omega n > 0)
        (Finset.range x)).card / (x : ℝ) < ε

/--
**Status of Question 1: OPEN**
-/
axiom question1_open : True

/-
## Part IV: Question 2 - Upper Bound
-/

/--
**Question 2 (OPEN):**
Is τ⊥(n) < exp((log n)^o(1)) for all n?

This asks if τ⊥(n) grows slower than any fixed power of log n.
-/
def question2_upper_bound : Prop :=
  ∀ ε > 0, ∃ N : ℕ, ∀ n : ℕ, n ≥ N →
    (tauPerp n : ℝ) < exp ((log n)^ε)

/--
**Erdős-Hall lower bound on the maximum:**
For all ε > 0 and sufficiently large x:
  max_{n<x} τ⊥(n) > exp((log log x)^(2-ε))
-/
axiom erdos_hall_max_lower_bound :
  ∀ ε > 0, ∃ X : ℕ, ∀ x : ℕ, x ≥ X →
    ∃ n : ℕ, n < x ∧ (tauPerp n : ℝ) > exp ((log (log x))^(2 - ε))

/--
**Status of Question 2: OPEN**
-/
axiom question2_open : True

/-
## Part V: Question 3 - Growth of g(k)
-/

/--
**g(k): Maximum τ⊥ among squarefree n with exactly k prime factors**
-/
noncomputable def g (k : ℕ) : ℕ :=
  sSup { tauPerp n | n : ℕ, Squarefree n ∧ omega n = k }

/--
**Erdős-Simonovits bounds on g(k):**
(√2 + o(1))^k < g(k) < (2-c)^k for some constant c > 0.
-/
axiom erdos_simonovits_bounds :
  ∃ c : ℝ, c > 0 ∧
    -- Lower bound
    (∀ ε > 0, ∃ K : ℕ, ∀ k : ℕ, k ≥ K →
      (g k : ℝ) > (Real.sqrt 2 - ε)^k) ∧
    -- Upper bound
    (∃ K : ℕ, ∀ k : ℕ, k ≥ K →
      (g k : ℝ) < (2 - c)^k)

/--
**The growth rate of g(k):**
The base of exponential growth is between √2 ≈ 1.414 and 2-c < 2.
-/
theorem g_exponential_growth :
    ∃ α β : ℝ, Real.sqrt 2 ≤ α ∧ β < 2 ∧
      ∀ k : ℕ, k ≥ 10 →
        α^k ≤ (g k : ℝ) ∧ (g k : ℝ) ≤ β^k := by
  obtain ⟨c, hc, hlower, hupper⟩ := erdos_simonovits_bounds
  use Real.sqrt 2, 2 - c
  constructor
  · linarith
  constructor
  · linarith
  · intro k _
    constructor
    · -- Lower bound
      sorry -- Requires the limit statement
    · -- Upper bound
      sorry -- From hupper

/-
## Part VI: Examples
-/

/--
**Example: n = 6**
Divisors: 1, 2, 3, 6
- gcd(1,2) = 1 ✓
- gcd(2,3) = 1 ✓
- gcd(3,6) = 3 ✗
τ⊥(6) = 2, ω(6) = 2
-/
example : omega 6 = 2 := by native_decide

/--
**Example: n = 12**
Divisors: 1, 2, 3, 4, 6, 12
- gcd(1,2) = 1 ✓
- gcd(2,3) = 1 ✓
- gcd(3,4) = 1 ✓
- gcd(4,6) = 2 ✗
- gcd(6,12) = 6 ✗
τ⊥(12) = 3, ω(12) = 2
-/
example : omega 12 = 2 := by native_decide

/-
## Part VII: Why This Problem Is Hard
-/

/--
**Structural Insight:**
The coprime consecutive divisors depend delicately on the factorization of n.
For n = p₁^a₁ · ... · p_k^a_k:
- Consecutive divisors differ by multiplying/dividing by primes
- Coprimality requires the consecutive divisors to share no common prime
- This creates intricate combinatorial constraints

The exponential bounds on g(k) show the structure is neither trivial nor chaotic.
-/
axiom structural_insight : True

/-
## Part VIII: Summary
-/

/--
**Erdős Problem #1100: Status**

**Definition:**
τ⊥(n) = number of coprime consecutive divisor pairs of n.

**Questions:**
1. τ⊥(n)/ω(n) → ∞ for almost all n? **OPEN**
2. τ⊥(n) < exp((log n)^o(1)) for all n? **OPEN**
3. Growth rate of g(k) = max τ⊥(n) for squarefree n with ω(n) = k?
   **Partially known:** (√2)^k < g(k) < (2-c)^k

**Key Results:**
- τ⊥(n) ≥ ω(n) (trivial lower bound)
- max_{n<x} τ⊥(n) > exp((log log x)^(2-ε)) [Erdős-Hall]
- Erdős-Simonovits bounds on g(k)
-/
theorem erdos_1100_summary :
    -- τ⊥(n) ≥ ω(n)
    (∀ n : ℕ, n > 0 → tauPerp n ≥ omega n) ∧
    -- Equality for infinitely many n
    (∀ N : ℕ, ∃ n : ℕ, n > N ∧ tauPerp n = omega n) ∧
    -- Erdős-Hall lower bound on max
    (∀ ε > 0, ∃ X : ℕ, ∀ x : ℕ, x ≥ X →
      ∃ n : ℕ, n < x ∧ (tauPerp n : ℝ) > exp ((log (log x))^(2 - ε))) := by
  constructor
  · exact tau_perp_lower_bound
  constructor
  · exact tau_perp_equality_infinitely_often
  · exact erdos_hall_max_lower_bound

end Erdos1100
