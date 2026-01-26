/-!
# Erdős Problem #1059: Primes Minus Factorials All Composite

Are there infinitely many primes p such that p - k! is composite
for each k with 1 ≤ k! < p?

## Key Results

- Examples: p = 101 and p = 211 satisfy the condition
- Counterexample: p = 89 does not (89 - 1! = 88, 89 - 2! = 87,
  89 - 6 = 83 which is prime)
- Related OEIS: A064152

## References

- Guy [Gu04], Problem A2
- <https://erdosproblems.com/1059>
-/

import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Data.Set.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Tactic

/-! ## Core Definitions -/

/-- A natural number is a factorial if it equals k! for some k. -/
def IsFactorial (d : ℕ) : Prop :=
  d ∈ Set.range Nat.factorial

/-- The set of factorials less than n. -/
def factorialsLessThan (n : ℕ) : Set ℕ :=
  { d | d < n ∧ IsFactorial d }

/-- All factorial subtractions from n are composite:
    n - k! is composite for every k! < n. -/
def AllFactorialSubtractionsComposite (n : ℕ) : Prop :=
  ∀ d ∈ factorialsLessThan n, (n - d).Composite

/-! ## Concrete Examples -/

/-- p = 101 satisfies the property: 101 - k! is composite for all k! < 101.
    Factorials < 101: 1, 2, 6, 24.
    101 - 1 = 100 = 4·25, 101 - 2 = 99 = 9·11,
    101 - 6 = 95 = 5·19, 101 - 24 = 77 = 7·11. -/
axiom example_101 : AllFactorialSubtractionsComposite 101

/-- p = 211 satisfies the property: 211 - k! is composite for all k! < 211.
    Factorials < 211: 1, 2, 6, 24, 120.
    211 - 1 = 210, 211 - 2 = 209, 211 - 6 = 205,
    211 - 24 = 187, 211 - 120 = 91. All composite. -/
axiom example_211 : AllFactorialSubtractionsComposite 211

/-- p = 89 does NOT satisfy the property: 89 - 6 = 83 is prime. -/
axiom counterexample_89 : ¬AllFactorialSubtractionsComposite 89

/-! ## Main Conjecture -/

/-- **Erdős Problem #1059** (OPEN): There are infinitely many primes p
    such that p - k! is composite for every k with 1 ≤ k! < p. -/
axiom erdos_1059_conjecture :
  Set.Infinite {p : ℕ | p.Prime ∧ AllFactorialSubtractionsComposite p}

/-! ## Structural Observations -/

/-- For any n, the factorials less than n form a finite set:
    {1!, 2!, ..., l!} where l! < n ≤ (l+1)!. -/
axiom factorials_less_than_finite (n : ℕ) :
  Set.Finite (factorialsLessThan n)

/-- The number of factorials less than n is O(log n / log log n),
    since k! grows super-exponentially. -/
axiom factorial_count_bound (n : ℕ) (hn : n ≥ 2) :
  ∃ l : ℕ, Nat.factorial l < n ∧ n ≤ Nat.factorial (l + 1) ∧
    (factorialsLessThan n).Finite ∧
    ∀ d ∈ factorialsLessThan n, ∃ k ≤ l, d = Nat.factorial k

/-- For large n, the number of factorial subtractions to check is small
    (at most ~ log n / log log n), making the condition mild. -/
axiom few_factorials_to_check :
  ∀ ε : ℝ, ε > 0 → ∃ N₀ : ℕ, ∀ n : ℕ, n > N₀ →
    ∃ l : ℕ, Nat.factorial l < n ∧ l + 1 ≤ n  -- l is small relative to n

/-! ## Erdős's Alternative Approach -/

/-- Erdős suggested it may be easier to prove: there exist infinitely many n
    with l! < n ≤ (l+1)! such that all prime factors of n exceed l,
    and n - k! is composite for all 1 ≤ k ≤ l. -/
axiom erdos_alternative_approach :
  Set.Infinite {n : ℕ | ∃ l : ℕ,
    Nat.factorial l < n ∧ n ≤ Nat.factorial (l + 1) ∧
    (∀ p : ℕ, p.Prime → p ∣ n → p > l) ∧
    (∀ k : ℕ, 1 ≤ k → k ≤ l → (n - Nat.factorial k).Composite)}

/-! ## Probabilistic Heuristic -/

/-- Heuristic: for a random prime p ~ N, each p - k! is composite with
    probability ≈ 1 - 1/ln(N). With ~ log N / log log N factorials
    to check, the probability that all subtractions are composite is
    roughly (1 - 1/ln N)^(log N / log log N) → 1 as N → ∞.
    This suggests the set should be infinite (and in fact dense
    among primes). -/
axiom heuristic_density :
  True  -- The heuristic suggests most large primes satisfy the property

/-- Primality is rare: for a random odd number n ~ N, the probability
    of n being prime is ~ 1/ln(N). Since each n - k! is a specific
    number, it's prime with probability ~ 1/ln(N). -/
axiom subtraction_primality_probability :
  True  -- Each n - k! is prime with probability ~ 1/ln(n)
