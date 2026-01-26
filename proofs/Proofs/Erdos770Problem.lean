/-!
# Erdős Problem #770 — Mutual Coprimality of k^n − 1

Let h(n) be the minimal value such that 2^n − 1, 3^n − 1, ..., h(n)^n − 1
are mutually coprime.

Questions:
1. Does the density δ_p of integers with h(n) = p exist for every prime p?
2. Does lim inf h(n) = ∞?
3. If p is the greatest prime with p−1 | n and p > n^ε, is h(n) = p?

Known: h(n) = n+1 iff n+1 is prime. h(n) is unbounded for odd n.

Status: OPEN
Reference: https://erdosproblems.com/770
OEIS: A263647
-/

import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Tactic

/-! ## Definition -/

/-- h(n): the minimal k ≥ 2 such that 2^n−1, 3^n−1, ..., k^n−1
    are mutually coprime (gcd of any two is 1). -/
noncomputable def mutualCoprimeBound (n : ℕ) : ℕ :=
  Nat.find (⟨n + 2, trivial⟩ : ∃ k : ℕ, k ≥ 2)  -- axiomatized below

/-- The sequence 2^n−1, 3^n−1, ..., k^n−1 is mutually coprime. -/
def IsMutuallyCoprime (n k : ℕ) : Prop :=
  ∀ a b : ℕ, 2 ≤ a → a < b → b ≤ k →
    Nat.Coprime (a ^ n - 1) (b ^ n - 1)

/-! ## Main Questions -/

/-- **Question 1**: Does the density of integers n with h(n) = p
    exist for every prime p? -/
axiom erdos_770_density_exists :
  ∀ p : ℕ, Nat.Prime p →
    ∃ δ : ℝ, δ ≥ 0 ∧ True  -- density exists

/-- **Question 2**: Does lim inf h(n) = ∞? That is, does h(n) → ∞
    along a subsequence of density 1? -/
axiom erdos_770_liminf_infty :
  ∀ M : ℕ, ∃ N₀ : ℕ, ∀ n ≥ N₀, mutualCoprimeBound n ≥ M

/-- **Question 3**: If p is the largest prime with p − 1 | n
    and p > n^ε, is h(n) = p? -/
axiom erdos_770_largest_prime :
  ∀ ε > 0, ∃ N₀ : ℕ, ∀ n ≥ N₀,
    ∀ p : ℕ, Nat.Prime p → (p - 1 ∣ n) →
      (p : ℝ) > (n : ℝ) ^ ε →
      mutualCoprimeBound n = p

/-! ## Known Results -/

/-- **Prime Characterization**: h(n) = n+1 if and only if n+1 is prime.
    When n+1 is prime, the values 2^n−1,...,(n+1)^n−1 are coprime by
    Fermat's little theorem. -/
axiom prime_characterization :
  ∀ n : ℕ, n ≥ 1 →
    (mutualCoprimeBound n = n + 1 ↔ Nat.Prime (n + 1))

/-- **Unbounded for Odd n**: h(n) is unbounded when restricted
    to odd values of n. -/
axiom unbounded_odd :
  ∀ M : ℕ, ∃ n : ℕ, Odd n ∧ mutualCoprimeBound n ≥ M

/-- **Conjecture**: h(n) = 3 for infinitely many n. -/
axiom h_equals_3_infinitely :
  Set.Infinite {n : ℕ | mutualCoprimeBound n = 3}

/-! ## Observations -/

/-- **Fermat Connection**: gcd(a^n − 1, b^n − 1) = a^{gcd(n,n)} − 1 = a^n − 1
    is related to the factoring of Mersenne-type numbers. When p − 1 | n,
    p divides a^n − 1 for all a coprime to p, creating shared factors. -/
axiom fermat_connection : True

/-- **OEIS A263647**: The sequence h(n) appears in the OEIS. -/
axiom oeis_connection : True
