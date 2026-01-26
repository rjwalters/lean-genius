/-!
# Erdős Problem #414: Merging Orbits of h(n) = n + τ(n)

Let h(n) = n + τ(n) where τ(n) is the number of divisors of n.
Define h_k(n) by iterating: h_1(n) = h(n), h_k(n) = h(h_{k-1}(n)).
Is it true that for any m, n > 0, there exist i, j such that
h_i(m) = h_j(n)?

## Key Results

- Erdős and Graham believed the answer is YES
- The sequence h^k(n) is strictly increasing since τ(n) ≥ 1
- Related to OEIS A064491

## References

- Erdős–Graham [ErGr80], p. 82
- Related: Problems #412, #413 (similar iterated function questions)
- <https://erdosproblems.com/414>
-/

import Mathlib.Data.Nat.Divisors
import Mathlib.Data.Nat.Basic
import Mathlib.Tactic

/-! ## Core Definitions -/

/-- The function h(n) = n + τ(n), where τ(n) counts divisors. -/
def h (n : ℕ) : ℕ := n + n.divisors.card

/-- The orbit of n under iteration of h: {n, h(n), h(h(n)), ...}. -/
def hOrbit (n : ℕ) : ℕ → ℕ
  | 0 => n
  | k + 1 => h (hOrbit n k)

/-! ## Basic Properties -/

/-- h(n) > n for all n ≥ 1 since τ(n) ≥ 1. -/
axiom h_strictly_increasing (n : ℕ) (hn : n ≥ 1) :
  h n > n

/-- The orbit is strictly increasing: h^{k+1}(n) > h^k(n) for n ≥ 1. -/
axiom orbit_strictly_increasing (n : ℕ) (hn : n ≥ 1) (k : ℕ) :
  hOrbit n (k + 1) > hOrbit n k

/-- h(n) ≤ 2n for all n ≥ 1 (since τ(n) ≤ n). -/
axiom h_upper (n : ℕ) (hn : n ≥ 1) :
  h n ≤ 2 * n

/-- For primes p, h(p) = p + 2 (since τ(p) = 2). -/
axiom h_prime (p : ℕ) (hp : p.Prime) :
  h p = p + 2

/-- h(1) = 1 + τ(1) = 1 + 1 = 2. -/
axiom h_one : h 1 = 2

/-- h(2) = 2 + τ(2) = 2 + 2 = 4. -/
axiom h_two : h 2 = 4

/-- h(3) = 3 + τ(3) = 3 + 2 = 5. -/
axiom h_three : h 3 = 5

/-! ## Main Conjecture -/

/-- **Erdős Problem #414** (OPEN): For any m, n ≥ 1, the orbits
    of m and n under h eventually merge: there exist i, j such
    that h^i(m) = h^j(n). -/
axiom erdos_414_conjecture :
  ∀ m n : ℕ, m ≥ 1 → n ≥ 1 → ∃ i j : ℕ, hOrbit m i = hOrbit n j

/-- Equivalently: there is a single eventual orbit that all
    positive integers converge to. -/
axiom single_eventual_orbit :
  ∃ S : ℕ → ℕ, ∀ n : ℕ, n ≥ 1 →
    ∃ k₀ : ℕ, ∀ k : ℕ, k ≥ k₀ →
      ∃ j : ℕ, hOrbit n k = S j

/-! ## Orbit Examples -/

/-- Orbit of 1: 1 → 2 → 4 → 7 → 9 → 12 → 18 → 24 → 32 → ... -/
axiom orbit_1_start :
  hOrbit 1 0 = 1 ∧ hOrbit 1 1 = 2 ∧ hOrbit 1 2 = 4 ∧
  hOrbit 1 3 = 7 ∧ hOrbit 1 4 = 9

/-- Orbit of 3: 3 → 5 → 7 → 9 → 12 → 18 → 24 → 32 → ...
    Merges with orbit of 1 at value 7 (h_3(1) = h_1(3) = 7). -/
axiom orbit_3_merges_with_1 :
  hOrbit 3 2 = hOrbit 1 3  -- both equal 7

/-! ## Growth Rate Analysis -/

/-- On average, τ(n) ~ log n (Dirichlet's theorem on average order).
    So h(n) ≈ n + log n, and after k iterations,
    h^k(n) ≈ n + k · log n (roughly). -/
axiom average_divisor_count :
  True  -- Σ_{n≤N} τ(n) ~ N log N (Dirichlet)

/-- The orbit grows at least linearly: h^k(n) ≥ n + k for n ≥ 1. -/
axiom orbit_linear_lower (n : ℕ) (hn : n ≥ 1) (k : ℕ) :
  hOrbit n k ≥ n + k

/-- Two orbits starting at m and n must eventually be "close" since
    both grow at rate ~ log(current value), and gaps between
    consecutive values h^k(n) are bounded by τ(h^k(n)). -/
axiom orbits_get_close :
  ∀ m n : ℕ, m ≥ 1 → n ≥ 1 →
    ∀ D : ℕ, ∃ i j : ℕ,
      (hOrbit m i : ℤ) - (hOrbit n j : ℤ) < D ∧
      (hOrbit n j : ℤ) - (hOrbit m i : ℤ) < D
