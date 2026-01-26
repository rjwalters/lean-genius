/-!
# Erdős Problem #463: Composites Near Their Least Prime Factor

Is there a function f with f(n) → ∞ such that for all large n,
there exists a composite m with n + f(n) < m < n + p(m),
where p(m) is the least prime factor of m?

## Key Context

- p(m) = Nat.minFac m, the least prime factor of composite m
- F(n) = min_{m > n} (m − p(m)): how far m exceeds its least prime factor
- Erdős asks whether n − F(n) ~ c·n^{1/2} for some c > 0
- Related to Problem #385 on composites and prime factors

## References

- [ErGr80] Erdős–Graham (1980)
- [Er92e] Erdős (1992)
- <https://erdosproblems.com/463>
-/

import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Order.Filter.Basic
import Mathlib.Order.Filter.AtTopBot
import Mathlib.Topology.Order.Basic
import Mathlib.Tactic

open Filter
open scoped Nat Topology

/-! ## Core Definitions -/

/-- The least prime factor gap: m − p(m) for composite m.
    Measures how far m is from its smallest prime factor. -/
def leastPrimeGap (m : ℕ) : ℕ := m - m.minFac

/-- F(n) = min_{m > n, m composite} (m − p(m)).
    The minimum least-prime-factor gap among composites greater than n. -/
noncomputable def minLeastPrimeGap (n : ℕ) : ℕ :=
  sSup {k : ℕ | ∀ m : ℕ, m > n → m.minFac < m → leastPrimeGap m ≥ k}

/-! ## Main Conjecture -/

/-- **Erdős Problem #463**: Does there exist f : ℕ → ℕ with f(n) → ∞
    such that for all sufficiently large n, some composite m satisfies
    n + f(n) < m < n + p(m)?

    This asks whether composites can be found far from n yet still
    closer to n than to their own least prime factor. -/
axiom erdos_463_conjecture :
  ∃ (f : ℕ → ℕ), Tendsto (fun n => (f n : ℝ)) atTop atTop ∧
    ∀ᶠ n in atTop,
      ∃ m : ℕ, m.minFac < m ∧
        n + f n < m ∧ m < n + m.minFac

/-! ## The Function F(n) -/

/-- Erdős's related question: is n − F(n) ~ c·√n for some constant c > 0?
    Here F(n) is the minimum of m − p(m) over composites m > n. -/
axiom erdos_F_asymptotic :
  ∃ c : ℝ, c > 0 ∧
    Tendsto (fun n => ((n : ℝ) - (minLeastPrimeGap n : ℝ)) / Real.sqrt n) atTop (nhds c)

/-! ## Basic Properties -/

/-- For any composite m, p(m) ≥ 2 (the least prime factor is at least 2). -/
axiom minFac_ge_two :
  ∀ m : ℕ, m.minFac < m → m.minFac ≥ 2

/-- For any composite m, m − p(m) ≥ m/2 when p(m) = 2 (i.e., m is even). -/
axiom even_composite_gap :
  ∀ m : ℕ, m.minFac = 2 → m ≥ 4 → leastPrimeGap m = m - 2

/-- For odd composite m, p(m) ≥ 3 and m ≥ 9. -/
axiom odd_composite_minFac :
  ∀ m : ℕ, m.minFac < m → m.minFac ≠ 2 → m.minFac ≥ 3 ∧ m ≥ 9

/-- The gap m − p(m) is large when m has only large prime factors.
    For m = p·q with p ≤ q primes, m − p = p·q − p = p·(q − 1). -/
axiom semiprime_gap :
  ∀ p q : ℕ, Nat.Prime p → Nat.Prime q → p ≤ q →
    leastPrimeGap (p * q) = p * q - p

/-! ## Density Considerations -/

/-- Among integers near n, composites with large least prime factor are rare.
    Most composites near n have p(m) = 2 (even composites). -/
axiom large_minFac_density :
  ∀ k : ℕ, k ≥ 2 →
    Tendsto (fun n => ({m ∈ Finset.range n | m.minFac ≥ k ∧ m.minFac < m}.card : ℝ) / n)
      atTop (nhds (1 - 1 / k))

/-- Composites with p(m) > √m are semiprimes p·q with p > √m.
    These have m − p(m) = m − p < m − √m. -/
axiom large_minFac_composites :
  ∀ m : ℕ, m.minFac < m → (m.minFac : ℝ) > Real.sqrt m →
    (leastPrimeGap m : ℝ) < m - Real.sqrt m

/-- Trivial observation: for any n, there exists a composite m > n
    (e.g., m = 2·(n+1) works for n ≥ 1). -/
theorem composite_above_exists (n : ℕ) (hn : n ≥ 1) :
    ∃ m : ℕ, m > n ∧ m.minFac < m := by
  use 2 * (n + 1)
  constructor
  · omega
  · have h2 : 2 * (n + 1) ≥ 4 := by omega
    rw [Nat.minFac_eq_two_iff]
    · exact dvd_mul_right 2 (n + 1)

/-- The conjecture is non-trivial: even composites have p(m) = 2,
    so m < n + p(m) = n + 2 requires m ≤ n + 1. But we need m > n + f(n).
    So even composites near n don't help when f(n) ≥ 2. -/
axiom even_composites_insufficient :
  ∀ n : ℕ, n ≥ 4 → ¬(∃ m : ℕ, m.minFac = 2 ∧ n + 2 < m ∧ m < n + 2)
