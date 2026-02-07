import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Tactic

/-
Erdős Problem #463: Composites Near Their Least Prime Factor

Is there a function f with f(n) → ∞ such that for all large n,
there exists a composite m with n + f(n) < m < n + p(m),
where p(m) is the least prime factor of m?

Key Context:
- p(m) = Nat.minFac m, the least prime factor of composite m
- F(n) = min_{m > n} (m - p(m)): how far m exceeds its least prime factor
- Erdős asks whether n - F(n) ~ c * sqrt(n) for some c > 0
- Related to Problem #385 on composites and prime factors

OPEN CONJECTURE (not formally stated to avoid heavy imports):
  ∃ f : ℕ → ℕ, f(n) → ∞ ∧ ∀ᶠ n, ∃ composite m,
    n + f(n) < m < n + m.minFac

OPEN RELATED QUESTION:
  ∃ c > 0, (n - F(n)) / sqrt(n) → c as n → ∞

References:
- [ErGr80] Erdős-Graham (1980)
- [Er92e] Erdős (1992)
- https://erdosproblems.com/463
-/

-- ## Core Definitions

/-- The least prime factor gap: m - p(m) for composite m.
    Measures how far m is from its smallest prime factor. -/
def leastPrimeGap (m : ℕ) : ℕ := m - m.minFac

-- ## Basic Properties (PROVED)

/-- For any composite m, p(m) ≥ 2 (the least prime factor is at least 2). -/
theorem minFac_ge_two (m : ℕ) (hc : m.minFac < m) : m.minFac ≥ 2 := by
  have hm1 : m ≠ 1 := by
    intro h; rw [h] at hc; simp [Nat.minFac_one] at hc
  exact (Nat.minFac_prime hm1).two_le

/-- For any composite m, leastPrimeGap m = m - 2 when p(m) = 2. -/
theorem even_composite_gap (m : ℕ) (hm2 : m.minFac = 2) :
    leastPrimeGap m = m - 2 := by
  unfold leastPrimeGap
  rw [hm2]

/-- For odd composite m, p(m) ≥ 3. -/
theorem odd_composite_minFac_ge_three (m : ℕ) (hc : m.minFac < m) (h2 : m.minFac ≠ 2) :
    m.minFac ≥ 3 := by
  have hm1 : m ≠ 1 := by
    intro h; rw [h] at hc; simp [Nat.minFac_one] at hc
  have hp := (Nat.minFac_prime hm1).two_le
  omega

/-- For odd composite m with p(m) ≥ 3, we have m ≥ 9.
    Proof: minFac^2 ≤ m for composites, and 3^2 = 9. -/
theorem odd_composite_ge_nine (m : ℕ) (hc : m.minFac < m) (h3 : m.minFac ≥ 3) :
    m ≥ 9 := by
  have hm1 : m ≠ 1 := by
    intro h; rw [h] at hc; simp [Nat.minFac_one] at hc
  have hm0 : 0 < m := by omega
  have hnp : ¬ m.Prime := by
    intro hp
    exact absurd hc (not_lt.mpr (le_of_eq hp.minFac_eq.symm))
  have hsq := Nat.minFac_sq_le_self hm0 hnp
  calc (9 : ℕ) = 3 * 3 := by norm_num
    _ ≤ m.minFac * m.minFac := Nat.mul_le_mul h3 h3
    _ = m.minFac ^ 2 := by ring
    _ ≤ m := hsq

/-- Trivial observation: for any n ≥ 1, there exists a composite m > n.
    We use m = 2 * (n+1), which is even and ≥ 4. -/
theorem composite_above_exists (n : ℕ) (hn : n ≥ 1) :
    ∃ m : ℕ, m > n ∧ m.minFac < m := by
  use 2 * (n + 1)
  refine ⟨by omega, ?_⟩
  have hne1 : 2 * (n + 1) ≠ 1 := by omega
  have hnp : ¬ Nat.Prime (2 * (n + 1)) := by
    intro hp
    have := hp.eq_one_or_self_of_dvd 2 (dvd_mul_right 2 (n + 1))
    omega
  have hle : (2 * (n + 1)).minFac ≤ 2 * (n + 1) := Nat.minFac_le (by omega)
  have hne : (2 * (n + 1)).minFac ≠ 2 * (n + 1) := by
    intro heq
    exact hnp (heq ▸ Nat.minFac_prime hne1)
  omega

/-- Even composites don't help for the conjecture when f(n) ≥ 2:
    m.minFac = 2 means m < n + 2 requires m ≤ n + 1,
    but we also need m > n + f(n) > n + 2. Contradiction. -/
theorem even_composites_insufficient (n : ℕ) :
    ¬(∃ m : ℕ, m.minFac = 2 ∧ n + 2 < m ∧ m < n + 2) := by
  intro ⟨_, _, h1, h2⟩
  omega

-- ## Key Structural Observations

/-- For the conjecture to hold, we need composites m with large minFac
    (specifically minFac > f(n)). -/
theorem conjecture_needs_large_minFac (n f_n m : ℕ)
    (hgt : n + f_n < m) (hlt : m < n + m.minFac) :
    m.minFac > f_n := by
  omega

/-- The gap leastPrimeGap m is bounded above by m. -/
theorem large_minFac_gap_bound (m : ℕ) :
    leastPrimeGap m ≤ m := by
  unfold leastPrimeGap
  omega

/-- The gap leastPrimeGap m is positive for composite m. -/
theorem leastPrimeGap_pos (m : ℕ) (hc : m.minFac < m) :
    leastPrimeGap m > 0 := by
  unfold leastPrimeGap
  omega
