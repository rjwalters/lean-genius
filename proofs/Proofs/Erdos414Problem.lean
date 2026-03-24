/-
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

import Mathlib.NumberTheory.Divisors
import Mathlib.Data.Nat.Basic
import Mathlib.Tactic

/- ## Core Definitions -/

/-- The function h(n) = n + τ(n), where τ(n) counts divisors. -/
def h (n : ℕ) : ℕ := n + n.divisors.card

/-- The orbit of n under iteration of h: {n, h(n), h(h(n)), ...}. -/
def hOrbit (n : ℕ) : ℕ → ℕ
  | 0 => n
  | k + 1 => h (hOrbit n k)

/- ## Basic Properties -/

/-- Every n ≥ 1 has at least one divisor (namely 1). -/
private theorem divisors_card_pos (n : ℕ) (hn : n ≥ 1) :
    n.divisors.card ≥ 1 := by
  have h1 : 1 ∈ n.divisors := by
    rw [Nat.mem_divisors]
    exact ⟨one_dvd n, by omega⟩
  exact Finset.card_pos.mpr ⟨1, h1⟩

/-- h(n) > n for all n ≥ 1 since τ(n) ≥ 1. -/
theorem h_strictly_increasing (n : ℕ) (hn : n ≥ 1) :
    h n > n := by
  unfold h
  have := divisors_card_pos n hn
  omega

/-- The orbit values are at least 1 when starting from n ≥ 1. -/
private theorem hOrbit_pos (n : ℕ) (hn : n ≥ 1) (k : ℕ) :
    hOrbit n k ≥ 1 := by
  induction k with
  | zero => simp [hOrbit]; exact hn
  | succ k ih =>
    simp [hOrbit]
    have := h_strictly_increasing (hOrbit n k) ih
    omega

/-- The orbit is strictly increasing: h^{k+1}(n) > h^k(n) for n ≥ 1. -/
theorem orbit_strictly_increasing (n : ℕ) (hn : n ≥ 1) (k : ℕ) :
    hOrbit n (k + 1) > hOrbit n k := by
  simp [hOrbit]
  exact h_strictly_increasing (hOrbit n k) (hOrbit_pos n hn k)

/-- h(n) ≤ 2n for all n ≥ 1 (since τ(n) ≤ n). -/
theorem h_upper (n : ℕ) (_hn : n ≥ 1) :
    h n ≤ 2 * n := by
  unfold h
  have : n.divisors.card ≤ n := Nat.card_divisors_le_self n
  omega

/-- For primes p, h(p) = p + 2 (since τ(p) = 2). -/
theorem h_prime (p : ℕ) (hp : p.Prime) :
    h p = p + 2 := by
  simp [h, Nat.Prime.divisors hp, Finset.card_pair (ne_of_lt hp.one_lt)]

/-- h(1) = 1 + τ(1) = 1 + 1 = 2. -/
theorem h_one : h 1 = 2 := by native_decide

/-- h(2) = 2 + τ(2) = 2 + 2 = 4. -/
theorem h_two : h 2 = 4 := by native_decide

/-- h(3) = 3 + τ(3) = 3 + 2 = 5. -/
theorem h_three : h 3 = 5 := by native_decide

/- ## Orbit Composition -/

/-- Orbit iteration is compositional: h^{a+b}(n) = h^b(h^a(n)). -/
theorem hOrbit_compose (n a b : ℕ) : hOrbit n (a + b) = hOrbit (hOrbit n a) b := by
  induction b with
  | zero => simp [hOrbit]
  | succ b ih => exact congrArg h ih

/- ## Main Conjecture -/

/-- **Erdős Problem #414** (OPEN): For any m, n ≥ 1, the orbits
    of m and n under h eventually merge: there exist i, j such
    that h^i(m) = h^j(n). -/
axiom erdos_414_conjecture :
  ∀ m n : ℕ, m ≥ 1 → n ≥ 1 → ∃ i j : ℕ, hOrbit m i = hOrbit n j

/-- Equivalently: there is a single eventual orbit that all
    positive integers converge to. Derived from the main conjecture
    by taking S = hOrbit 1 (the orbit of 1). -/
theorem single_eventual_orbit :
    ∃ S : ℕ → ℕ, ∀ n : ℕ, n ≥ 1 →
      ∃ k₀ : ℕ, ∀ k : ℕ, k ≥ k₀ →
        ∃ j : ℕ, hOrbit n k = S j := by
  refine ⟨hOrbit 1, fun n hn => ?_⟩
  obtain ⟨i, j₀, hij⟩ := erdos_414_conjecture 1 n (by omega) hn
  refine ⟨j₀, fun k hk => ⟨i + (k - j₀), ?_⟩⟩
  conv_lhs => rw [show k = j₀ + (k - j₀) by omega]
  rw [hOrbit_compose n j₀, ← hij, ← hOrbit_compose]

/- ## Orbit Examples -/

/-- Orbit of 1: 1 → 2 → 4 → 7 → 9 → 12 → 18 → 24 → 32 → ... -/
theorem orbit_1_start :
    hOrbit 1 0 = 1 ∧ hOrbit 1 1 = 2 ∧ hOrbit 1 2 = 4 ∧
    hOrbit 1 3 = 7 ∧ hOrbit 1 4 = 9 := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> native_decide

/-- Orbit of 3: 3 → 5 → 7 → 9 → 12 → 18 → 24 → 32 → ...
    Merges with orbit of 1 at value 7 (h_3(1) = h_1(3) = 7). -/
theorem orbit_3_merges_with_1 :
    hOrbit 3 2 = hOrbit 1 3 := by  -- both equal 7
  native_decide

/- ## Growth Rate Analysis -/

/-- On average, τ(n) ~ log n (Dirichlet's theorem on average order).
    So h(n) ≈ n + log n, and after k iterations,
    h^k(n) ≈ n + k · log n (roughly). -/
theorem average_divisor_count :
    True :=  -- Σ_{n≤N} τ(n) ~ N log N (Dirichlet)
  trivial

/-- The orbit grows at least linearly: h^k(n) ≥ n + k for n ≥ 1.
    Proved by induction using h(m) > m for m ≥ 1. -/
theorem orbit_linear_lower (n : ℕ) (hn : n ≥ 1) (k : ℕ) :
    hOrbit n k ≥ n + k := by
  induction k with
  | zero => simp [hOrbit]
  | succ k ih =>
    simp [hOrbit]
    have hpos := hOrbit_pos n hn k
    have hgt := h_strictly_increasing (hOrbit n k) hpos
    omega

/-- Two orbits eventually merge exactly, so in particular they get
    within any positive distance D. Derived from the main conjecture. -/
theorem orbits_get_close (m n : ℕ) (hm : m ≥ 1) (hn : n ≥ 1)
    (D : ℕ) (hD : D ≥ 1) :
    ∃ i j : ℕ,
      (hOrbit m i : ℤ) - (hOrbit n j : ℤ) < D ∧
      (hOrbit n j : ℤ) - (hOrbit m i : ℤ) < D := by
  obtain ⟨i, j, hij⟩ := erdos_414_conjecture m n hm hn
  exact ⟨i, j, by simp [show (hOrbit m i : ℤ) = hOrbit n j from by exact_mod_cast hij]; omega⟩
