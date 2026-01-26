/-!
# Erdős Problem #40: Representation Function and Dense Sets

For which functions g(N) → ∞ is it true that
|A ∩ {1,...,N}| >> N^{1/2} / g(N) implies limsup r_A(n) = ∞,
where r_A(n) = |{(a,b) ∈ A² : a + b = n}| counts sum representations?

## Key Results

- This strengthens the Erdős–Turán conjecture (Problem #28):
  every additive basis of order 2 has unbounded representation function
- Solving for ANY g(N) → ∞ implies Problem #28
- $500 bounty

## References

- Erdős [Er95], [Er97c]
- Related: Problem #28 (Erdős–Turán conjecture)
- <https://erdosproblems.com/40>
-/

import Mathlib.Data.Nat.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Set.Basic
import Mathlib.Tactic

/-! ## Core Definitions -/

/-- The representation count r_A(n): number of ways to write n = a + b
    with a, b ∈ A and a ≤ b. -/
noncomputable def repCount (A : Set ℕ) (n : ℕ) : ℕ :=
  Set.ncard {p : ℕ × ℕ | p.1 ∈ A ∧ p.2 ∈ A ∧ p.1 ≤ p.2 ∧ p.1 + p.2 = n}

/-- The counting function: |A ∩ {1,...,N}|. -/
noncomputable def countingFn (A : Set ℕ) (N : ℕ) : ℕ :=
  Set.ncard (A ∩ Set.Icc 1 N)

/-- A is an additive basis of order 2: every sufficiently large n
    is a sum of two elements of A. -/
def IsAdditiveBasis2 (A : Set ℕ) : Prop :=
  ∃ N₀ : ℕ, ∀ n : ℕ, n ≥ N₀ → repCount A n ≥ 1

/-- The representation function is unbounded: limsup r_A(n) = ∞. -/
def RepUnbounded (A : Set ℕ) : Prop :=
  ∀ M : ℕ, ∃ n : ℕ, repCount A n ≥ M

/-! ## Erdős–Turán Conjecture (Problem #28) -/

/-- **Erdős–Turán Conjecture** (Problem #28, OPEN):
    Every additive basis of order 2 has unbounded representation function. -/
axiom erdos_turan_conjecture :
  ∀ A : Set ℕ, IsAdditiveBasis2 A → RepUnbounded A

/-! ## Problem #40: Strengthened Form -/

/-- A set A has density at least N^{1/2}/g(N). -/
def HasDensity (A : Set ℕ) (g : ℕ → ℝ) : Prop :=
  ∃ c : ℝ, c > 0 ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N > N₀ →
    (countingFn A N : ℝ) ≥ c * Real.sqrt N / g N

/-- **Erdős Problem #40** (OPEN, $500): For which g(N) → ∞ does
    |A ∩ {1,...,N}| >> N^{1/2}/g(N) imply limsup r_A(n) = ∞?
    The strongest form asks: does this hold for ALL g → ∞? -/
axiom erdos_40_conjecture :
  ∀ (g : ℕ → ℝ), (∀ M : ℝ, ∃ N₀ : ℕ, ∀ N : ℕ, N > N₀ → g N > M) →
    ∀ A : Set ℕ, HasDensity A g → RepUnbounded A

/-! ## Connection to Problem #28 -/

/-- Problem #40 (for any g → ∞) implies Problem #28:
    An additive basis of order 2 has |A ∩ {1,...,N}| >> N^{1/2}
    (or more), so taking g(N) = N^{1/2} suffices. -/
axiom problem_40_implies_28
    (h40 : ∀ (g : ℕ → ℝ), (∀ M : ℝ, ∃ N₀ : ℕ, ∀ N : ℕ, N > N₀ → g N > M) →
      ∀ A : Set ℕ, HasDensity A g → RepUnbounded A) :
  ∀ A : Set ℕ, IsAdditiveBasis2 A → RepUnbounded A

/-! ## Known Partial Results -/

/-- For Sidon sets (r_A(n) ≤ 1 for all n), we have
    |A ∩ {1,...,N}| ≤ (1+o(1))N^{1/2}. So the N^{1/2} threshold
    is natural: Sidon sets are exactly at this density. -/
axiom sidon_density_bound :
  ∀ A : Set ℕ, (∀ n : ℕ, repCount A n ≤ 1) →
    ∀ ε : ℝ, ε > 0 → ∃ N₀ : ℕ, ∀ N : ℕ, N > N₀ →
      (countingFn A N : ℝ) ≤ (1 + ε) * Real.sqrt N

/-- For B₂[g] sets (r_A(n) ≤ g for all n), the density is
    bounded by |A ∩ {1,...,N}| ≤ c·N^{1/2} for a constant
    depending on g. -/
axiom b2g_density_bound (g : ℕ) :
  ∃ c : ℝ, c > 0 ∧ ∀ A : Set ℕ, (∀ n : ℕ, repCount A n ≤ g) →
    ∀ N : ℕ, N ≥ 1 → (countingFn A N : ℝ) ≤ c * Real.sqrt N

/-! ## Probabilistic Heuristic -/

/-- Heuristic: a random set A ⊆ {1,...,N} with |A| ~ N^{1/2}/g(N)
    has expected representation count
    E[r_A(n)] ~ |A|²/N ~ 1/g(N)² for typical n.
    If g(N) → ∞, this goes to 0, so most n have r_A(n) = 0.
    But fluctuations may produce occasional large values. -/
axiom random_heuristic :
  True  -- Random models suggest the answer depends on g's growth rate

/-- The critical threshold: if g(N) = (log N)^{1/2+ε} the conjecture
    is expected to hold; if g(N) grows polynomially it may fail. -/
axiom threshold_heuristic :
  True  -- The exact threshold function is unknown
