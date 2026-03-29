/-
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
import Mathlib.Data.Set.Card
import Mathlib.Tactic

/- ## Core Definitions -/

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

/- ## Erdős–Turán Conjecture (Problem #28) -/

-- **Erdős–Turán Conjecture** (Problem #28, OPEN):
-- Every additive basis of order 2 has unbounded representation function.
-- Stated as a hypothesis where needed (not as a global axiom).

/- ## Problem #40: Strengthened Form -/

/-- A set A has density at least N^{1/2}/g(N). -/
def HasDensity (A : Set ℕ) (g : ℕ → ℝ) : Prop :=
  ∃ c : ℝ, c > 0 ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N > N₀ →
    (countingFn A N : ℝ) ≥ c * Real.sqrt N / g N

-- **Erdős Problem #40** (OPEN, $500): For which g(N) → ∞ does
-- |A ∩ {1,...,N}| >> N^{1/2}/g(N) imply limsup r_A(n) = ∞?
-- The strongest form asks: does this hold for ALL g → ∞?
-- Stated as a hypothesis where needed (not as a global axiom).

/- ## Proving #40 ⟹ #28 -/

/-- The representation set for n is finite (bounded by [0,n]²). -/
private lemma rep_set_finite (A : Set ℕ) (n : ℕ) :
    {p : ℕ × ℕ | p.1 ∈ A ∧ p.2 ∈ A ∧ p.1 ≤ p.2 ∧ p.1 + p.2 = n}.Finite := by
  apply (Set.Finite.prod (Set.finite_Icc 0 n) (Set.finite_Icc 0 n)).subset
  rintro ⟨a, b⟩ ⟨-, -, -, hab⟩
  exact ⟨Set.mem_Icc.mpr ⟨by omega, by omega⟩, Set.mem_Icc.mpr ⟨by omega, by omega⟩⟩

/-- From a positive representation count, extract a witness in {1,...,n}. -/
private lemma basis_has_element {A : Set ℕ} {n : ℕ} (hn : 1 ≤ n)
    (hrep : repCount A n ≥ 1) : ∃ b ∈ A, 1 ≤ b ∧ b ≤ n := by
  unfold repCount at hrep
  obtain ⟨⟨a, b⟩, -, hbA, -, hsum⟩ :=
    (Set.ncard_pos (rep_set_finite A n)).mp (by omega)
  exact ⟨b, hbA, by omega, by omega⟩

/-- If a ∈ A ∩ {1,...,N}, then countingFn A N ≥ 1. -/
private lemma countingFn_pos {A : Set ℕ} {a N : ℕ}
    (ha : a ∈ A) (ha1 : 1 ≤ a) (haN : a ≤ N) : 1 ≤ countingFn A N := by
  unfold countingFn
  have hfin : (A ∩ Set.Icc 1 N).Finite :=
    (Set.finite_Icc 1 N).subset Set.inter_subset_right
  have := (Set.ncard_pos hfin).mpr
    ⟨a, Set.mem_inter ha (Set.mem_Icc.mpr ⟨ha1, haN⟩)⟩
  omega

/-- **PROVED**: Problem #40 (for any g → ∞) implies Problem #28.
    Proof: take g(N) = N. Any basis has countingFn ≥ 1 for large N,
    and 1 ≥ √N/N, so the density condition is trivially satisfied. -/
theorem problem_40_implies_28
    (h40 : ∀ (g : ℕ → ℝ), (∀ M : ℝ, ∃ N₀ : ℕ, ∀ N : ℕ, N > N₀ → g N > M) →
      ∀ A : Set ℕ, HasDensity A g → RepUnbounded A) :
  ∀ A : Set ℕ, IsAdditiveBasis2 A → RepUnbounded A := by
  intro A ⟨N₀, hbasis⟩
  obtain ⟨a₀, ha₀A, ha₀_ge1, ha₀_le⟩ := basis_has_element
    (le_max_right N₀ 1) (hbasis _ (le_max_left N₀ 1))
  apply h40 (fun N => (N : ℝ))
  · -- g(N) = N → ∞ (Archimedean property)
    intro M
    obtain ⟨n, hn⟩ := exists_nat_gt M
    exact ⟨n, fun N hN => lt_trans hn (by exact_mod_cast hN)⟩
  · -- HasDensity A (fun N => ↑N)
    refine ⟨1, one_pos, max N₀ 1, fun N hN => ?_⟩
    simp only [one_mul]
    have hN_pos : (0 : ℝ) < ↑N := by positivity
    have hcf : (1 : ℝ) ≤ ↑(countingFn A N) := by
      exact_mod_cast countingFn_pos ha₀A ha₀_ge1 (by omega)
    have hsqrt_le : Real.sqrt ↑N ≤ ↑N := by
      nlinarith [Real.mul_self_sqrt (show (0 : ℝ) ≤ ↑N from by positivity),
                 Real.sqrt_nonneg (↑N : ℝ),
                 mul_self_nonneg (Real.sqrt ↑N - 1),
                 show (1 : ℝ) ≤ ↑N from by exact_mod_cast (show 1 ≤ N from by omega)]
    linarith [(div_le_one hN_pos).mpr hsqrt_le]

/- ## Known Partial Results -/

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

/- ## Proved Properties -/

/-- If representation is unbounded, then for every bound M there exists n
    with at least M representations. (Definition unfolding.) -/
theorem repUnbounded_iff (A : Set ℕ) :
    RepUnbounded A ↔ ∀ M : ℕ, ∃ n : ℕ, repCount A n ≥ M :=
  Iff.rfl

/-- If repCount is bounded by some constant B for all n, then A is NOT
    RepUnbounded. Contrapositive of unboundedness. -/
theorem bounded_rep_not_unbounded (A : Set ℕ) (B : ℕ) (hB : ∀ n, repCount A n ≤ B) :
    ¬RepUnbounded A := by
  intro h
  obtain ⟨n, hn⟩ := h (B + 1)
  have := hB n
  omega

/-- An additive basis of order 2 represents every large n at least once.
    (Definition unfolding.) -/
theorem basis2_iff (A : Set ℕ) :
    IsAdditiveBasis2 A ↔ ∃ N₀, ∀ n, n ≥ N₀ → repCount A n ≥ 1 :=
  Iff.rfl

/- ## Probabilistic Heuristic -/

-- Probabilistic heuristic: a random set A ⊆ {1,...,N} with |A| ~ N^{1/2}/g(N)
-- has E[r_A(n)] ~ |A|²/N ~ 1/g(N)² for typical n.
-- If g(N) → ∞, E → 0, so most n have r_A(n) = 0.
-- But fluctuations may produce occasional large values.
-- Critical threshold conjecture: g(N) = (log N)^{1/2+ε} should suffice.
