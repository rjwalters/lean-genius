/-
  Erdős Problem #28: Erdős-Turán Conjecture on Additive Bases

  Source: https://erdosproblems.com/28
  Status: OPEN
  Prize: $500

  Statement:
  If A ⊆ ℕ is such that A + A contains all but finitely many integers,
  then lim sup r_A(n) = ∞, where r_A(n) = |{(a,b) ∈ A×A : a + b = n}|.

  Key Definition:
  The **representation function** r_A(n) counts the number of ways to write n
  as a sum of two elements from set A.

  Stronger Conjectures:
  1. lim sup r_A(n) / log(n) > 0  (Erdős-Turán 1941)
  2. The hypothesis |A ∩ [1,N]| >> N^{1/2} suffices

  Known Results:
  - Grekos et al. (2003): r_A(n) ≥ 6 for infinitely many n
  - Borwein et al.: r_A(n) ≥ 8 for infinitely many n
  - There exist bases with bounded representations (Sidon-type constructions don't apply here)

  What We Can Do:
  1. Define representation function r_A(n)
  2. Define asymptotic basis (A+A contains all large n)
  3. State the conjecture formally
  4. Prove basic properties
  5. Exhibit constructions with unbounded representations

  Tags: number-theory, additive-combinatorics, erdos-problem, prize-problem
-/

import Mathlib.Data.Nat.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Set.Card
import Mathlib.Order.Filter.Basic
import Mathlib.Tactic

namespace Erdos28

open Finset Filter

/-! ## Part I: Representation Function -/

/-- The representation function r_A(n): counts pairs (a,b) ∈ A×A with a + b = n.
    We count ordered pairs, so r_A(n) counts each representation {a,b} twice if a ≠ b,
    and once if a = b. -/
noncomputable def repFunc (A : Set ℕ) (n : ℕ) : ℕ :=
  Set.ncard {p : ℕ × ℕ | p.1 ∈ A ∧ p.2 ∈ A ∧ p.1 + p.2 = n}

/-- Alternative: unordered representation count (pairs with a ≤ b). -/
noncomputable def repFuncUnordered (A : Set ℕ) (n : ℕ) : ℕ :=
  Set.ncard {p : ℕ × ℕ | p.1 ∈ A ∧ p.2 ∈ A ∧ p.1 ≤ p.2 ∧ p.1 + p.2 = n}

/-- For finite sets, we can use Finset cardinality. -/
def repFuncFinset (A : Finset ℕ) (n : ℕ) : ℕ :=
  (A.product A).filter (fun p => p.1 + p.2 = n) |>.card

/-! ## Part II: Sumset and Asymptotic Basis -/

/-- The sumset A + A = {a + b : a, b ∈ A}. -/
def sumset (A : Set ℕ) : Set ℕ :=
  {n | ∃ a b, a ∈ A ∧ b ∈ A ∧ n = a + b}

/-- A is an asymptotic additive basis of order 2 if A+A contains all sufficiently large integers. -/
def IsAsymptoticBasis (A : Set ℕ) : Prop :=
  ∃ N₀ : ℕ, ∀ n ≥ N₀, n ∈ sumset A

/-- Equivalent: A+A misses only finitely many integers. -/
def IsAsymptoticBasis' (A : Set ℕ) : Prop :=
  (sumset A)ᶜ.Finite

/-- The two definitions are equivalent.
    Proof sketch: If A+A contains [N₀, ∞), the complement is ⊆ {0,...,N₀-1}, hence finite.
    Conversely, if the complement is finite, it has a maximum M, so [M+1, ∞) ⊆ A+A. -/
theorem isAsymptoticBasis_iff (A : Set ℕ) :
    IsAsymptoticBasis A ↔ IsAsymptoticBasis' A := by
  constructor
  · intro ⟨N₀, h⟩
    unfold IsAsymptoticBasis'
    have hsub : (sumset A)ᶜ ⊆ Finset.range N₀ := fun n hn => by
      simp only [Set.mem_compl_iff] at hn
      simp only [Finset.coe_range, Set.mem_Iio]
      by_contra h'
      push_neg at h'
      exact hn (h n h')
    exact Set.Finite.subset (Finset.finite_toSet _) hsub
  · intro hfin
    -- The complement is finite, hence bounded, so has a maximum.
    -- All n beyond that maximum are in A+A.
    sorry

/-! ## Part III: Basic Properties -/

/-- If n ∈ A+A then r_A(n) ≥ 1. -/
theorem repFunc_pos_of_mem_sumset (A : Set ℕ) (n : ℕ) (h : n ∈ sumset A) :
    repFunc A n ≥ 1 := by
  -- There exists at least one pair (a,b) with a + b = n
  -- so the representation count is at least 1
  sorry

/-- If A is infinite and 0 ∈ A, then r_A(n) ≥ 1 for all n ∈ A. -/
theorem repFunc_pos_of_zero_mem (A : Set ℕ) (h0 : 0 ∈ A) (n : ℕ) (hn : n ∈ A) :
    repFunc A n ≥ 1 := by
  apply repFunc_pos_of_mem_sumset
  exact ⟨0, n, h0, hn, by ring⟩

/-- For Sidon sets, r_A(n) ≤ 2 for all n. -/
def IsSidon (A : Set ℕ) : Prop :=
  ∀ a b c d, a ∈ A → b ∈ A → c ∈ A → d ∈ A →
    a + b = c + d → ({a, b} : Set ℕ) = {c, d}

/-- Sidon sets have bounded representation. -/
theorem sidon_repFunc_bounded (A : Set ℕ) (hS : IsSidon A) :
    ∀ n, repFunc A n ≤ 2 := by
  intro n
  -- For Sidon sets, if a + b = c + d then {a,b} = {c,d}
  -- So there's at most one unordered pair summing to n
  -- Ordered pairs: at most 2 (the pair and its reversal, or 1 if a = b)
  sorry

/-! ## Part IV: The Main Conjecture -/

/-- **Erdős-Turán Conjecture** (Weak Form, 1941)

    If A is an asymptotic basis of order 2, then the representation function
    is unbounded: lim sup r_A(n) = ∞.

    Equivalently: for every k, there exists n with r_A(n) > k. -/
def erdos_turan_weak : Prop :=
  ∀ A : Set ℕ, IsAsymptoticBasis A → ∀ k : ℕ, ∃ n : ℕ, repFunc A n > k

/-- **Erdős-Turán Conjecture** (Strong Form)

    If A is an asymptotic basis of order 2, then
    lim sup r_A(n) / log(n) > 0. -/
def erdos_turan_strong : Prop :=
  ∀ A : Set ℕ, IsAsymptoticBasis A →
    ∃ c : ℝ, c > 0 ∧ ∀ M : ℕ, ∃ n > M, repFunc A n > c * Real.log n

/-- **Erdős Problem #28** (Official Statement)

    Prize: $500 for proof or disproof. -/
def erdos_28 : Prop := erdos_turan_weak

/-! ## Part V: Known Partial Results -/

/-- Grekos et al. (2003): For any asymptotic basis A, r_A(n) ≥ 6 for infinitely many n. -/
axiom grekos_lower_bound :
  ∀ A : Set ℕ, IsAsymptoticBasis A → ∀ M : ℕ, ∃ n > M, repFunc A n ≥ 6

/-- Borwein et al.: Improved to r_A(n) ≥ 8 infinitely often. -/
axiom borwein_lower_bound :
  ∀ A : Set ℕ, IsAsymptoticBasis A → ∀ M : ℕ, ∃ n > M, repFunc A n ≥ 8

/-! ## Part VI: Examples -/

/-- The even numbers {0, 2, 4, 6, ...} form a basis for even numbers. -/
def evens : Set ℕ := {n | Even n}

/-- Every even number is in evens + evens. -/
theorem evens_sumset : sumset evens = evens := by
  ext n
  constructor
  · intro ⟨a, b, ha, hb, heq⟩
    obtain ⟨ka, hka⟩ := ha
    obtain ⟨kb, hkb⟩ := hb
    use ka + kb
    omega
  · intro hn_even
    -- n = 0 + n, where 0 ∈ evens and n ∈ evens
    refine ⟨0, n, ?_, hn_even, ?_⟩
    · exact ⟨0, rfl⟩
    · ring

/-- For evens, r_{evens}(2n) = n + 1 for n ≥ 0.
    Pairs: (0,2n), (2,2n-2), ..., (2n,0). -/
theorem evens_repFunc (n : ℕ) : repFuncUnordered evens (2*n) = n + 1 := by
  -- The pairs are (2k, 2(n-k)) for k = 0, 1, ..., n
  sorry

/-- The natural numbers ℕ form a basis (trivially). -/
theorem nat_is_basis : IsAsymptoticBasis (Set.univ : Set ℕ) := by
  use 0
  intro n _
  exact ⟨0, n, trivial, trivial, by ring⟩

/-- For ℕ, r_ℕ(n) = n + 1 (pairs (0,n), (1,n-1), ..., (n,0)). -/
theorem nat_repFunc (n : ℕ) : repFuncUnordered (Set.univ : Set ℕ) n = n / 2 + 1 := by
  sorry

/-! ## Part VII: Connection to Sidon Sets -/

/-- Sidon sets (B₂ sequences) are NOT asymptotic bases.
    This shows the conjecture is not trivially false. -/
theorem sidon_not_basis (A : Set ℕ) (hS : IsSidon A) (hInf : A.Infinite) :
    ¬IsAsymptoticBasis A := by
  -- Sidon sets have density at most N^{1/2}, so A+A has density at most N
  -- which means A+A cannot contain all large integers
  sorry

#check erdos_28
#check erdos_turan_weak
#check erdos_turan_strong

end Erdos28
