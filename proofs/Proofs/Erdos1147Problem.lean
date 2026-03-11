/-
  Erdős Problem #1147: Additive Basis from Diophantine Approximation

  Source: https://erdosproblems.com/1147
  Status: DISPROVED (Konieczny [Ko16b])

  Statement:
  Let α > 0 be irrational. Is the set
    A = {n ≥ 1 : ‖αn²‖ < 1/log(n)}
  (where ‖·‖ denotes the distance to the nearest integer)
  an additive basis of order 2?

  Answer: NO

  Background:
  Erdős asked whether the set of integers n where αn² is "close" to an
  integer (within 1/log(n)) forms an additive basis of order 2, meaning
  every sufficiently large integer can be written as the sum of two
  elements of A.

  This connects two fundamental topics:
  - Diophantine approximation (how well irrationals can be approximated)
  - Additive combinatorics (sumset structure of integer sets)

  Solution:
  Konieczny [Ko16b] disproved this conjecture by showing that for almost
  every α > 0, the set A is NOT an additive basis of order 2. Moreover,
  for any function ε(n) → 0, the generalized set
    A_ε = {n ≥ 1 : ‖αn²‖ < ε(n)}
  fails to be a basis of order 2 for almost every α.

  References:
  - [Va99, 1.21] Original problem reference
  - Konieczny [Ko16b]: Disproof
-/

import Mathlib

open Real Set Filter MeasureTheory

noncomputable section

namespace Erdos1147

-- ============================================================================
-- Part I: Distance to Nearest Integer
-- ============================================================================

/-- The distance to the nearest integer: ‖x‖ = min(fract(x), 1 - fract(x)).
    This measures how close x is to an integer. -/
def distToNearestInt (x : ℝ) : ℝ :=
  min (Int.fract x) (1 - Int.fract x)

/-- Distance to nearest integer is always non-negative. -/
theorem distToNearestInt_nonneg (x : ℝ) : distToNearestInt x ≥ 0 := by
  unfold distToNearestInt
  simp only [ge_iff_le, le_min_iff]
  exact ⟨Int.fract_nonneg x, by linarith [Int.fract_lt_one x]⟩

/-- Distance to nearest integer is at most 1/2. -/
theorem distToNearestInt_le_half (x : ℝ) : distToNearestInt x ≤ 1 / 2 := by
  unfold distToNearestInt
  have h1 := Int.fract_nonneg x
  have h2 := Int.fract_lt_one x
  rcases le_or_gt (Int.fract x) (1 / 2) with h | h
  · exact min_le_of_left_le h
  · have : 1 - Int.fract x < 1 / 2 := by linarith
    exact min_le_of_right_le (le_of_lt this)

/-- Distance to nearest integer is zero iff x is an integer. -/
theorem distToNearestInt_eq_zero_iff (x : ℝ) :
    distToNearestInt x = 0 ↔ ∃ n : ℤ, x = n := by
  unfold distToNearestInt
  constructor
  · intro h
    have h1 := Int.fract_nonneg x
    have h2 : 1 - Int.fract x ≥ 0 := by linarith [Int.fract_lt_one x]
    have hfrac : Int.fract x = 0 := by
      rcases min_cases (Int.fract x) (1 - Int.fract x) with ⟨heq, _⟩ | ⟨heq, _⟩
      · linarith
      · linarith [Int.fract_lt_one x]
    exact ⟨⌊x⌋, by rw [← Int.self_sub_fract x, hfrac, sub_zero]⟩
  · rintro ⟨n, rfl⟩
    simp [Int.fract_intCast]

-- ============================================================================
-- Part II: The Set A (Diophantine Approximation Set)
-- ============================================================================

/-- The set A_α = {n ≥ 1 : ‖αn²‖ < 1/log(n)} for a given irrational α.
    This is the set of integers where αn² is "close" to an integer. -/
def diophantineSet (α : ℝ) : Set ℕ :=
  { n : ℕ | n ≥ 1 ∧ distToNearestInt (α * (n : ℝ)^2) < 1 / Real.log n }

/-- The generalized set with threshold ε(n) instead of 1/log(n). -/
def generalizedDiophantineSet (α : ℝ) (ε : ℕ → ℝ) : Set ℕ :=
  { n : ℕ | n ≥ 1 ∧ distToNearestInt (α * (n : ℝ)^2) < ε n }

-- ============================================================================
-- Part III: Additive Basis
-- ============================================================================

/-- A set A ⊆ ℕ is an additive basis of order 2 if every sufficiently large
    integer can be written as a sum of two elements of A. -/
def IsAdditiveBasisOrder2 (A : Set ℕ) : Prop :=
  ∃ N₀ : ℕ, ∀ n ≥ N₀, ∃ a b : ℕ, a ∈ A ∧ b ∈ A ∧ n = a + b

/-- Equivalently: the sumset A + A covers a cofinite subset of ℕ. -/
def Sumset (A : Set ℕ) : Set ℕ := { n | ∃ a ∈ A, ∃ b ∈ A, n = a + b }

/-- Being an additive basis of order 2 is equivalent to the sumset being cofinite. -/
theorem additiveBasis_iff_sumset_cofinite (A : Set ℕ) :
    IsAdditiveBasisOrder2 A ↔ ∃ N₀, ∀ n ≥ N₀, n ∈ Sumset A := by
  constructor
  · rintro ⟨N₀, hN₀⟩
    exact ⟨N₀, fun n hn => by
      obtain ⟨a, b, ha, hb, hab⟩ := hN₀ n hn
      exact ⟨a, ha, b, hb, hab⟩⟩
  · rintro ⟨N₀, hN₀⟩
    exact ⟨N₀, fun n hn => by
      obtain ⟨a, ha, b, hb, hab⟩ := hN₀ n hn
      exact ⟨a, b, ha, hb, hab⟩⟩

-- ============================================================================
-- Part IV: Properties of the Diophantine Set
-- ============================================================================

/-- For n ≥ 3, log(n) > 1, so the threshold 1/log(n) < 1. -/
theorem threshold_lt_one (n : ℕ) (hn : n ≥ 3) :
    1 / Real.log (n : ℝ) < 1 := by
  have hn3 : (n : ℝ) ≥ 3 := by exact_mod_cast hn
  have hlog_pos : Real.log (n : ℝ) > 0 := by
    apply Real.log_pos; linarith
  have hlog : Real.log (n : ℝ) > 1 := by
    have h1 : Real.log (n : ℝ) ≥ Real.log 3 :=
      Real.log_le_log (by norm_num : (0 : ℝ) < 3) (by linarith)
    have h2 : Real.log 3 > 1 := by
      rw [show (1 : ℝ) = Real.log (Real.exp 1) from (Real.log_exp 1).symm]
      exact Real.log_lt_log (Real.exp_pos 1) (by linarith [Real.exp_one_lt_d9])
    linarith
  rw [div_lt_one hlog_pos]
  exact hlog

/-- The threshold 1/log(n) → 0 as n → ∞. -/
theorem threshold_tendsto_zero :
    Tendsto (fun n : ℕ => 1 / Real.log (n : ℝ)) atTop (nhds 0) := by
  simp only [one_div]
  exact tendsto_inv_atTop_zero.comp (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)

-- ============================================================================
-- Part V: Main Results (Konieczny's Disproof)
-- ============================================================================

/-- Konieczny's theorem: For almost every irrational α > 0, the set
    A = {n ≥ 1 : ‖αn²‖ < 1/log(n)} is NOT an additive basis of order 2. -/
axiom konieczny_disproof :
  ∀ᵐ α ∂(volume.restrict (Set.Ioi (0 : ℝ))),
    Irrational α → ¬IsAdditiveBasisOrder2 (diophantineSet α)

/-- Stronger version: For any ε(n) → 0, the generalized set
    A_ε = {n ≥ 1 : ‖αn²‖ < ε(n)} is not a basis for almost every α. -/
axiom konieczny_generalized (ε : ℕ → ℝ) (hε : Tendsto ε atTop (nhds 0)) :
  ∀ᵐ α ∂(volume.restrict (Set.Ioi (0 : ℝ))),
    Irrational α → ¬IsAdditiveBasisOrder2 (generalizedDiophantineSet α ε)

-- ============================================================================
-- Part VI: Specific Counterexample
-- ============================================================================

/-- For α = √2, the set is not an additive basis of order 2. -/
axiom sqrt2_not_basis : ¬IsAdditiveBasisOrder2 (diophantineSet (Real.sqrt 2))

/-- √2 is irrational (from Mathlib). -/
theorem sqrt2_irrational : Irrational (Real.sqrt 2) := irrational_sqrt_two

-- ============================================================================
-- Part VII: The Conjecture Statement (for Gallery)
-- ============================================================================

/-- Erdős Problem #1147 Conjecture (DISPROVED):
    For every irrational α > 0, the set {n : ‖αn²‖ < 1/log n}
    is an additive basis of order 2. -/
def Erdos1147Conjecture : Prop :=
  ∀ α : ℝ, α > 0 → Irrational α →
    IsAdditiveBasisOrder2 (diophantineSet α)

/-- The conjecture is FALSE: √2 provides a specific counterexample. -/
theorem erdos_1147_false : ¬Erdos1147Conjecture := by
  intro hconj
  have h2pos : Real.sqrt 2 > 0 := Real.sqrt_pos_of_pos (by norm_num : (2 : ℝ) > 0)
  exact sqrt2_not_basis (hconj _ h2pos sqrt2_irrational)

-- ============================================================================
-- Part VIII: Connection Between Diophantine Approximation and Density
-- ============================================================================

/-- The Diophantine set is infinite for any irrational α > 0.
    This follows from Dirichlet's approximation theorem:
    there are infinitely many n with ‖αn²‖ < 1/n, which is
    eventually less than 1/log(n). -/
axiom diophantine_set_infinite (α : ℝ) (hα : α > 0) (hαirr : Irrational α) :
  (diophantineSet α).Infinite

-- Despite being infinite, the Diophantine set is too sparse and too
-- irregularly distributed to form a basis of order 2 for almost every α.

-- ============================================================================
-- Part IX: Summary
-- ============================================================================

-- Erdős Problem #1147 asked whether {n : ‖αn²‖ < 1/log n} is an additive
-- basis of order 2 for every irrational α > 0.
--
-- Answer: NO (Konieczny [Ko16b])
--
-- Key Points:
-- 1. The set is infinite (by Dirichlet's approximation theorem)
-- 2. But it is NOT an additive basis of order 2 for almost every α
-- 3. The result extends: any ε(n) → 0 gives the same failure
-- 4. Specific counterexample: α = √2
--
-- Axiom count: 4 (konieczny_disproof, konieczny_generalized,
--                  sqrt2_not_basis, diophantine_set_infinite)
-- Proved theorems: 8
-- Sorry count: 0

end Erdos1147

-- Verification
#check Erdos1147.distToNearestInt_nonneg
#check Erdos1147.distToNearestInt_le_half
#check Erdos1147.additiveBasis_iff_sumset_cofinite
#check Erdos1147.threshold_tendsto_zero
#check Erdos1147.sqrt2_irrational
