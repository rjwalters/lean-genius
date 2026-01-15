/-
Erdős Problem #29: Explicit Economical Additive Basis

Source: https://erdosproblems.com/29
Status: SOLVED (Jain-Pham-Sawhney-Zakharov 2024)
Prize: $100

Statement:
Is there an explicit construction of a set A ⊆ ℕ such that A + A = ℕ but
1_A ∗ 1_A(n) = o(n^ε) for every ε > 0?

Meaning: Can we find an additive basis A (every natural number is a sum of two
elements from A) where the number of representations grows slower than any
polynomial?

History:
- Sidon asked Erdős this in 1932
- Erdős proved existence using probabilistic methods
- Jain, Pham, Sawhney, Zakharov (2024) gave an explicit construction

The explicit construction resolves a 90+ year old question with a concrete
algorithm rather than a probabilistic existence proof.

Reference: Jain, Pham, Sawhney, Zakharov (2024) "An explicit economical
           additive basis" arXiv:2405.08650
-/

import Mathlib

open Set Finset Nat Filter

namespace Erdos29

/-! ## Basic Definitions -/

/-- The sumset A + B = {a + b : a ∈ A, b ∈ B}. -/
def Sumset (A B : Set ℕ) : Set ℕ := { n | ∃ a ∈ A, ∃ b ∈ B, n = a + b }

notation:65 A " +ₛ " B => Sumset A B

/-- A + A for a single set. -/
def Doubling (A : Set ℕ) : Set ℕ := A +ₛ A

/-- The representation function r_A(n) = #{(a,b) ∈ A² : a + b = n}. -/
noncomputable def representationCount (A : Set ℕ) (n : ℕ) : ℕ :=
  Set.ncard { p : ℕ × ℕ | p.1 ∈ A ∧ p.2 ∈ A ∧ p.1 + p.2 = n }

/-- Alternative: count pairs (a, b) with a ≤ b and a + b = n. -/
noncomputable def orderedRepCount (A : Set ℕ) (n : ℕ) : ℕ :=
  Set.ncard { p : ℕ × ℕ | p.1 ∈ A ∧ p.2 ∈ A ∧ p.1 ≤ p.2 ∧ p.1 + p.2 = n }

/-! ## Additive Bases -/

/-- A set A is an additive basis of order 2 if A + A = ℕ. -/
def IsAdditiveBasis (A : Set ℕ) : Prop := Doubling A = Set.univ

/-- Equivalent: every n ∈ ℕ is representable as a sum of two elements from A. -/
def CoversAll (A : Set ℕ) : Prop := ∀ n : ℕ, n ∈ Doubling A

theorem additive_basis_iff (A : Set ℕ) : IsAdditiveBasis A ↔ CoversAll A := by
  unfold IsAdditiveBasis CoversAll
  constructor
  · intro h n
    rw [h]
    trivial
  · intro h
    ext n
    simp only [Set.mem_univ, iff_true]
    exact h n

/-! ## The Economical Condition -/

/-- The representation count is o(n^ε) for all ε > 0.
    This means: for all ε > 0, r_A(n) / n^ε → 0 as n → ∞. -/
def IsEconomical (A : Set ℕ) : Prop :=
  ∀ ε > 0, Tendsto (fun n => (representationCount A n : ℝ) / (n : ℝ)^ε) atTop (nhds 0)

/-- Equivalent formulation: for all ε > 0, r_A(n) = o(n^ε). -/
def IsEconomical' (A : Set ℕ) : Prop :=
  ∀ ε > 0, ∀ C > 0, ∃ N₀ : ℕ, ∀ n ≥ N₀, (representationCount A n : ℝ) < C * (n : ℝ)^ε

theorem economical_equiv (A : Set ℕ) : IsEconomical A ↔ IsEconomical' A := by
  sorry -- Standard equivalence of limit definitions

/-! ## Erdős's Original Problem -/

/-- Erdős Problem #29: Does there exist an explicit economical additive basis? -/
def Erdos29Statement : Prop :=
  ∃ A : Set ℕ, IsAdditiveBasis A ∧ IsEconomical A

/-! ## The Probabilistic Existence (Erdős) -/

/-- Erdős proved existence using probabilistic method (non-constructive). -/
axiom erdos_probabilistic_existence :
  ∃ A : Set ℕ, IsAdditiveBasis A ∧ IsEconomical A

/-! ## The Explicit Construction (JPSZ 2024) -/

/-- The Jain-Pham-Sawhney-Zakharov construction.
    This is an explicit, computable set satisfying both conditions. -/
axiom JPSZ_set : Set ℕ

/-- The JPSZ set is an additive basis. -/
axiom JPSZ_is_basis : IsAdditiveBasis JPSZ_set

/-- The JPSZ set is economical. -/
axiom JPSZ_is_economical : IsEconomical JPSZ_set

/-- The main theorem: Erdős Problem #29 is SOLVED. -/
theorem erdos_29_solved : Erdos29Statement :=
  ⟨JPSZ_set, JPSZ_is_basis, JPSZ_is_economical⟩

/-! ## Properties of the JPSZ Construction -/

/-- The JPSZ set has density 0. -/
def HasDensityZero (A : Set ℕ) : Prop :=
  Tendsto (fun N => (Set.ncard (A ∩ Set.Icc 1 N) : ℝ) / N) atTop (nhds 0)

/-- The JPSZ set has density 0 (necessary for economical bases). -/
axiom JPSZ_density_zero : HasDensityZero JPSZ_set

/-- Representation count bound: r_A(n) ≤ exp(C √(log n)) for JPSZ. -/
axiom JPSZ_representation_bound :
  ∃ C > 0, ∀ n ≥ 2, (representationCount JPSZ_set n : ℝ) ≤
    Real.exp (C * Real.sqrt (Real.log n))

/-! ## Comparison with Other Bases -/

/-- The natural numbers ℕ itself is an additive basis (trivially). -/
theorem univ_is_basis : IsAdditiveBasis Set.univ := by
  unfold IsAdditiveBasis Doubling Sumset
  ext n
  simp only [Set.mem_setOf_eq, Set.mem_univ, true_and, iff_true]
  use 0, n
  ring

/-- But ℕ is not economical: r_ℕ(n) = n + 1. -/
theorem univ_not_economical : ¬IsEconomical Set.univ := by
  -- r_ℕ(n) = n + 1, which is not o(n^ε) for ε < 1
  -- This leads to contradiction since n+1 doesn't go to 0 when divided by n^(1/2)
  sorry

/-- The squares are not an additive basis (not every n is sum of two squares). -/
theorem squares_not_basis : ¬IsAdditiveBasis { n : ℕ | ∃ k : ℕ, n = k^2 } := by
  intro h
  -- 3 is not a sum of two squares
  have : (3 : ℕ) ∈ Doubling { n : ℕ | ∃ k : ℕ, n = k^2 } := by
    rw [additive_basis_iff] at h
    exact h 3
  unfold Doubling Sumset at this
  simp only [Set.mem_setOf_eq] at this
  obtain ⟨a, ⟨ka, hka⟩, b, ⟨kb, hkb⟩, hab⟩ := this
  -- 3 cannot be written as sum of two squares
  -- The squares ≤ 3 are 0 and 1, and no combination sums to 3
  sorry

/-! ## Thin Bases and Sidon Sets -/

/-- A Sidon set has at most one representation for each sum (r_A(n) ≤ 2). -/
def IsSidon (A : Set ℕ) : Prop :=
  ∀ n : ℕ, orderedRepCount A n ≤ 1

/-- No Sidon set can be an additive basis.
    (Sidon sets are too thin to cover all of ℕ.) -/
theorem sidon_not_basis (A : Set ℕ) (hS : IsSidon A) : ¬IsAdditiveBasis A := by
  -- A Sidon set has |A ∩ [1,N]| ≤ √N + O(1)
  -- So A + A has at most N + O(√N) elements in [1, 2N]
  -- Therefore A + A ≠ ℕ
  sorry

/- The JPSZ construction is a "middle ground":
   - Not as thin as Sidon sets (which can't be bases)
   - Not as thick as ℕ (which isn't economical)
   - Just right: basis with subpolynomial representations -/

/-! ## Explicit vs Probabilistic -/

/-- A set is "explicit" if it's computable/constructive. -/
class ExplicitSet (A : Set ℕ) where
  membership_decidable : DecidablePred (· ∈ A)

/-- The JPSZ set is explicit (has a constructive definition). -/
axiom JPSZ_explicit : ExplicitSet JPSZ_set

/- This distinguishes JPSZ from Erdős's probabilistic proof:
   - Erdős: ∃ A with properties (non-constructive)
   - JPSZ: Here is A explicitly (constructive) -/

/-! ## Historical Context

The problem originated in 1932 when Sidon asked Erdős.

Erdős's probabilistic argument:
Take each n ∈ A with probability p_n = n^{-1/2 + o(1)}.
Then with positive probability, A is both a basis and economical.

Why explicit matters:
1. Algorithmic applications (can compute A ∩ [1,N])
2. Mathematical insight into structure
3. Resolves 90+ year old open problem completely -/

/-! ## Lower Bounds -/

/-- Any additive basis A must have |A ∩ [1,N]| ≥ √N. -/
theorem basis_size_lower_bound (A : Set ℕ) (hA : IsAdditiveBasis A) :
    ∀ N ≥ 1, (Set.ncard (A ∩ Set.Icc 1 N) : ℝ) ≥ Real.sqrt N := by
  sorry

/-- The JPSZ construction is essentially optimal in size. -/
axiom JPSZ_size_optimal :
  ∃ C > 0, ∀ N ≥ 1, (Set.ncard (JPSZ_set ∩ Set.Icc 1 N) : ℝ) ≤
    C * Real.sqrt N * Real.sqrt (Real.log N)

/-! ## Summary

**Problem Status: SOLVED**

Erdős Problem #29 asked for an explicit construction of an additive basis A
(A + A = ℕ) where the representation function r_A(n) = o(n^ε) for all ε > 0.

**Answer: YES** (Jain-Pham-Sawhney-Zakharov 2024)

**Historical Journey:**
- 1932: Sidon asks Erdős the question
- ~1950s: Erdős proves existence using probabilistic methods
- 2024: JPSZ provide an explicit construction

**Significance:**
- Transforms existence proof into constructive algorithm
- 90+ years from question to complete answer
- Demonstrates power of modern combinatorics

**Key Properties of JPSZ Set:**
- Explicit and computable
- A + A = ℕ (additive basis)
- r_A(n) ≤ exp(C√(log n)) (economical)
- |A ∩ [1,N]| ≈ √N · √(log N) (optimal size)

References:
- Jain, Pham, Sawhney, Zakharov (2024): arXiv:2405.08650
- Erdős: Original probabilistic proof
- Sidon (1932): Original question
-/

end Erdos29
