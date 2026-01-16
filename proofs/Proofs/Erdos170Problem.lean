/-
  Erdős Problem #170: Sparse Rulers (Perfect Difference Bases)

  Source: https://erdosproblems.com/170
  Status: PARTIALLY SOLVED (limit exists, bounds known)

  Question:
  Let F(N) be the smallest size of A ⊆ {0,...,N} such that every integer
  in {1,...,N} can be expressed as a difference a₁ - a₀ with a₀, a₁ ∈ A.
  Find lim_{N→∞} F(N)/√N.

  Known Results:
  - Erdős-Gál (1948): The limit exists
  - Leech (1956): Lower bound 1.56...
  - Wichmann (1963): Upper bound √3 ≈ 1.732

  The exact value remains open, but is known to be in [1.56, √3].

  Reference:
  - Erdős, Gál, "On the representation of 1,2,...,n by differences" (1948)
  - Leech, J., "On the representation of 1,2,...,n by differences" (1956)
  - Wichmann, B., "A note on restricted difference bases" (1963)
-/

import Mathlib

open Set Nat Filter Finset

namespace Erdos170

/-! ## Core Definitions -/

/-- A set A is an **N-perfect ruler** (or N-difference basis) if every
    integer k in {1,...,N} can be expressed as a₁ - a₀ for some a₀, a₁ ∈ A. -/
def IsPerfectRuler (N : ℕ) (A : Finset ℕ) : Prop :=
  ∀ k : ℕ, 1 ≤ k → k ≤ N → ∃ a₀ ∈ A, ∃ a₁ ∈ A, k = a₁ - a₀

/-- A **restricted** N-perfect ruler is contained in {0,...,N}. -/
def IsRestrictedPerfectRuler (N : ℕ) (A : Finset ℕ) : Prop :=
  A ⊆ Finset.range (N + 1) ∧ IsPerfectRuler N A

/-! ## The Trivial Ruler -/

/-- The trivial ruler {0, 1, ..., N} with all marks. -/
def trivialRuler (N : ℕ) : Finset ℕ := Finset.range (N + 1)

/-- The trivial ruler is a perfect ruler. -/
theorem trivial_is_perfect (N : ℕ) : IsRestrictedPerfectRuler N (trivialRuler N) := by
  constructor
  · exact Finset.Subset.refl _
  · intro k hk1 hkN
    use 0
    constructor
    · simp [trivialRuler]
    use k
    constructor
    · simp [trivialRuler]
      omega
    · omega

/-! ## The Minimum Size Function F(N) -/

/-- F(N) is the minimum cardinality of a restricted N-perfect ruler. -/
noncomputable def F (N : ℕ) : ℕ :=
  sInf { m : ℕ | ∃ A : Finset ℕ, IsRestrictedPerfectRuler N A ∧ A.card = m }

/-- F(N) is well-defined: there exists at least one perfect ruler. -/
theorem F_nonempty (N : ℕ) :
    { m : ℕ | ∃ A : Finset ℕ, IsRestrictedPerfectRuler N A ∧ A.card = m }.Nonempty := by
  use (trivialRuler N).card
  exact ⟨trivialRuler N, trivial_is_perfect N, rfl⟩

/-! ## Basic Bounds -/

/-- Trivial upper bound: F(N) ≤ N + 1. -/
theorem F_upper_trivial (N : ℕ) : F N ≤ N + 1 := by
  unfold F
  apply Nat.sInf_le
  use trivialRuler N
  constructor
  · exact trivial_is_perfect N
  · simp [trivialRuler]

/-- Lower bound: F(N) ≥ 2 for N ≥ 1.
    Proof: Empty set can't measure 1; singleton a-a=0, can't measure 1. -/
axiom F_lower_two (N : ℕ) (hN : N ≥ 1) : F N ≥ 2

/-! ## The Limit Theorem -/

/-- **Erdős-Gál (1948)**: The limit lim_{N→∞} F(N)/√N exists. -/
axiom erdos_gal_limit_exists :
    ∃ L : ℝ, Tendsto (fun N => (F N : ℝ) / Real.sqrt N) atTop (nhds L)

/-- The limit value (noncomputable). -/
noncomputable def limitValue : ℝ := Classical.choose erdos_gal_limit_exists

/-- **Leech (1956)**: Lower bound L ≥ 1.56... -/
axiom leech_lower_bound : limitValue ≥ 1.56

/-- **Wichmann (1963)**: Upper bound L ≤ √3 ≈ 1.732. -/
axiom wichmann_upper_bound : limitValue ≤ Real.sqrt 3

/-- The limit is in the interval [1.56, √3]. -/
theorem limit_in_interval : 1.56 ≤ limitValue ∧ limitValue ≤ Real.sqrt 3 :=
  ⟨leech_lower_bound, wichmann_upper_bound⟩

/-! ## Known Constructions -/

/-- **Wichmann Rulers**: Achieve asymptotic density √3.
    For certain N, the ruler {0, 1, 3, 6, ..., (k²+k)/2, ..., N} is optimal. -/
axiom wichmann_construction :
    ∀ ε > 0, ∃ N₀, ∀ N ≥ N₀, (F N : ℝ) / Real.sqrt N ≤ Real.sqrt 3 + ε

/-- **Redei-Renyi Lower Bound**: Any perfect ruler needs at least ~√(2N) marks
    to cover all differences. -/
axiom redei_renyi_lower :
    ∀ N : ℕ, N ≥ 1 → (F N : ℝ) ≥ Real.sqrt (2 * N) - 1

/-! ## Unrestricted Version -/

/-- The unrestricted version: A can be any finite subset of ℕ. -/
def IsUnrestrictedPerfectRuler (N : ℕ) (A : Finset ℕ) : Prop :=
  ∀ k : ℕ, 1 ≤ k → k ≤ N → ∃ a₀ ∈ A, ∃ a₁ ∈ A, k = a₁ - a₀

/-- F'(N) for unrestricted rulers. -/
noncomputable def F' (N : ℕ) : ℕ :=
  sInf { m : ℕ | ∃ A : Finset ℕ, IsUnrestrictedPerfectRuler N A ∧ A.card = m }

/-- Unrestricted rulers can be smaller: F'(N) ≤ F(N). -/
axiom unrestricted_le_restricted : ∀ N, F' N ≤ F N

/-! ## Examples -/

/-- Example: {0, 1, 3} is a 3-perfect ruler.
    Differences: 1-0=1, 3-0=3, 3-1=2. -/
axiom example_3_ruler : IsPerfectRuler 3 {0, 1, 3}

/-- Example: {0, 1, 2, 6, 10, 14, 17, 21, 25, 27, 28, 29, 30} is a 30-perfect ruler
    with only 13 marks (instead of 31). This is an optimal ruler for N=30. -/
axiom example_30_ruler :
    IsPerfectRuler 30 {0, 1, 2, 6, 10, 14, 17, 21, 25, 27, 28, 29, 30}

/-! ## Summary

**Problem Status: PARTIALLY SOLVED**

Erdős Problem #170 (Sparse Rulers) asks for the limit of F(N)/√N where F(N)
is the minimum size of a set A ⊆ {0,...,N} such that every 1 ≤ k ≤ N is
a difference of elements in A.

**Main Results:**
- Erdős-Gál (1948): The limit exists
- Leech (1956): Lower bound ≈ 1.56
- Wichmann (1963): Upper bound √3 ≈ 1.732

**Current Knowledge:** The limit is in [1.56, √3], exact value unknown.

**Computational Evidence:** Suggests √3 may be the true limit.
-/

end Erdos170
