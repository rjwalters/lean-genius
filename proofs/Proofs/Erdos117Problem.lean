/-!
# Erdős Problem #117 — Covering Groups by Abelian Subgroups

Let h(n) be the minimum number of Abelian subgroups needed to cover
any group G with the property that every subset of size > n contains
some x ≠ y with xy = yx.

Estimate h(n).

## Known Results
- Pyber (1987): c₁^n < h(n) < c₂^n for constants c₂ > c₁ > 1
- Lower bound previously known to Isaacs

Status: OPEN
Reference: https://erdosproblems.com/117
-/

import Mathlib.GroupTheory.Subgroup.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Nat.Basic
import Mathlib.Tactic

/-! ## Definitions -/

/-- A group has the n-commuting property if every subset of size > n
    contains two distinct commuting elements. -/
def HasNCommutingProperty (G : Type*) [Group G] (n : ℕ) : Prop :=
  ∀ S : Finset G, S.card > n →
    ∃ x y, x ∈ S ∧ y ∈ S ∧ x ≠ y ∧ x * y = y * x

/-- A subgroup H of G is Abelian. -/
def IsAbelianSubgroup (G : Type*) [Group G] (H : Subgroup G) : Prop :=
  ∀ x y : G, x ∈ H → y ∈ H → x * y = y * x

/-- h(n) is the minimum k such that every group with the n-commuting
    property can be covered by k Abelian subgroups. -/
noncomputable def abelianCoverNumber (n : ℕ) : ℕ :=
  sInf {k : ℕ | ∀ (G : Type*) [Group G] [Fintype G],
    HasNCommutingProperty G n →
    ∃ H : Fin k → Subgroup G,
      (∀ i, IsAbelianSubgroup G (H i)) ∧
      ∀ g : G, ∃ i, g ∈ H i}

/-! ## Main Problem -/

/-- **Erdős Problem #117**: estimate h(n). Known: exponential in n. -/
axiom erdos_117_problem :
  ∃ c₁ c₂ : ℝ, 1 < c₁ ∧ c₁ < c₂ ∧
    ∀ n : ℕ, n > 0 →
      c₁ ^ n < (abelianCoverNumber n : ℝ) ∧
      (abelianCoverNumber n : ℝ) < c₂ ^ n

/-! ## Known Results -/

/-- **Pyber (1987)**: h(n) is exponential. There exist c₂ > c₁ > 1 with
    c₁^n < h(n) < c₂^n. The gap between c₁ and c₂ is open. -/
axiom pyber_1987 :
  ∃ c₁ c₂ : ℝ, 1 < c₁ ∧ c₁ < c₂ ∧
    ∀ n : ℕ, n > 0 →
      c₁ ^ n ≤ (abelianCoverNumber n : ℝ) ∧
      (abelianCoverNumber n : ℝ) ≤ c₂ ^ n

/-- **Isaacs Lower Bound**: the exponential lower bound c₁^n was known
    to Isaacs before Pyber's work. -/
axiom isaacs_lower :
  ∃ c : ℝ, c > 1 ∧ ∀ n : ℕ, n > 0 → c ^ n ≤ (abelianCoverNumber n : ℝ)

/-! ## Observations -/

/-- **Trivial Case n = 1**: every pair of elements commutes, so G is Abelian.
    Then h(1) = 1. -/
axiom trivial_case : abelianCoverNumber 1 = 1

/-- **Connection to Ramsey Theory**: the n-commuting property is a Ramsey-type
    condition on the group. The covering number h(n) measures how far the group
    is from being globally Abelian. -/
axiom ramsey_connection : True

/-- **Open**: determine the exact base of the exponential growth. Is there
    a single constant c > 1 with h(n) = Θ(c^n)? -/
axiom exact_base_open : True
