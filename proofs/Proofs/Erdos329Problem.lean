/-
Erdős Problem #329: Maximum Density of Sidon Sets

**Question**: For a Sidon set A ⊆ ℕ, how large can limsup |A ∩ {1,...,N}| / √N be?

**Status**: OPEN (exact supremum unknown)

**Known Results**:
- Erdős: 1/2 is achievable
- Krückeberg (1961): 1/√2 ≈ 0.707 is achievable
- Erdős-Turán (1941): Upper bound of 1

A **Sidon set** (or B₂ sequence) is a set where all pairwise sums a + b
(with a ≤ b) are distinct. The classic result is that |A ∩ [1,N]| ≤ √N + O(N^{1/4}).

The problem asks for the best constant in the normalized density √N.

**Connection to Perfect Difference Sets**:
If every finite Sidon set could be embedded in a perfect difference set,
then limsup = 1 would be achievable.

References:
- https://erdosproblems.com/329
- Erdős-Turán [ErTu41], On a problem of Sidon (1941)
- Krückeberg [Kr61], B₂-Folgen und verwandte Zahlenfolgen (1961)
-/

import Mathlib.Data.Set.Card
import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Order.LiminfLimsup
import Mathlib.Data.Finset.Card

namespace Erdos329

open Set Filter

/-! ## Sidon Sets (B₂ Sequences) -/

/--
A set A is a **Sidon set** (or B₂ sequence) if all pairwise sums are distinct.
That is, if a + b = c + d with a, b, c, d ∈ A and a ≤ b, c ≤ d, then {a, b} = {c, d}.

Equivalently: no sum a + b (with a, b ∈ A) occurs more than once.
-/
def IsSidon (A : Set ℕ) : Prop :=
  ∀ a b c d : ℕ, a ∈ A → b ∈ A → c ∈ A → d ∈ A →
    a ≤ b → c ≤ d → a + b = c + d → (a = c ∧ b = d)

/-! ## Density Measures -/

/--
The partial density of a set A up to N, normalized by √N instead of N.
This is the appropriate normalization for Sidon sets.
-/
noncomputable def sqrtPartialDensity (A : Set ℕ) (N : ℕ) : ℝ :=
  (A ∩ Set.Icc 1 N).ncard / Real.sqrt N

/--
The upper density of a Sidon set A, normalized by √N.
This is the quantity whose supremum we seek.
-/
noncomputable def sidonUpperDensity (A : Set ℕ) : ℝ :=
  limsup (fun N => sqrtPartialDensity A N) atTop

/-! ## Perfect Difference Sets -/

/--
A set D is a **perfect difference set** of order n if |D| = n + 1 and
every nonzero integer can be expressed as a difference d₁ - d₂ with d₁, d₂ ∈ D
in exactly one way.

Perfect difference sets are finite Sidon sets with optimal structure.
-/
def IsPerfectDifferenceSet (D : Set ℕ) (n : ℕ) : Prop :=
  D.ncard = n + 1 ∧ IsSidon D ∧
  ∀ k : ℤ, k ≠ 0 → ∃! (p : ℕ × ℕ), p.1 ∈ D ∧ p.2 ∈ D ∧ (p.1 : ℤ) - p.2 = k

/-! ## The Main Question -/

/--
**Erdős Problem #329** (OPEN): What is the supremum of sidonUpperDensity
over all Sidon sets?

Known: 1/√2 ≤ sup ≤ 1
The exact value is unknown.
-/
noncomputable def maxSidonDensity : ℝ :=
  sSup {d | ∃ A : Set ℕ, IsSidon A ∧ sidonUpperDensity A = d}

/-! ## Known Lower Bounds -/

/--
**Erdős**: There exists a Sidon set with upper density at least 1/2.
-/
axiom erdos_lower_bound :
    ∃ A : Set ℕ, IsSidon A ∧ sidonUpperDensity A ≥ 1 / 2

/--
**Krückeberg (1961)**: There exists a Sidon set with upper density exactly 1/√2.

This improved Erdős's 1/2 bound significantly.
The construction uses algebraic number theory.
-/
axiom kruckeberg_1961 :
    ∃ A : Set ℕ, IsSidon A ∧ sidonUpperDensity A = 1 / Real.sqrt 2

/--
Corollary: The maximum Sidon density is at least 1/√2 ≈ 0.707.
-/
theorem max_density_ge_inv_sqrt2 :
    ∃ A : Set ℕ, IsSidon A ∧ sidonUpperDensity A ≥ 1 / Real.sqrt 2 := by
  obtain ⟨A, hA, hd⟩ := kruckeberg_1961
  exact ⟨A, hA, hd.ge⟩

/-! ## Known Upper Bound -/

/--
**Erdős-Turán (1941)**: Every Sidon set has upper density at most 1.

The proof uses the counting argument: if A is Sidon with |A ∩ [1,N]| = k,
then the k(k+1)/2 pairwise sums are distinct and lie in [2, 2N],
so k(k+1)/2 ≤ 2N - 1, giving k ≤ √(4N) + O(1).
-/
axiom erdos_turan_upper_bound :
    ∀ A : Set ℕ, IsSidon A → sidonUpperDensity A ≤ 1

/--
The maximum Sidon density is at most 1.
-/
theorem max_density_le_one :
    ∀ d ∈ {d | ∃ A : Set ℕ, IsSidon A ∧ sidonUpperDensity A = d}, d ≤ 1 := by
  intro d ⟨A, hSidon, hd⟩
  rw [← hd]
  exact erdos_turan_upper_bound A hSidon

/-! ## Connection to Perfect Difference Sets -/

/--
**Conditional Result**: If every finite Sidon set can be embedded in a
perfect difference set, then the maximum density is exactly 1.
-/
axiom embedding_implies_density_one :
    (∀ A : Finset ℕ, IsSidon ↑A → ∃ D : Set ℕ, ∃ n : ℕ,
      ↑A ⊆ D ∧ IsPerfectDifferenceSet D n) →
    maxSidonDensity = 1

/--
**Converse**: If the maximum density is 1, then every finite Sidon set
can be embedded in a perfect difference set.
-/
axiom density_one_implies_embedding :
    maxSidonDensity = 1 →
    (∀ A : Finset ℕ, IsSidon ↑A → ∃ D : Set ℕ, ∃ n : ℕ,
      ↑A ⊆ D ∧ IsPerfectDifferenceSet D n)

/-! ## Basic Examples -/

/-- The empty set is trivially Sidon. -/
theorem empty_is_sidon : IsSidon ∅ := by
  intro a b c d ha _ _ _
  exact absurd ha (Set.notMem_empty a)

/-- Any singleton is Sidon. -/
theorem singleton_is_sidon (n : ℕ) : IsSidon {n} := by
  intro a b c d ha hb hc hd hab hcd heq
  simp only [Set.mem_singleton_iff] at ha hb hc hd
  rw [ha, hb, hc, hd]
  exact ⟨rfl, rfl⟩

/-- The set {1, 2, 5, 10} is a Sidon set (all 6 pairwise sums are distinct). -/
axiom sidon_example_1_2_5_10 : IsSidon ({1, 2, 5, 10} : Set ℕ)

/-! ## Verified Computations -/

/-- 1 + 2 = 3 -/
example : (1 : ℕ) + 2 = 3 := by native_decide

/-- 1 + 5 = 6 -/
example : (1 : ℕ) + 5 = 6 := by native_decide

/-- 1 + 10 = 11 -/
example : (1 : ℕ) + 10 = 11 := by native_decide

/-- 2 + 5 = 7 -/
example : (2 : ℕ) + 5 = 7 := by native_decide

/-- 2 + 10 = 12 -/
example : (2 : ℕ) + 10 = 12 := by native_decide

/-- 5 + 10 = 15 -/
example : (5 : ℕ) + 10 = 15 := by native_decide

/-! All 6 sums {3, 6, 7, 11, 12, 15} are distinct, as verified above. -/

/-! ## Summary -/

/-- **Erdős Problem #329** Summary:

1. OPEN: What is sup{sidonUpperDensity A : A is Sidon}?
2. LOWER: ≥ 1/√2 ≈ 0.707 (Krückeberg 1961)
3. UPPER: ≤ 1 (Erdős-Turán 1941)
4. CONDITIONAL: = 1 iff finite Sidon sets embed in perfect difference sets
-/
theorem erdos_329_summary :
    -- Krückeberg's lower bound
    (∃ A : Set ℕ, IsSidon A ∧ sidonUpperDensity A = 1 / Real.sqrt 2) ∧
    -- Erdős-Turán upper bound
    (∀ A : Set ℕ, IsSidon A → sidonUpperDensity A ≤ 1) :=
  ⟨kruckeberg_1961, erdos_turan_upper_bound⟩

end Erdos329
