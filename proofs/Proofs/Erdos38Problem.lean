/-
  Erdős Problem #38: Essential Components and Schnirelmann Density

  Source: https://erdosproblems.com/38
  Status: OPEN

  Statement:
  Does there exist B ⊆ ℕ which is NOT an additive basis, but has the property
  that for every set A ⊆ ℕ of Schnirelmann density α and every N, there exists
  b ∈ B such that
    |(A ∪ (A + b)) ∩ {1,...,N}| ≥ (α + f(α)) · N
  where f(α) > 0 for 0 < α < 1?

  Background:
  - Schnirelmann density: σ(A) = inf_{N≥1} |A ∩ {1,...,N}| / N
  - Additive basis: B is a basis of order k if B + B + ... + B (k times) = ℕ
  - Essential component: A set that increases Schnirelmann density when added

  Related Results:
  - Erdős [1936]: Additive bases of order k satisfy a related inequality with
    factor α(1-α)/(2k)
  - Linnik [1942]: First constructed an essential component that isn't an
    additive basis (weaker than what this problem asks)

  This problem asks whether there's a set with the density-boosting property
  of essential components but without being an additive basis.
-/

import Mathlib

open Set Filter
open scoped Pointwise

namespace Erdos38

/-! ## Schnirelmann Density

The Schnirelmann density of A ⊆ ℕ is:
  σ(A) = inf_{N≥1} |A ∩ {1,...,N}| / N

This is a "worst-case" density - it's the infimum over all initial segments.
Unlike asymptotic density, it's sensitive to gaps early in the sequence.
-/

/-- The counting function: |A ∩ {1,...,N}| -/
noncomputable def countingFunction (A : Set ℕ) (N : ℕ) : ℕ :=
  (A ∩ Icc 1 N).ncard

/-- Schnirelmann density: the infimum of |A ∩ {1,...,N}| / N over N ≥ 1 -/
noncomputable def schnirelmannDensity (A : Set ℕ) : ℝ :=
  ⨅ N : { n : ℕ // n ≥ 1 }, (countingFunction A N : ℝ) / N

/-- Basic property: Schnirelmann density is in [0, 1] -/
axiom schnirelmann_density_bounds (A : Set ℕ) :
  0 ≤ schnirelmannDensity A ∧ schnirelmannDensity A ≤ 1

/-! ## Additive Bases

A set B is an additive basis of order k if every natural number can be
written as a sum of at most k elements from B.
-/

/-- B is an additive basis of order k -/
def IsAdditiveBasisOfOrder (B : Set ℕ) (k : ℕ) : Prop :=
  ∀ n : ℕ, ∃ (S : Finset ℕ), ↑S ⊆ B ∧ S.card ≤ k ∧ S.sum id = n

/-- B is an additive basis (of some finite order) -/
def IsAdditiveBasis (B : Set ℕ) : Prop :=
  ∃ k : ℕ, IsAdditiveBasisOfOrder B k

/-! ## Essential Components

An essential component is a set that increases the Schnirelmann density
of any set when added to it. This is weaker than being an additive basis.
-/

/-- The translate A + {b} = {a + b : a ∈ A} -/
def translate (A : Set ℕ) (b : ℕ) : Set ℕ := A + {b}

/-- The union A ∪ (A + b) has larger counting function -/
def boostsCount (B : Set ℕ) (A : Set ℕ) (N : ℕ) (f : ℝ → ℝ) : Prop :=
  let α := schnirelmannDensity A
  ∃ b ∈ B, (countingFunction (A ∪ translate A b) N : ℝ) ≥ (α + f α) * N

/-- The density-boosting property for all sets and all N -/
def HasDensityBoostProperty (B : Set ℕ) (f : ℝ → ℝ) : Prop :=
  ∀ A : Set ℕ, ∀ N : ℕ, N ≥ 1 → boostsCount B A N f

/-! ## The Main Problem

**Erdős Problem #38**: Does there exist B that is NOT an additive basis
but still has the density-boosting property?
-/

/-- The problem asks for existence of B with:
    1. B is NOT an additive basis
    2. For some f with f(α) > 0 for 0 < α < 1, B has the density-boost property -/
def Erdos38Problem : Prop :=
  ∃ B : Set ℕ, ¬IsAdditiveBasis B ∧
    ∃ f : ℝ → ℝ, (∀ α : ℝ, 0 < α → α < 1 → f α > 0) ∧
      HasDensityBoostProperty B f

/-! ## Known Related Results -/

/-- **Erdős [1936]**: Additive bases of order k satisfy the property with
    f(α) = α(1-α)/(2k). This shows bases DO have the density-boost property. -/
axiom erdos_1936_bases (B : Set ℕ) (k : ℕ) (hB : IsAdditiveBasisOfOrder B k) :
  HasDensityBoostProperty B (fun α => α * (1 - α) / (2 * k))

/-- **Linnik [1942]**: There exists an essential component that is not
    an additive basis. However, "essential component" is a weaker notion
    than the density-boost property asked here. -/
axiom linnik_essential_component :
  ∃ B : Set ℕ, ¬IsAdditiveBasis B ∧
    ∀ A : Set ℕ, schnirelmannDensity A > 0 →
      schnirelmannDensity (A + B) > schnirelmannDensity A

/-- The random set result: For B = ℕ, the factor α(1-α) in Erdős's bound
    cannot be improved. -/
axiom random_set_optimality :
  ∀ f : ℝ → ℝ, (∀ α, 0 < α → α < 1 → f α > α * (1 - α)) →
    ¬HasDensityBoostProperty (univ : Set ℕ) f

/-! ## Problem Status

This problem remains OPEN. The gap is:
- We know additive bases have the density-boost property
- We know there are essential components that aren't bases
- We don't know if the stronger density-boost property can hold without
  being a basis

The question essentially asks: is the density-boost property equivalent
to being an additive basis, or is there a "middle ground"?
-/

/-- The main conjecture (OPEN) -/
axiom erdos_38_conjecture : Erdos38Problem ∨ ¬Erdos38Problem

end Erdos38
