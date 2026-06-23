/-
# Erdős Problem #592: Partition Ordinals and Ordinal Ramsey Theory

For which countable ordinals β does ω^β → (ω^β, 3)² hold?
That is, for which β is it true that in any red/blue 2-coloring of K_{ω^β},
there exists either a red K_{ω^β} or a blue K_3?

## Key Results
- β = 2: TRUE (Specker 1957)
- 3 ≤ β < ω: FALSE (Specker 1957)
- β = ω: TRUE (Chang 1972)
- Galvin–Larson (1974): if β ≥ 3 works, then β must be additively
  indecomposable (β = ω^γ for some γ)
- Schipperus (2010): TRUE when γ is sum of 1 or 2 indecomposable ordinals;
  FALSE when γ is sum of ≥ 4 indecomposable ordinals

## Status: OPEN ($1,000 bounty)
The case γ = sum of exactly 3 indecomposable ordinals remains unresolved.

Reference: https://erdosproblems.com/592
-/

import Mathlib.SetTheory.Ordinal.Arithmetic
import Mathlib.SetTheory.Cardinal.Basic
import Mathlib.Tactic

/- ## Core Definitions -/

/-- A countable ordinal: an ordinal with cardinality at most ℵ₀. -/
def IsCountableOrdinal (β : Ordinal) : Prop :=
  β.card ≤ Cardinal.aleph0

/-- The ordinal Ramsey arrow: α → (α, k)² means that for any 2-coloring of
    pairs from α, there is either a monochromatic-0 copy of size α or a
    monochromatic-1 copy of size k. -/
axiom ordinalPartition (α : Ordinal) (k : ℕ) : Prop

/-- An ordinal α is a partition ordinal (for triangles) if α → (α, 3)². -/
def IsPartitionOrdinal (α : Ordinal) : Prop :=
  ordinalPartition α 3

/-- β has the partition property if ω^β → (ω^β, 3)². -/
def HasPartitionProperty (β : Ordinal) : Prop :=
  IsPartitionOrdinal (Ordinal.omega ^ β)

/- ## Specker's Results (1957) -/

/- ## Chang's Theorem (1972) -/

/- ## Galvin–Larson Necessary Condition (1974) -/

/-- An ordinal is additively indecomposable if it equals ω^γ for some ordinal γ.
    Equivalently, for all δ₁ δ₂ < β, δ₁ + δ₂ < β. -/
def IsAdditivelyIndecomposable (β : Ordinal) : Prop :=
  ∃ γ : Ordinal, β = Ordinal.omega ^ γ

/- ## Schipperus Classification (2010) -/

/-- The Cantor normal form length: the number of indecomposable ordinal
    summands in the Cantor normal form of γ. -/
axiom cantorNFLength (γ : Ordinal) : ℕ

/- ## The Open Case -/

/- ## Classification Summary -/
