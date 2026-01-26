/-!
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

/-! ## Core Definitions -/

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

/-! ## Specker's Results (1957) -/

/-- Specker (1957): ω² → (ω², 3)². The case β = 2 holds. -/
axiom specker_beta_two : HasPartitionProperty 2

/-- Specker (1957): For finite 3 ≤ n < ω, ω^n does NOT have the partition property. -/
axiom specker_finite_fail (n : ℕ) (h3 : 3 ≤ n) :
    ¬ HasPartitionProperty (Ordinal.ofNat n)

/-! ## Chang's Theorem (1972) -/

/-- Chang (1972): ω^ω → (ω^ω, 3)². The case β = ω holds. -/
axiom chang_beta_omega : HasPartitionProperty Ordinal.omega

/-! ## Galvin–Larson Necessary Condition (1974) -/

/-- An ordinal is additively indecomposable if it equals ω^γ for some ordinal γ.
    Equivalently, for all δ₁ δ₂ < β, δ₁ + δ₂ < β. -/
def IsAdditivelyIndecomposable (β : Ordinal) : Prop :=
  ∃ γ : Ordinal, β = Ordinal.omega ^ γ

/-- Galvin–Larson (1974): If β ≥ 3 has the partition property,
    then β must be additively indecomposable. -/
axiom galvin_larson_necessary (β : Ordinal) (hge : 3 ≤ β)
    (hpart : HasPartitionProperty β) :
    IsAdditivelyIndecomposable β

/-! ## Schipperus Classification (2010) -/

/-- The Cantor normal form length: the number of indecomposable ordinal
    summands in the Cantor normal form of γ. -/
axiom cantorNFLength (γ : Ordinal) : ℕ

/-- Schipperus (2010): If β = ω^γ where γ has Cantor NF length ≤ 2
    (i.e., γ is a sum of at most 2 indecomposable ordinals),
    then ω^β → (ω^β, 3)². -/
axiom schipperus_leq_two (γ : Ordinal) (hlen : cantorNFLength γ ≤ 2) :
    HasPartitionProperty (Ordinal.omega ^ γ)

/-- Schipperus (2010): If β = ω^γ where γ has Cantor NF length ≥ 4
    (i.e., γ is a sum of 4 or more indecomposable ordinals),
    then ω^β does NOT have the partition property. -/
axiom schipperus_geq_four (γ : Ordinal) (hlen : 4 ≤ cantorNFLength γ) :
    ¬ HasPartitionProperty (Ordinal.omega ^ γ)

/-! ## The Open Case -/

/-- The critical open case: Does the partition property hold when
    β = ω^γ and γ has Cantor NF length exactly 3?
    This is Erdős Problem #592 ($1,000 bounty). -/
axiom erdos_592_open_case (γ : Ordinal) (hlen : cantorNFLength γ = 3) :
    HasPartitionProperty (Ordinal.omega ^ γ) ∨
    ¬ HasPartitionProperty (Ordinal.omega ^ γ)

/-! ## Classification Summary -/

/-- The known partition ordinals of the form ω^β for countable β:
    - β = 0: trivially true (ω⁰ = 1)
    - β = 1: true (Ramsey's theorem for ω)
    - β = 2: true (Specker 1957)
    - 3 ≤ β < ω: false (Specker 1957)
    - β = ω^γ, CNF-length(γ) ≤ 2: true (Schipperus 2010)
    - β = ω^γ, CNF-length(γ) ≥ 4: false (Schipperus 2010)
    - β = ω^γ, CNF-length(γ) = 3: OPEN -/
axiom partition_ordinal_classification :
    HasPartitionProperty 0 ∧
    HasPartitionProperty 1 ∧
    HasPartitionProperty 2 ∧
    (∀ n : ℕ, 3 ≤ n → ¬ HasPartitionProperty (Ordinal.ofNat n))
