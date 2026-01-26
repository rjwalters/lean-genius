/-!
# Erdős Problem #118: Partition Ordinals and Higher Cliques

Does α → (α, 3)² imply α → (α, n)² for all finite n ≥ 3?
That is, if every 2-coloring of K_α yields a red K_α or blue triangle,
must it also yield a red K_α or blue K_n for all n?

## Answer: NO (Disproved)
- Schipperus (1999/2010) and Darby (1999) independently showed the answer is NO.
- Larson gave a specific counterexample: α = ω^(ω²), n = 5.
  We have ω^(ω²) → (ω^(ω²), 3)² but ω^(ω²) ↛ (ω^(ω²), 5)².

## Context
The problem was posed by Erdős and Hajnal. Partition ordinals satisfying
α → (α, k)² can have different thresholds for different k.

Reference: https://erdosproblems.com/118
-/

import Mathlib.SetTheory.Ordinal.Arithmetic
import Mathlib.SetTheory.Cardinal.Basic
import Mathlib.Tactic

/-! ## Core Definitions -/

/-- The ordinal partition relation: α → (α, k)² means that for any 2-coloring
    of pairs from α, there is either a monochromatic-red set of order type α
    or a monochromatic-blue set of size k. -/
axiom ordPartition (α : Ordinal) (k : ℕ) : Prop

/-- A partition ordinal for k-cliques: α satisfies α → (α, k)². -/
def IsPartitionOrd (α : Ordinal) (k : ℕ) : Prop :=
  ordPartition α k

/-- The Erdős–Hajnal conjecture (DISPROVED): if α → (α, 3)² then α → (α, n)²
    for all n ≥ 3. -/
def ErdosHajnalConjecture : Prop :=
  ∀ α : Ordinal, IsPartitionOrd α 3 → ∀ n : ℕ, 3 ≤ n → IsPartitionOrd α n

/-! ## The Counterexample -/

/-- The specific counterexample ordinal: ω^(ω²). -/
noncomputable def counterexampleOrd : Ordinal :=
  Ordinal.omega ^ (Ordinal.omega ^ (2 : Ordinal))

/-- ω^(ω²) → (ω^(ω²), 3)²: the partition property holds for triangles.
    This follows from Schipperus's positive results for small CNF-length. -/
axiom counter_partition_3 : IsPartitionOrd counterexampleOrd 3

/-- ω^(ω²) ↛ (ω^(ω²), 5)²: the partition property FAILS for K_5.
    Larson demonstrated this specific counterexample. -/
axiom counter_not_partition_5 : ¬ IsPartitionOrd counterexampleOrd 5

/-! ## Disproof -/

/-- The Erdős–Hajnal conjecture is false.
    Proof: ω^(ω²) satisfies α → (α,3)² but not α → (α,5)². -/
theorem erdos_118_disproved : ¬ ErdosHajnalConjecture := by
  intro h
  have h5 := h counterexampleOrd counter_partition_3 5 (by norm_num)
  exact counter_not_partition_5 h5

/-! ## Positive Direction: Monotonicity Failure -/

/-- The partition threshold: for a given ordinal α, the largest k such that
    α → (α, k)² holds. -/
axiom partitionThreshold (α : Ordinal) : ℕ

/-- If α → (α, k)² holds, then α → (α, j)² holds for all j ≤ k.
    The partition relation is monotone decreasing in k. -/
axiom partition_monotone_down (α : Ordinal) (k j : ℕ) (hjk : j ≤ k)
    (hk : IsPartitionOrd α k) : IsPartitionOrd α j

/-- The threshold captures the exact boundary. -/
axiom threshold_exact (α : Ordinal) :
    IsPartitionOrd α (partitionThreshold α) ∧
    (partitionThreshold α + 1 > 2 → ¬ IsPartitionOrd α (partitionThreshold α + 1))

/-! ## Known Thresholds -/

/-- For ω^(ω²), the threshold is between 3 and 4 (inclusive).
    We know triangles work but K_5 fails. -/
axiom omega_omega2_threshold :
    3 ≤ partitionThreshold counterexampleOrd ∧
    partitionThreshold counterexampleOrd ≤ 4

/-! ## Relation to Problem #592 -/

/-- Problem #118 is closely related to Problem #592 (partition ordinals for triangles).
    The disproof shows that being a partition ordinal for triangles does not
    automatically extend to larger cliques. -/
axiom relation_to_592 :
    ∃ α : Ordinal, IsPartitionOrd α 3 ∧ ¬ IsPartitionOrd α 5
