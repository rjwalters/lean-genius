/-
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
import Mathlib.SetTheory.Ordinal.Exponential
import Mathlib.SetTheory.Cardinal.Basic
import Mathlib.Tactic

/- ## Core Definitions -/

/-- The ordinal partition relation: α → (α, k)² means that for any 2-coloring
    of pairs from α, there is either a monochromatic-red set of order type α
    or a monochromatic-blue set of size k.

    Formally: given any coloring f of ordered pairs of ordinals less than α,
    either there exists a strictly monotone embedding φ of [0,α) into itself
    with all pairs colored true (red), or there exist k ordinals less than α
    forming a strictly increasing sequence with all pairs colored false (blue). -/
def ordPartition (α : Ordinal.{0}) (k : ℕ) : Prop :=
  ∀ f : Ordinal → Ordinal → Bool,
    (∃ (φ : Ordinal → Ordinal), StrictMono φ ∧
      (∀ x, x < α → φ x < α) ∧
      ∀ x y, x < y → x < α → y < α → f (φ x) (φ y) = true) ∨
    (∃ (ψ : Fin k → Ordinal), StrictMono ψ ∧ (∀ i, ψ i < α) ∧
      ∀ i j, i < j → f (ψ i) (ψ j) = false)

/-- A partition ordinal for k-cliques: α satisfies α → (α, k)². -/
def IsPartitionOrd (α : Ordinal.{0}) (k : ℕ) : Prop :=
  ordPartition α k

/-- The Erdős–Hajnal conjecture (DISPROVED): if α → (α, 3)² then α → (α, n)²
    for all n ≥ 3. -/
def ErdosHajnalConjecture : Prop :=
  ∀ α : Ordinal.{0}, IsPartitionOrd α 3 → ∀ n : ℕ, 3 ≤ n → IsPartitionOrd α n

/- ## The Counterexample -/

/-- The specific counterexample ordinal: ω^(ω²). -/
noncomputable def counterexampleOrd : Ordinal :=
  Ordinal.omega0 ^ (Ordinal.omega0 ^ (2 : Ordinal))

/-- ω^(ω²) → (ω^(ω²), 3)²: the partition property holds for triangles.
    This follows from Schipperus's positive results for small CNF-length. -/
axiom counter_partition_3 : IsPartitionOrd counterexampleOrd 3

/-- ω^(ω²) ↛ (ω^(ω²), 5)²: the partition property FAILS for K_5.
    Larson demonstrated this specific counterexample. -/
axiom counter_not_partition_5 : ¬ IsPartitionOrd counterexampleOrd 5

/- ## Disproof -/

/-- The Erdős–Hajnal conjecture is false.
    Proof: ω^(ω²) satisfies α → (α,3)² but not α → (α,5)². -/
theorem erdos_118_disproved : ¬ ErdosHajnalConjecture := by
  intro h
  have h5 := h counterexampleOrd counter_partition_3 5 (by norm_num)
  exact counter_not_partition_5 h5

/- ## Positive Direction: Monotonicity Failure -/

/-- The partition threshold: for a given ordinal α, the largest k such that
    α → (α, k)² holds. -/
axiom partitionThreshold (α : Ordinal.{0}) : ℕ

/-- If α → (α, k)² holds, then α → (α, j)² holds for all j ≤ k.
    The partition relation is monotone decreasing in k.

    Proof: Given a blue k-clique, any j-element initial segment (j ≤ k)
    is also a blue clique. A red set of order type α passes through unchanged. -/
theorem partition_monotone_down (α : Ordinal.{0}) (k j : ℕ) (hjk : j ≤ k)
    (hk : IsPartitionOrd α k) : IsPartitionOrd α j := by
  intro f
  rcases hk f with ⟨φ, hφ_mono, hφ_bound, hφ_red⟩ | ⟨ψ, hψ_mono, hψ_bound, hψ_blue⟩
  · left; exact ⟨φ, hφ_mono, hφ_bound, hφ_red⟩
  · -- Restrict the blue k-clique ψ : Fin k → Ordinal to a j-element initial segment
    right
    let embed : Fin j → Fin k := fun i => ⟨i.val, Nat.lt_of_lt_of_le i.isLt hjk⟩
    have hemb : StrictMono embed := fun _ _ h => h
    exact ⟨ψ ∘ embed, hψ_mono.comp hemb, fun i => hψ_bound _,
           fun a b hab => hψ_blue _ _ (hemb hab)⟩

/-- The threshold captures the exact boundary: the partition property holds
    at the threshold and fails one step above. -/
axiom threshold_exact (α : Ordinal.{0}) :
    IsPartitionOrd α (partitionThreshold α) ∧
    ¬ IsPartitionOrd α (partitionThreshold α + 1)

/- ## Known Thresholds -/

/-- For ω^(ω²), the threshold is between 3 and 4 (inclusive).
    We know triangles work but K_5 fails.
    PROVED from threshold_exact, partition_monotone_down, and counterexample axioms. -/
theorem omega_omega2_threshold :
    3 ≤ partitionThreshold counterexampleOrd ∧
    partitionThreshold counterexampleOrd ≤ 4 := by
  constructor
  · -- Lower bound: threshold ≥ 3
    -- If threshold ≤ 2, then threshold+1 ≤ 3, and by monotonicity from
    -- counter_partition_3, IsPartitionOrd counterexampleOrd (threshold+1).
    -- But threshold_exact says ¬ IsPartitionOrd α (threshold+1). Contradiction.
    by_contra h
    push_neg at h -- h : partitionThreshold counterexampleOrd < 3
    have ht := (threshold_exact counterexampleOrd).2
    have hle : partitionThreshold counterexampleOrd + 1 ≤ 3 := by omega
    have h3 := partition_monotone_down counterexampleOrd 3
      (partitionThreshold counterexampleOrd + 1) hle counter_partition_3
    exact ht h3
  · -- Upper bound: threshold ≤ 4
    -- If threshold ≥ 5, then by threshold_exact, IsPartitionOrd α threshold.
    -- By monotonicity with j=5 ≤ threshold: IsPartitionOrd α 5.
    -- But counter_not_partition_5. Contradiction.
    by_contra h
    push_neg at h -- h : 5 ≤ partitionThreshold counterexampleOrd
    have ht := (threshold_exact counterexampleOrd).1
    have h5 := partition_monotone_down counterexampleOrd
      (partitionThreshold counterexampleOrd) 5 h ht
    exact counter_not_partition_5 h5

/- ## Relation to Problem #592 -/

/-- Problem #118 is closely related to Problem #592 (partition ordinals for triangles).
    The disproof shows that being a partition ordinal for triangles does not
    automatically extend to larger cliques.
    Previously axiomatized; follows directly from the counterexample. -/
theorem relation_to_592 :
    ∃ α : Ordinal.{0}, IsPartitionOrd α 3 ∧ ¬ IsPartitionOrd α 5 :=
  ⟨counterexampleOrd, counter_partition_3, counter_not_partition_5⟩
