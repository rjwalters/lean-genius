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

/- ## Positive Direction: Monotonicity -/

/-- If α → (α, k)² holds, then α → (α, j)² holds for all j ≤ k.
    Monotonicity: the partition relation is decreasing in k. -/
theorem partition_monotone_down (α : Ordinal.{0}) (k j : ℕ) (hjk : j ≤ k)
    (hk : IsPartitionOrd α k) : IsPartitionOrd α j := by
  intro f
  rcases hk f with ⟨φ, hφ_mono, hφ_bound, hφ_red⟩ | ⟨ψ, hψ_mono, hψ_bound, hψ_blue⟩
  · left; exact ⟨φ, hφ_mono, hφ_bound, hφ_red⟩
  · right
    let embed : Fin j → Fin k := fun i => ⟨i.val, Nat.lt_of_lt_of_le i.isLt hjk⟩
    have hemb : StrictMono embed := fun _ _ h => h
    exact ⟨ψ ∘ embed, hψ_mono.comp hemb, fun i => hψ_bound _,
           fun a b hab => hψ_blue _ _ (hemb hab)⟩

/-- Contrapositive: if ¬ IsPartitionOrd α j, then ¬ IsPartitionOrd α k for k ≥ j. -/
theorem partition_monotone_up_neg (α : Ordinal.{0}) (j k : ℕ) (hjk : j ≤ k)
    (hj : ¬ IsPartitionOrd α j) : ¬ IsPartitionOrd α k :=
  fun hk => hj (partition_monotone_down α k j hjk hk)

/-- If the partition property holds at k but fails at m > k, there exists
    an exact transition point t ∈ [k, m) where it holds at t but fails at t+1.
    Proof: strong induction on m. -/
theorem partition_transition_exists (α : Ordinal.{0}) (k m : ℕ)
    (hk : IsPartitionOrd α k) (hm : ¬ IsPartitionOrd α m) (hkm : k < m) :
    ∃ t, k ≤ t ∧ t < m ∧ IsPartitionOrd α t ∧ ¬ IsPartitionOrd α (t + 1) := by
  revert k
  induction m using Nat.strong_rec_on with
  | _ m ih =>
    intro k hk hm hkm
    by_cases hm1 : IsPartitionOrd α (m - 1)
    · -- Transition at t = m-1: holds at m-1, fails at (m-1)+1 = m
      refine ⟨m - 1, by omega, by omega, hm1, ?_⟩
      rwa [Nat.sub_add_cancel (by omega)]
    · -- Fails already at m-1; recurse after finding k < m-1
      have hkm1 : k < m - 1 := by
        by_contra h; push_neg at h
        exact hm1 (partition_monotone_down α k (m - 1) h hk)
      obtain ⟨t, ht1, ht2, ht3, ht4⟩ :=
        ih (m - 1) (Nat.sub_lt (by omega) one_pos) k hk hm1 hkm1
      exact ⟨t, ht1, by omega, ht3, ht4⟩

/- ## Known Thresholds -/

/-- For ω^(ω²), the partition threshold is in {3, 4}: there exists t ∈ [3, 4]
    such that IsPartitionOrd t and ¬ IsPartitionOrd (t+1).
    Proved from the two deep counterexample axioms via partition_transition_exists. -/
theorem omega_omega2_threshold :
    ∃ t : ℕ, 3 ≤ t ∧ t ≤ 4 ∧
    IsPartitionOrd counterexampleOrd t ∧
    ¬ IsPartitionOrd counterexampleOrd (t + 1) := by
  obtain ⟨t, ht1, ht2, ht3, ht4⟩ :=
    partition_transition_exists counterexampleOrd 3 5
      counter_partition_3 counter_not_partition_5 (by omega)
  exact ⟨t, by omega, by omega, ht3, ht4⟩

/- ## Relation to Problem #592 -/

/-- Problem #118 is closely related to Problem #592 (partition ordinals for triangles).
    The disproof shows that being a partition ordinal for triangles does not
    automatically extend to larger cliques.
    Previously axiomatized; follows directly from the counterexample. -/
theorem relation_to_592 :
    ∃ α : Ordinal.{0}, IsPartitionOrd α 3 ∧ ¬ IsPartitionOrd α 5 :=
  ⟨counterexampleOrd, counter_partition_3, counter_not_partition_5⟩
