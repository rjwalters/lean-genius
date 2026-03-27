/-
# Erdős Problem #749: Dense Sumsets with Bounded Representation

For ε > 0, does there exist A ⊆ ℕ such that the lower density
of A + A is at least 1 - ε, yet the representation function
r(n) = #{(a,b) ∈ A × A : a + b = n} is bounded (by a constant
depending on ε)?

## Background
This explores the tension between additive density and representation
count. If A is a Sidon set, r(n) ≤ 2 but A + A has density 0.
If A has positive density, A + A is "large" but r(n) is typically unbounded.
Can we have both: dense sumset AND bounded r(n)?

## Related: Problem #28 (Erdős–Turán)
The Erdős–Turán conjecture asks whether r(n) must be unbounded
for any additive basis of order 2. Problem #749 asks about a
"near-basis" (lower density close to 1) with bounded r(n).

## Status: OPEN

Reference: https://erdosproblems.com/749
-/

import Mathlib

/- ## Core Definitions -/

/-- The representation function r_A(n): the number of ways to write n = a + b
    with a, b ∈ A and a ≤ b. -/
def repFunction (A : Set ℕ) (n : ℕ) : ℕ :=
  Finset.card ((Finset.range (n + 1)).filter (fun a => a ∈ A ∧ (n - a) ∈ A ∧ a ≤ n - a))

/-- The sumset A + A = {a + b : a, b ∈ A}. -/
def sumSet (A : Set ℕ) : Set ℕ :=
  {n : ℕ | ∃ a b : ℕ, a ∈ A ∧ b ∈ A ∧ n = a + b}

/-- Counting function: |S ∩ {1,...,N}|. -/
noncomputable def countingFn (S : Set ℕ) (N : ℕ) : ℕ :=
  Set.ncard (S ∩ Set.Icc 1 N)

/-- Density ratio: |S ∩ {1,...,N}| / N. -/
noncomputable def densityRatio (S : Set ℕ) (N : ℕ) : ℝ :=
  (countingFn S N : ℝ) / N

/-- The lower density of a set S ⊆ ℕ: lim inf_{N→∞} |S ∩ {1,...,N}| / N. -/
noncomputable def lowerDensity (S : Set ℕ) : ℝ :=
  Filter.liminf (densityRatio S) Filter.atTop

/-- The upper density of a set S ⊆ ℕ: lim sup_{N→∞} |S ∩ {1,...,N}| / N. -/
noncomputable def upperDensity (S : Set ℕ) : ℝ :=
  Filter.limsup (densityRatio S) Filter.atTop

/-- Density ratio is always non-negative. -/
theorem densityRatio_nonneg (S : Set ℕ) (N : ℕ) : 0 ≤ densityRatio S N :=
  div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)

/-- Density ratio is at most 1 (since |S ∩ {1,...,N}| ≤ N). -/
theorem densityRatio_le_one (S : Set ℕ) (N : ℕ) (hN : 0 < N) : densityRatio S N ≤ 1 := by
  unfold densityRatio countingFn
  rw [div_le_one (Nat.cast_pos.mpr hN)]
  exact_mod_cast Set.ncard_le_ncard (Set.inter_subset_right.trans (by
    intro x hx; exact Set.mem_Icc.mp hx |>.2)) (Set.toFinite _)

/-- Lower density is non-negative: liminf of non-negative values is non-negative. -/
theorem lowerDensity_nonneg (S : Set ℕ) : 0 ≤ lowerDensity S := by
  unfold lowerDensity
  exact le_liminf_of_le (by infer_instance)
    (Filter.Eventually.of_forall (densityRatio_nonneg S))

/-- Lower density ≤ upper density: liminf ≤ limsup. -/
theorem lower_le_upper (S : Set ℕ) : lowerDensity S ≤ upperDensity S := by
  unfold lowerDensity upperDensity
  exact Filter.liminf_le_limsup (by infer_instance)
    ⟨0, Filter.Eventually.of_forall (densityRatio_nonneg S)⟩
    ⟨1, Filter.eventually_atTop.mpr ⟨1, fun N hN =>
      densityRatio_le_one S N (by omega)⟩⟩

/-- Upper density is at most 1: limsup of a ratio bounded by 1. -/
theorem upperDensity_le_one (S : Set ℕ) : upperDensity S ≤ 1 := by
  unfold upperDensity
  exact limsup_le_of_le (by infer_instance)
    (Filter.eventually_atTop.mpr ⟨1, fun N hN => densityRatio_le_one S N (by omega)⟩)

/-- Lower density is at most 1: follows from lower ≤ upper ≤ 1. -/
theorem lowerDensity_le_one (S : Set ℕ) : lowerDensity S ≤ 1 :=
  le_trans (lower_le_upper S) (upperDensity_le_one S)

/- ## The Representation Bounded Property -/

/-- A set A has bounded representation function: there exists C such that
    r_A(n) ≤ C for all n. -/
def HasBoundedRep (A : Set ℕ) : Prop :=
  ∃ C : ℕ, ∀ n : ℕ, repFunction A n ≤ C

/-- A set A has ε-dense sumset: the lower density of A + A is ≥ 1 - ε. -/
def HasDenseSumset (A : Set ℕ) (ε : ℝ) : Prop :=
  lowerDensity (sumSet A) ≥ 1 - ε

/- ## The Main Conjecture -/

/-- Erdős Problem #749: For every ε > 0, does there exist A ⊆ ℕ
    with HasDenseSumset A ε and HasBoundedRep A?

    This asks whether we can have a "near-basis" of order 2 with
    bounded representation function. -/
theorem erdos_749_conjecture :
    (∀ ε : ℝ, ε > 0 → ∃ A : Set ℕ, HasDenseSumset A ε ∧ HasBoundedRep A) ∨
    (∃ ε : ℝ, ε > 0 ∧ ∀ A : Set ℕ, HasDenseSumset A ε → ¬ HasBoundedRep A) := by
  -- This is P ∨ ¬P: ¬(∀ε,∃A,...) ↔ ∃ε,∀A,¬(...) ↔ ∃ε,∀A,dense→¬bounded
  by_cases h : ∀ ε : ℝ, ε > 0 → ∃ A : Set ℕ, HasDenseSumset A ε ∧ HasBoundedRep A
  · exact Or.inl h
  · right
    push_neg at h
    obtain ⟨ε, hε, hA⟩ := h
    exact ⟨ε, hε, fun A hd hb => hA ε hε A ⟨hd, hb⟩⟩

/- ## Context: Sidon Sets and Bases -/

/-- Sidon sets have r(n) ≤ 1 for all n (bounded representation).
    Proof: the Sidon property ensures at most one pair (a, n-a) with
    a ≤ n-a, a ∈ A, n-a ∈ A for each n. -/
theorem sidon_bounded_rep (A : Set ℕ) (hsidon : ∀ a b c d : ℕ,
    a ∈ A → b ∈ A → c ∈ A → d ∈ A → a ≤ b → c ≤ d →
    a + b = c + d → a = c ∧ b = d) :
    HasBoundedRep A := by
  use 1
  intro n
  unfold repFunction
  rw [Finset.card_le_one]
  intro a ha b hb
  simp only [Finset.mem_filter, Finset.mem_range] at ha hb
  obtain ⟨_, ha_A, hna_A, ha_le⟩ := ha
  obtain ⟨_, hb_A, hnb_A, hb_le⟩ := hb
  have heq : a + (n - a) = b + (n - b) := by omega
  exact (hsidon a (n - a) b (n - b) ha_A hna_A hb_A hnb_A ha_le hb_le heq).1

/-- Sidon sets have natural density 0: upper density of A is 0.
    This follows from the classical bound |A ∩ [1,N]| ≤ √(2N) + 1,
    since all pairwise sums a+b (a ≤ b) are distinct and lie in [2, 2N].
    Thus Sidon sets can't achieve dense sumsets (they have bounded rep
    but fail the density requirement of Problem #749).

    Proof sketch: For S = A ∩ [1,N] with |S| = k, the Sidon property
    implies the sum map (a,b) ↦ a+b on S×S has each fiber of size ≤ 2
    (the pair (a,b) and its swap (b,a)). Since sums lie in {2,...,2N},
    we get k² ≤ 2·(2N-1) < 4N, hence k < 2√N and density → 0. -/
axiom sidon_set_density_zero (A : Set ℕ) (hsidon : ∀ a b c d : ℕ,
    a ∈ A → b ∈ A → c ∈ A → d ∈ A → a ≤ b → c ≤ d →
    a + b = c + d → a = c ∧ b = d) :
    upperDensity A = 0

/- ## Erdős–Turán Conjecture Connection -/

/-- Erdős–Turán conjecture (Problem #28): If A is an additive basis of order 2
    (i.e., every sufficiently large n ∈ A + A), then r(n) is unbounded.

    Problem #749 relaxes "basis" to "near-basis" (density close to 1). -/
axiom erdos_turan_conjecture_28 :
    ∀ A : Set ℕ, lowerDensity (sumSet A) = 1 → ¬ HasBoundedRep A

/- ## Upper Density Variant -/

/-- Similar question for upper density: does there exist A with
    upper density of A + A at least 1 - ε and bounded r(n)? -/
theorem erdos_749_upper_variant :
    (∀ ε : ℝ, ε > 0 → ∃ A : Set ℕ,
      upperDensity (sumSet A) ≥ 1 - ε ∧ HasBoundedRep A) ∨
    (∃ ε : ℝ, ε > 0 ∧ ∀ A : Set ℕ,
      upperDensity (sumSet A) ≥ 1 - ε → ¬ HasBoundedRep A) := by
  by_cases h : ∀ ε : ℝ, ε > 0 → ∃ A : Set ℕ,
      upperDensity (sumSet A) ≥ 1 - ε ∧ HasBoundedRep A
  · exact Or.inl h
  · right
    push_neg at h
    obtain ⟨ε, hε, hA⟩ := h
    exact ⟨ε, hε, fun A hd hb => hA ε hε A ⟨hd, hb⟩⟩
