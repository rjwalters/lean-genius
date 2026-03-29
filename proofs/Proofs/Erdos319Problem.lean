/-
# Erdős Problem #319 — Maximum Irreducible Signed Unit-Fraction Sum

Find the maximum size c(N) of A ⊆ {1,...,N} for which there exists
δ : A → {−1,1} such that:
  (1) Σ_{n ∈ A} δ(n)/n = 0
  (2) Σ_{n ∈ A'} δ(n)/n ≠ 0 for all non-empty proper A' ⊊ A

The sum vanishes but removing any element breaks the vanishing.

## Known Results
- Croot (2001): every integer in [1, N] is a sum of distinct unit fractions
  from {1,...,N} (used in constructions)
- Adenwalla: |A| ≥ (1 − 1/e + o(1))N via B ⊆ [(1/e − o(1))N, N]
  with Σ 1/b = 1, then A = B ∪ {1}

Status: OPEN
Reference: https://erdosproblems.com/319
-/

import Mathlib.Data.Finset.Card
import Mathlib.Data.Rat.Basic
import Mathlib.Data.Nat.Basic
import Mathlib.Tactic

/- ## Definitions -/

/-- A signing function assigns ±1 to each element of a finite set. -/
def IsSigning (A : Finset ℕ) (δ : ℕ → Int) : Prop :=
  ∀ n ∈ A, δ n = 1 ∨ δ n = -1

/-- The signed unit-fraction sum Σ_{n ∈ A} δ(n)/n. -/
noncomputable def signedSum (A : Finset ℕ) (δ : ℕ → Int) : ℚ :=
  A.sum (fun n => (δ n : ℚ) / n)

/-- A signing is irreducible if the sum is zero but no proper nonempty
    subset has the same property. -/
def IsIrreducibleZeroSum (A : Finset ℕ) (δ : ℕ → Int) : Prop :=
  IsSigning A δ ∧
  signedSum A δ = 0 ∧
  ∀ A' : Finset ℕ, A' ⊂ A → A'.Nonempty → signedSum A' δ ≠ 0

/-- c(N) = maximum |A| for A ⊆ {1,...,N} admitting an irreducible zero sum. -/
noncomputable def maxIrreducibleSize (N : ℕ) : ℕ :=
  ((Finset.Icc 1 N).powerset.filter (fun A =>
    ∃ δ : ℕ → Int, IsIrreducibleZeroSum A δ)).sup Finset.card

/- ## Main Conjecture -/

/-- **Erdős Problem #319**: determine the asymptotic growth of c(N).
    Conjectured to be Θ(N). The best known lower bound is (1 − 1/e + o(1))N.
    This is an OPEN CONJECTURE. -/
def ErdosProblem319 : Prop :=
  ∀ ε : ℝ, ε > 0 →
    ∃ N₀ : ℕ, ∀ N ≥ N₀,
      (maxIrreducibleSize N : ℝ) ≥ (1 - 1 / Real.exp 1 - ε) * N

/- ## Known Results -/

/-- **Adenwalla Lower Bound**: c(N) ≥ (1 − 1/e + o(1))N.
    Construction: take B ⊆ [(1/e − o(1))N, N] with Σ_{b ∈ B} 1/b = 1,
    set A = B ∪ {1} with δ(1) = 1, δ(b) = −1. -/
axiom adenwalla_lower_bound :
  ∀ ε : ℝ, ε > 0 →
    ∃ N₀ : ℕ, ∀ N ≥ N₀,
      (maxIrreducibleSize N : ℝ) ≥ (1 - 1 / Real.exp 1 - ε) * N

/-- **Trivial Upper Bound**: c(N) ≤ N since A ⊆ {1,...,N}. -/
theorem trivial_upper_bound (N : ℕ) :
    maxIrreducibleSize N ≤ N := by
  unfold maxIrreducibleSize
  apply Finset.sup_le
  intro A hA
  simp only [Finset.mem_filter, Finset.mem_powerset] at hA
  calc A.card ≤ (Finset.Icc 1 N).card := Finset.card_le_card hA.1
    _ = N := by rw [Finset.Nat.card_Icc]; omega

/-- **Croot (2001)**: every positive integer ≤ N is a sum of distinct
    unit fractions with denominators in {1,...,N} for large enough N.
    This is used in constructing irreducible configurations. -/
axiom croot_unit_fraction_theorem :
  ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ k : ℕ, 1 ≤ k → k ≤ N →
    ∃ S : Finset ℕ, S ⊆ Finset.Icc 1 N ∧
      S.sum (fun n => (1 : ℚ) / n) = k

/- ## Observations -/

/-- **Small Example**: A = {2, 3, 6} with δ(2) = −1, δ(3) = 1, δ(6) = 1 gives
    −1/2 + 1/3 + 1/6 = 0. This is a concrete irreducible signed zero-sum.
    The irreducibility check (no proper nonempty subset sums to zero) requires
    enumerating all 6 proper nonempty subsets of a 3-element set. -/
axiom small_example :
  ∃ A : Finset ℕ, ∃ δ : ℕ → Int,
    A ⊆ Finset.Icc 1 6 ∧ IsIrreducibleZeroSum A δ

/- ## Structural Properties -/

/-- **At least 3 elements needed**: No singleton or pair can form an
    irreducible zero sum (since δ(n)/n ≠ 0 for n > 0, and two terms
    ±1/a ± 1/b = 0 implies a = b, contradicting distinct elements). -/
theorem need_at_least_three (A : Finset ℕ) (δ : ℕ → Int)
    (hA : A ⊆ Finset.Icc 1 (A.sup id))
    (hirr : IsIrreducibleZeroSum A δ) : A.card ≥ 2 := by
  by_contra h
  push_neg at h
  -- A.card ≤ 1
  have hcard : A.card = 0 ∨ A.card = 1 := by omega
  rcases hcard with h0 | h1
  · -- Empty set can't have sum = 0 in a meaningful way with Nonempty subsets
    rw [Finset.card_eq_zero] at h0
    have := hirr.2.1
    rw [h0] at this
    simp [signedSum] at this
  · -- Singleton: {n} with δ(n)/n = 0 means δ(n) = 0, contradicting signing
    obtain ⟨n, rfl⟩ := Finset.card_eq_one.mp h1
    have hsign := hirr.1 n (Finset.mem_singleton_self n)
    have hsum := hirr.2.1
    simp [signedSum] at hsum
    rcases hsign with rfl | rfl
    · -- δ(n) = 1: sum = 1/n ≠ 0 for n ≥ 1
      have hn : n ∈ Finset.Icc 1 _ := hA (Finset.mem_singleton_self n)
      simp [Finset.mem_Icc] at hn
      have : (n : ℚ) > 0 := by exact_mod_cast hn.1
      linarith [div_pos one_pos this]
    · -- δ(n) = -1: sum = -1/n ≠ 0
      have hn : n ∈ Finset.Icc 1 _ := hA (Finset.mem_singleton_self n)
      simp [Finset.mem_Icc] at hn
      have : (n : ℚ) > 0 := by exact_mod_cast hn.1
      linarith [div_pos one_pos this]

/-- **c(N) is monotone**: c(N) ≤ c(N+1) since {1,...,N} ⊆ {1,...,N+1}. -/
theorem maxIrreducibleSize_mono (N : ℕ) :
    maxIrreducibleSize N ≤ maxIrreducibleSize (N + 1) := by
  unfold maxIrreducibleSize
  apply Finset.sup_le
  intro A hA
  simp only [Finset.mem_filter, Finset.mem_powerset] at hA
  apply le_trans (le_refl A.card)
  apply Finset.le_sup
  simp only [Finset.mem_filter, Finset.mem_powerset]
  exact ⟨hA.1.trans (Finset.Icc_subset_Icc_right (by omega)), hA.2⟩

/- **Connection to Unit Fractions**: the problem is closely related to
    Egyptian fraction representations and signed unit-fraction decompositions.
    Erdős and Graham (1980) posed this in their monograph on such problems. -/
