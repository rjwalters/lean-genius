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

/- ## Known Results -/

/-- **Adenwalla Lower Bound**: c(N) ≥ (1 − 1/e + o(1))N.
    Construction: take B ⊆ [(1/e − o(1))N, N] with Σ_{b ∈ B} 1/b = 1,
    set A = B ∪ {1} with δ(1) = 1, δ(b) = −1. -/
axiom adenwalla_lower_bound :
  ∀ ε : ℝ, ε > 0 →
    ∃ N₀ : ℕ, ∀ N ≥ N₀,
      (maxIrreducibleSize N : ℝ) ≥ (1 - 1 / Real.exp 1 - ε) * N

/- ## Main Conjecture -/

/-- **Erdős Problem #319**: c(N) ≥ (1 − 1/e + o(1))N.
    This follows directly from the Adenwalla lower bound (which is a known result,
    not a conjecture). The full problem asks for the exact asymptotic of c(N). -/
theorem erdos_319_conjecture :
    ∀ ε : ℝ, ε > 0 →
      ∃ N₀ : ℕ, ∀ N ≥ N₀,
        (maxIrreducibleSize N : ℝ) ≥ (1 - 1 / Real.exp 1 - ε) * N :=
  adenwalla_lower_bound

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

/-- **PROVED** (was axiom): A = {2, 3, 6} with δ(2) = −1, δ(3) = δ(6) = 1 gives
    −1/2 + 1/3 + 1/6 = 0, and every proper non-empty subset sums to
    ±1/6, ±1/3, or ±1/2 (all non-zero). -/
theorem small_example :
    ∃ A : Finset ℕ, ∃ δ : ℕ → Int,
      A ⊆ Finset.Icc 1 6 ∧ IsIrreducibleZeroSum A δ := by
  refine ⟨{2, 3, 6}, fun n => if n = 2 then -1 else 1, ?_, ?_, ?_, ?_⟩
  -- (1) A ⊆ Icc 1 6
  · intro n hn
    simp only [Finset.mem_insert, Finset.mem_singleton] at hn
    rcases hn with rfl | rfl | rfl <;> simp [Finset.mem_Icc] <;> omega
  -- (2) IsSigning: all δ values are ±1
  · intro n hn
    simp only [Finset.mem_insert, Finset.mem_singleton] at hn
    rcases hn with rfl | rfl | rfl <;> simp
  -- (3) signedSum = 0: −1/2 + 1/3 + 1/6 = 0
  · unfold signedSum
    simp only [Finset.sum_insert (show (2 : ℕ) ∉ ({3, 6} : Finset ℕ) from by decide),
               Finset.sum_insert (show (3 : ℕ) ∉ ({6} : Finset ℕ) from by decide),
               Finset.sum_singleton]
    push_cast; norm_num
  -- (4) Irreducibility: no proper non-empty subset sums to zero
  · intro A' hss hne
    have hmem : ∀ x ∈ A', x = 2 ∨ x = 3 ∨ x = 6 := fun x hx => by
      have := hss.1 hx; simp only [Finset.mem_insert, Finset.mem_singleton] at this; exact this
    by_cases h2 : 2 ∈ A' <;> by_cases h3 : 3 ∈ A' <;> by_cases h6 : 6 ∈ A'
    -- {2,3,6}: full set, contradicts proper subset
    · exfalso; exact hss.not_subset fun x hx => by
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with rfl | rfl | rfl <;> assumption
    -- {2,3}: sum = −1/6 ≠ 0
    · have hA' : A' = {2, 3} := le_antisymm
        (fun x hx => by
          simp only [Finset.mem_insert, Finset.mem_singleton]
          rcases hmem x hx with rfl | rfl | rfl
          · left; rfl; · right; rfl; · contradiction)
        (fun x hx => by
          simp only [Finset.mem_insert, Finset.mem_singleton] at hx
          rcases hx with rfl | rfl <;> assumption)
      rw [hA']; unfold signedSum
      simp only [Finset.sum_insert (show (2 : ℕ) ∉ ({3} : Finset ℕ) from by decide),
                 Finset.sum_singleton]
      push_cast; norm_num
    -- {2,6}: sum = −1/3 ≠ 0
    · have hA' : A' = {2, 6} := le_antisymm
        (fun x hx => by
          simp only [Finset.mem_insert, Finset.mem_singleton]
          rcases hmem x hx with rfl | rfl | rfl
          · left; rfl; · contradiction; · right; rfl)
        (fun x hx => by
          simp only [Finset.mem_insert, Finset.mem_singleton] at hx
          rcases hx with rfl | rfl <;> assumption)
      rw [hA']; unfold signedSum
      simp only [Finset.sum_insert (show (2 : ℕ) ∉ ({6} : Finset ℕ) from by decide),
                 Finset.sum_singleton]
      push_cast; norm_num
    -- {2}: sum = −1/2 ≠ 0
    · have hA' : A' = {2} := le_antisymm
        (fun x hx => by
          simp only [Finset.mem_singleton]
          rcases hmem x hx with rfl | rfl | rfl
          · rfl; · contradiction; · contradiction)
        (Finset.singleton_subset_iff.mpr h2)
      rw [hA']; unfold signedSum; simp only [Finset.sum_singleton]
      push_cast; norm_num
    -- {3,6}: sum = 1/2 ≠ 0
    · have hA' : A' = {3, 6} := le_antisymm
        (fun x hx => by
          simp only [Finset.mem_insert, Finset.mem_singleton]
          rcases hmem x hx with rfl | rfl | rfl
          · contradiction; · left; rfl; · right; rfl)
        (fun x hx => by
          simp only [Finset.mem_insert, Finset.mem_singleton] at hx
          rcases hx with rfl | rfl <;> assumption)
      rw [hA']; unfold signedSum
      simp only [Finset.sum_insert (show (3 : ℕ) ∉ ({6} : Finset ℕ) from by decide),
                 Finset.sum_singleton]
      push_cast; norm_num
    -- {3}: sum = 1/3 ≠ 0
    · have hA' : A' = {3} := le_antisymm
        (fun x hx => by
          simp only [Finset.mem_singleton]
          rcases hmem x hx with rfl | rfl | rfl
          · contradiction; · rfl; · contradiction)
        (Finset.singleton_subset_iff.mpr h3)
      rw [hA']; unfold signedSum; simp only [Finset.sum_singleton]
      push_cast; norm_num
    -- {6}: sum = 1/6 ≠ 0
    · have hA' : A' = {6} := le_antisymm
        (fun x hx => by
          simp only [Finset.mem_singleton]
          rcases hmem x hx with rfl | rfl | rfl
          · contradiction; · contradiction; · rfl)
        (Finset.singleton_subset_iff.mpr h6)
      rw [hA']; unfold signedSum; simp only [Finset.sum_singleton]
      push_cast; norm_num
    -- ∅: contradicts A'.Nonempty
    · obtain ⟨x, hx⟩ := hne
      rcases hmem x hx with rfl | rfl | rfl <;> contradiction

/- **Connection to Unit Fractions**: the problem is closely related to
    Egyptian fraction representations and signed unit-fraction decompositions.
    Erdős and Graham (1980) posed this in their monograph on such problems. -/
