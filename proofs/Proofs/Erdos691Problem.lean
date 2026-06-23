/- Erdős Problem #691 — Behrend Sequences and Density of Multiples

Given A ⊆ ℕ, let M_A = {n ≥ 1 : a | n for some a ∈ A} be the set of
multiples of A. A sequence A is called a **Behrend sequence** if M_A
has asymptotic density 1.

Erdős asked: Find a necessary and sufficient condition on A for M_A
to have density 1.

Known results:
- For pairwise coprime A (no 1): A is Behrend iff Σ 1/a = ∞
- Tenenbaum (1996): For lacunary block sequences with η_k = k^{−β},
  Behrend iff β < log 2

Reference: https://erdosproblems.com/691
-/

import Mathlib.Data.Nat.Basic
import Mathlib.Data.Set.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Real.Basic
import Mathlib.Order.Filter.AtTopBot
import Mathlib.Tactic

open Finset Set Filter

namespace Erdos691

/- ## Part I: Density Infrastructure -/

/-- The counting function: |{a ∈ S : a ≤ n}|. -/
noncomputable def countingFunction (S : Set ℕ) (n : ℕ) : ℕ :=
  (Finset.range (n + 1)).filter (· ∈ S) |>.card

/-- Upper density: limsup of |S ∩ [0,n]| / n. -/
noncomputable def upperDensity (S : Set ℕ) : ℝ :=
  limsup (fun n => (countingFunction S n : ℝ) / n) atTop

/-- Lower density: liminf of |S ∩ [0,n]| / n. -/
noncomputable def lowerDensity (S : Set ℕ) : ℝ :=
  liminf (fun n => (countingFunction S n : ℝ) / n) atTop

/-- S has natural (asymptotic) density d. -/
def HasDensity (S : Set ℕ) (d : ℝ) : Prop :=
  Filter.Tendsto (fun n => (countingFunction S n : ℝ) / (n : ℝ)) atTop (nhds d)

/-- S has density 1. -/
def HasDensityOne (S : Set ℕ) : Prop := HasDensity S 1

/- ## Part II: Set of Multiples -/

/-- The set of multiples of A: all positive n divisible by some a ∈ A. -/
def multiplesOf (A : Set ℕ) : Set ℕ :=
  {n | 0 < n ∧ ∃ a ∈ A, a ∣ n}

/-- A is a Behrend sequence: the set of its multiples has density 1. -/
def IsBehrend (A : Set ℕ) : Prop :=
  HasDensityOne (multiplesOf A)

/- ## Part III: Basic Structural Lemmas -/

/-- Membership in multiplesOf: n ∈ M_A iff n > 0 and some a ∈ A divides n. -/
theorem mem_multiplesOf (A : Set ℕ) (n : ℕ) :
    n ∈ multiplesOf A ↔ (0 < n ∧ ∃ a ∈ A, a ∣ n) := by
  rfl

/-- If A ⊆ B then M_A ⊆ M_B (monotonicity of multiples). -/
theorem multiplesOf_mono {A B : Set ℕ} (h : A ⊆ B) :
    multiplesOf A ⊆ multiplesOf B := by
  intro n hn
  obtain ⟨hpos, a, haA, hdvd⟩ := hn
  exact ⟨hpos, a, h haA, hdvd⟩

/-- M_∅ = ∅ (no multiples of the empty set). -/
theorem multiplesOf_empty : multiplesOf ∅ = ∅ := by
  ext n
  simp [multiplesOf]

/-- Every element of A is in M_A (if positive). -/
theorem self_mem_multiplesOf {A : Set ℕ} {a : ℕ} (ha : a ∈ A) (hpos : 0 < a) :
    a ∈ multiplesOf A :=
  ⟨hpos, a, ha, dvd_refl a⟩

/-- For any a ∈ A with a > 0, every positive multiple of a is in M_A. -/
theorem mul_mem_multiplesOf {A : Set ℕ} {a : ℕ} (ha : a ∈ A) (hpos : 0 < a)
    {k : ℕ} (hk : 0 < k) : k * a ∈ multiplesOf A :=
  ⟨Nat.mul_pos hk hpos, a, ha, dvd_mul_left a k⟩

/-- M_A is closed upward under taking multiples: if n ∈ M_A and k > 0
    then k * n ∈ M_A. -/
theorem multiplesOf_mul_closed {A : Set ℕ} {n : ℕ} (hn : n ∈ multiplesOf A)
    {k : ℕ} (hk : 0 < k) : k * n ∈ multiplesOf A := by
  obtain ⟨hpos, a, haA, hdvd⟩ := hn
  exact ⟨Nat.mul_pos hk hpos, a, haA, dvd_trans hdvd (dvd_mul_left n k)⟩

/-- M_{A ∪ B} = M_A ∪ M_B (multiples of union is union of multiples). -/
theorem multiplesOf_union (A B : Set ℕ) :
    multiplesOf (A ∪ B) = multiplesOf A ∪ multiplesOf B := by
  ext n
  simp only [multiplesOf, Set.mem_setOf_eq, Set.mem_union]
  constructor
  · rintro ⟨hpos, a, haAB, hdvd⟩
    cases haAB with
    | inl haA => left; exact ⟨hpos, a, haA, hdvd⟩
    | inr haB => right; exact ⟨hpos, a, haB, hdvd⟩
  · rintro (⟨hpos, a, haA, hdvd⟩ | ⟨hpos, a, haB, hdvd⟩)
    · exact ⟨hpos, a, Or.inl haA, hdvd⟩
    · exact ⟨hpos, a, Or.inr haB, hdvd⟩

/-- Counting function is monotone for subsets. -/
theorem countingFunction_mono {A B : Set ℕ} (h : A ⊆ B) (n : ℕ) :
    countingFunction A n ≤ countingFunction B n := by
  apply Finset.card_le_card
  exact Finset.filter_subset_filter _ (fun x hx => h hx)

/-- Counting function is bounded by n + 1 (at most n+1 elements in [0..n]). -/
theorem countingFunction_le (S : Set ℕ) (n : ℕ) :
    countingFunction S n ≤ n + 1 := by
  unfold countingFunction
  exact Finset.card_filter_le _ _

/- ## Part IV: Pairwise Coprime Characterization -/

/-- A set is pairwise coprime with all elements > 1. -/
def IsPairwiseCoprime (A : Set ℕ) : Prop :=
  (∀ a ∈ A, 1 < a) ∧
  (∀ a ∈ A, ∀ b ∈ A, a ≠ b → Nat.Coprime a b)

/-- The reciprocal sum of A diverges: for every C > 0, there exists a
    finite subset S ⊆ A with Σ_{a ∈ S} 1/a ≥ C. -/
def HasDivergentReciprocalSum (A : Set ℕ) : Prop :=
  ∀ C : ℝ, 0 < C → ∃ (S : Finset ℕ), ↑S ⊆ A ∧
    C ≤ S.sum (fun a => (1 : ℝ) / (a : ℝ))

/-- For pairwise coprime A: Behrend iff Σ 1/a = ∞.
    This is a classical result in multiplicative number theory. -/
/-- The set of all primes is Behrend (since Σ 1/p = ∞). -/
/- ## Part V: Block Sequences and Tenenbaum's Theorem -/

/-- A lacunary sequence with bounded ratios:
    there exist 1 < C₁ < C₂ with C₁ ≤ n_{i+1}/n_i ≤ C₂ for all i. -/
def IsLacunaryBounded (n : ℕ → ℕ) (C₁ C₂ : ℝ) : Prop :=
  1 < C₁ ∧ C₁ < C₂ ∧
  (∀ i, C₁ ≤ (n (i + 1) : ℝ) / (n i : ℝ)) ∧
  (∀ i, (n (i + 1) : ℝ) / (n i : ℝ) ≤ C₂)

/-- A block sequence associated to (nₖ, ηₖ):
    A = ∪_k { m ∈ ℕ : nₖ < m ≤ (1 + ηₖ) · nₖ }. -/
def IsBlockSequence (A : Set ℕ) (n : ℕ → ℕ) (η : ℕ → ℝ) : Prop :=
  ∀ m : ℕ, m ∈ A ↔
    ∃ k : ℕ, (n k : ℝ) < (m : ℝ) ∧ (m : ℝ) ≤ (1 + η k) * (n k : ℝ)

/-- If Σ ηₖ < ∞ (converges), the block sequence is NOT Behrend. -/
/-- **Tenenbaum's Theorem (1996)**: For lacunary block sequences with bounded
    ratios and ηₖ = k^{−β}:
    - β < log 2 implies A is Behrend
    - β > log 2 implies A is not Behrend

    The threshold is β₀ = log 2.
    Reference: Tenenbaum, G., "On block Behrend sequences",
    Math. Proc. Cambridge Philos. Soc. (1996), 355-367. -/
/- ## Part VI: The Erdős Problem (Open) -/

/-- Erdős Problem 691: Find a necessary and sufficient condition for
    A to be a Behrend sequence.

    The general characterization remains OPEN. Known partial results:
    1. Coprime case: Behrend iff Σ 1/a diverges
    2. Lacunary block case: threshold at β = log 2 (Tenenbaum 1996)

    The problem asks for a unifying condition that subsumes both. -/
end Erdos691
