/-
  Aristotle targets for Erdos840 (Quasi-Sidon Subsets)
  Routine supporting lemmas for automated proof search.
  See Erdos840Problem.lean for the main formalization.

  These lemmas provide building blocks for quasi-Sidon set analysis:
  - IsSidon basic properties (distinct sums, sumset cardinality)
  - IsQuasiSidon structural helpers
  - Sidon set existence bounds
  - Arithmetic for sumset bounds (n*(n+1)/2)
  - sqrt(N) bound arithmetic
-/
import Mathlib

open Finset Real

namespace Erdos840.Aristotle

variable {α : Type*} [DecidableEq α] [AddCommMonoid α]

/-
  ## Section 1: Sumset Arithmetic
-/

/-- n*(n+1)/2 = C(n,2) + n -/
lemma triangular_eq_choose_plus (n : ℕ) : n * (n + 1) / 2 = n.choose 2 + n := by
  sorry -- Nat division arithmetic, leaving for Aristotle

/-- C(n,2) = n*(n-1)/2 for natural numbers -/
lemma choose_two_formula (n : ℕ) : n.choose 2 = n * (n - 1) / 2 := by
  sorry -- Nat division arithmetic, leaving for Aristotle

/-- For A with |A| = k, the number of ordered pairs (a,b) with a ≠ b is k*(k-1) -/
lemma card_ordered_pairs (A : Finset ℕ) :
    ((A ×ˢ A).filter fun p => p.1 ≠ p.2).card = A.card * (A.card - 1) := by
  sorry -- complex finset computation, leaving for Aristotle

/-
  ## Section 2: IsSidon Properties
-/

/-- A Sidon set has all pairwise sums distinct -/
def IsSidon' (A : Finset ℕ) : Prop :=
  ∀ a b c d : ℕ, a ∈ A → b ∈ A → c ∈ A → d ∈ A →
    a + b = c + d → a ≤ b → c ≤ d → (a = c ∧ b = d)

/-- The sumset of a Finset -/
def sumset' (A : Finset ℕ) : Finset ℕ :=
  (A ×ˢ A).image fun p => p.1 + p.2

/-- Sumset contains both singletons and pairwise sums -/
lemma mem_sumset (A : Finset ℕ) (a b : ℕ) (ha : a ∈ A) (hb : b ∈ A) :
    a + b ∈ sumset' A := by
  simp only [sumset', Finset.mem_image, Finset.mem_product]
  exact ⟨(a, b), ⟨ha, hb⟩, rfl⟩

/-- Singleton in A implies 2*a in sumset -/
lemma two_mul_mem_sumset (A : Finset ℕ) (a : ℕ) (ha : a ∈ A) :
    2 * a ∈ sumset' A := by
  rw [two_mul]
  exact mem_sumset A a a ha ha

/-- For Sidon set, different pairs give different sums -/
lemma sidon_distinct_sums (A : Finset ℕ) (hS : IsSidon' A)
    (a b c d : ℕ) (ha : a ∈ A) (hb : b ∈ A) (hc : c ∈ A) (hd : d ∈ A)
    (hab : a < b) (hcd : c < d) (hne : (a, b) ≠ (c, d)) : a + b ≠ c + d := by
  intro h_eq
  have := hS a b c d ha hb hc hd h_eq hab.le hcd.le
  exact hne (Prod.ext this.1 this.2)

/-
  ## Section 3: Sumset Size Bounds
-/

/-- The number of unordered pairs from A is C(|A|, 2) -/
lemma unordered_pairs_card (A : Finset ℕ) :
    ((A ×ˢ A).filter fun p => p.1 < p.2).card = A.card.choose 2 := by
  sorry -- needs careful finset biijection argument

/-- Sumset is nonempty when A is nonempty -/
lemma sumset_nonempty (A : Finset ℕ) (hA : A.Nonempty) : (sumset' A).Nonempty := by
  obtain ⟨a, ha⟩ := hA
  exact ⟨a + a, mem_sumset A a a ha ha⟩

/-- Sumset card ≥ |A| (the diagonal 2*a are all distinct for distinct a) -/
lemma sumset_card_ge (A : Finset ℕ) : (sumset' A).card ≥ A.card := by
  calc A.card = (A.image (fun a => 2 * a)).card :=
        (Finset.card_image_of_injective A (fun a b h => by omega)).symm
    _ ≤ (sumset' A).card := Finset.card_le_card (fun x hx => by
        simp only [Finset.mem_image] at hx
        obtain ⟨a, ha, rfl⟩ := hx
        rw [two_mul]
        simp only [sumset', Finset.mem_image, Finset.mem_product]
        exact ⟨(a, a), ⟨ha, ha⟩, rfl⟩)

/-
  ## Section 4: sqrt(N) Arithmetic
-/

/-- (sqrt N)^2 ≤ N -/
lemma sqrt_sq_le (N : ℕ) : (Nat.sqrt N) ^ 2 ≤ N :=
  Nat.sqrt_le' N

/-- sqrt N ≤ N for N ≥ 1 -/
lemma sqrt_le_self (N : ℕ) (hN : N ≥ 1) : Real.sqrt N ≤ N := by
  have hN' : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have h : Real.sqrt N ≤ Real.sqrt (N ^ 2) := Real.sqrt_le_sqrt (by nlinarith)
  rwa [Real.sqrt_sq hN'] at h

/-- sqrt 3 < 2 -/
lemma sqrt3_lt_two : Real.sqrt 3 < 2 := by
  rw [show (2 : ℝ) = Real.sqrt 4 by
    rw [show (4 : ℝ) = 2^2 by norm_num, Real.sqrt_sq (by norm_num)]]
  exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)

/-- 2 / sqrt 3 > 1 -/
lemma two_div_sqrt3_gt_one : 2 / Real.sqrt 3 > 1 := by
  have h3 : (0 : ℝ) < Real.sqrt 3 := Real.sqrt_pos.mpr (by norm_num)
  rw [gt_iff_lt, ← sub_pos]
  have heq : (2 : ℝ) / Real.sqrt 3 - 1 = (2 - Real.sqrt 3) / Real.sqrt 3 := by
    field_simp [h3.ne']
  rw [heq]
  apply div_pos
  · linarith [sqrt3_lt_two]
  · exact h3

/-- Sidon set cardinality bound: |A| ≤ sqrt N + O(1) for A ⊆ {1..N} -/
lemma sidon_card_le_sqrt (A : Finset ℕ) (N : ℕ) (hN : N ≥ 1)
    (hA : ∀ a ∈ A, a ≤ N) (hS : IsSidon' A) :
    (A.card : ℝ) ≤ Real.sqrt N + 1 := by
  sorry -- classic Sidon bound: differences argument gives k(k-1) ≤ 2N, so k ≤ sqrt(2N)+1

end Erdos840.Aristotle
