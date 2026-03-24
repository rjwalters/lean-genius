/-
# Erdős Problem #848: Squarefree Products and Extremal Sets

Determine the maximum size of A ⊆ {1,...,N} such that ab + 1 is never
squarefree for all a, b ∈ A (including a = b).

Equivalently: for every a, b ∈ A, there exists a prime p with p² | ab + 1.

The conjectured extremal sets are {n ≡ 7 (mod 25)} and {n ≡ 18 (mod 25)},
each giving |A| ≈ N/25.

Solved by Sawhney for sufficiently large N.

Reference: https://erdosproblems.com/848
-/

import Mathlib.Tactic
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Prime.Basic

/- ## Definitions -/

/-- n is squarefree if no prime squared divides n. -/
def IsSquarefree (n : ℕ) : Prop :=
  ∀ p : ℕ, p.Prime → ¬(p * p ∣ n)

/-- A set A ⊆ {1,...,N} has the non-squarefree product property if
    ab + 1 is not squarefree for all a, b ∈ A. -/
def HasNonSqfreeProductProp (A : Finset ℕ) : Prop :=
  ∀ a ∈ A, ∀ b ∈ A, ¬IsSquarefree (a * b + 1)

/- ## Extremal Function -/

open Classical in
/-- The maximum size of a subset of {1,...,N} with the non-squarefree
    product property. Defined as the supremum over all qualifying subsets. -/
noncomputable def maxNonSqfreeSet (N : ℕ) : ℕ :=
  ((Finset.Icc 1 N).powerset.filter (fun A => HasNonSqfreeProductProp A)).sup Finset.card

/-- The max size is at most N: any qualifying subset of {1,...,N} has ≤ N elements. -/
theorem maxNonSqfreeSet_le (N : ℕ) : maxNonSqfreeSet N ≤ N := by
  classical
  unfold maxNonSqfreeSet
  apply Finset.sup_le
  intro A hA
  simp only [Finset.mem_filter, Finset.mem_powerset] at hA
  -- |A| ≤ |Icc 1 N| ≤ |range N| = N via injection x ↦ x - 1
  calc A.card
      ≤ (Finset.Icc 1 N).card := Finset.card_le_card hA.1
    _ ≤ (Finset.range N).card := by
        apply Finset.card_le_card_of_injOn (· - 1)
        · intro x hx; simp at hx ⊢; omega
        · intro a ha b hb hab; simp at ha hb; dsimp at hab; omega
    _ = N := Finset.card_range N

/- ## Known Results -/

/-- The set {n ∈ {1,...,N} : n ≡ 7 (mod 25)} achieves the property:
    for a ≡ b ≡ 7 (mod 25), ab + 1 ≡ 50 ≡ 0 (mod 25), so 5² | ab + 1. -/
theorem mod25_achieves :
  ∀ a b : ℕ, a % 25 = 7 → b % 25 = 7 →
    5 * 5 ∣ a * b + 1 := by
  intro a b ha hb
  have ha' : a = 25 * (a / 25) + 7 := by omega
  have hb' : b = 25 * (b / 25) + 7 := by omega
  rw [ha', hb']
  exact ⟨25 * (a / 25) * (b / 25) + 7 * (a / 25) + 7 * (b / 25) + 2, by ring⟩

/-- The symmetric case: {n ≡ 18 (mod 25)} also achieves the property.
    For a ≡ b ≡ 18 (mod 25), ab + 1 ≡ 325 ≡ 0 (mod 25), so 5² | ab + 1. -/
theorem mod25_achieves_18 :
  ∀ a b : ℕ, a % 25 = 18 → b % 25 = 18 →
    5 * 5 ∣ a * b + 1 := by
  intro a b ha hb
  have ha' : a = 25 * (a / 25) + 18 := by omega
  have hb' : b = 25 * (b / 25) + 18 := by omega
  rw [ha', hb']
  exact ⟨25 * (a / 25) * (b / 25) + 18 * (a / 25) + 18 * (b / 25) + 13, by ring⟩

/-- 5 is prime — needed to connect 5² | n to ¬IsSquarefree n. -/
theorem five_prime : Nat.Prime 5 := by decide

/-- If 5² | n, then n is not squarefree (by our definition). -/
theorem not_sqfree_of_five_sq_dvd {n : ℕ} (h : 5 * 5 ∣ n) : ¬IsSquarefree n := by
  intro hsf
  exact hsf 5 five_prime h

/-- The mod 7 residue class satisfies the full non-squarefree product property. -/
theorem mod7_set_has_property (A : Finset ℕ) (hA : ∀ a ∈ A, a % 25 = 7) :
    HasNonSqfreeProductProp A := by
  intro a ha b hb
  exact not_sqfree_of_five_sq_dvd (mod25_achieves a b (hA a ha) (hA b hb))

/-- The mod 18 residue class satisfies the full non-squarefree product property. -/
theorem mod18_set_has_property (A : Finset ℕ) (hA : ∀ a ∈ A, a % 25 = 18) :
    HasNonSqfreeProductProp A := by
  intro a ha b hb
  exact not_sqfree_of_five_sq_dvd (mod25_achieves_18 a b (hA a ha) (hA b hb))

/- ## Lower Bound via Witness Construction -/

/-- The mod 7 residue class in {1,...,N}. -/
private def mod7Set (N : ℕ) : Finset ℕ :=
  (Finset.Icc 1 N).filter (fun n => n % 25 = 7)

/-- mod7Set is a subset of Icc 1 N. -/
private lemma mod7Set_sub (N : ℕ) : mod7Set N ⊆ Finset.Icc 1 N :=
  Finset.filter_subset _ _

/-- All elements of mod7Set are ≡ 7 (mod 25). -/
private lemma mod7Set_residue {N n : ℕ} (hn : n ∈ mod7Set N) : n % 25 = 7 := by
  simp only [mod7Set, Finset.mem_filter] at hn
  exact hn.2

/-- mod7Set satisfies HasNonSqfreeProductProp. -/
private lemma mod7Set_prop (N : ℕ) : HasNonSqfreeProductProp (mod7Set N) :=
  mod7_set_has_property (mod7Set N) (fun _ h => mod7Set_residue h)

/-- Key cardinality bound: |{n ∈ {1,...,N} : n ≡ 7 (mod 25)}| ≥ N/25.
    Proof via injection: k ↦ 25k + 7 maps {0,...,N/25-1} into mod7Set. -/
private lemma mod7Set_card_ge (N : ℕ) (hN : 25 ≤ N) : N / 25 ≤ (mod7Set N).card := by
  -- Define the injection k ↦ 25k + 7
  set f : ℕ → ℕ := fun k => 25 * k + 7 with hf_def
  -- Image of {0,...,N/25-1} under f lands in mod7Set N
  have hf_mem : ∀ k, k ∈ Finset.range (N / 25) → f k ∈ mod7Set N := by
    intro k hk
    simp only [Finset.mem_range] at hk
    simp only [mod7Set, Finset.mem_filter, Finset.mem_Icc, hf_def]
    refine ⟨⟨by omega, ?_⟩, by omega⟩
    have := Nat.div_mul_le_self N 25
    omega
  -- f is injective on Finset.range (N / 25)
  have hf_inj : Set.InjOn f (Finset.range (N / 25) : Set ℕ) := by
    intro a _ b _ hab
    simp only [hf_def] at hab
    omega
  -- Conclude via card comparison
  calc N / 25 = (Finset.range (N / 25)).card := (Finset.card_range _).symm
    _ ≤ (mod7Set N).card := Finset.card_le_card_of_injOn f hf_mem hf_inj

/-- Lower bound: maxNonSqfreeSet(N) ≥ ⌊N/25⌋ for N ≥ 25.
    Proved by exhibiting the mod 7 residue class as a witness. -/
theorem lower_bound (N : ℕ) (hN : 25 ≤ N) :
    N / 25 ≤ maxNonSqfreeSet N := by
  classical
  unfold maxNonSqfreeSet
  -- mod7Set N is in the filtered powerset
  have hmem : mod7Set N ∈
      (Finset.Icc 1 N).powerset.filter (fun A => HasNonSqfreeProductProp A) := by
    rw [Finset.mem_filter]
    exact ⟨Finset.mem_powerset.mpr (mod7Set_sub N), mod7Set_prop N⟩
  calc N / 25 ≤ (mod7Set N).card := mod7Set_card_ge N hN
    _ ≤ _ := Finset.le_sup hmem

/- ## Structural Results -/

/-- Self-condition: every element of a valid set must have a²+1 not squarefree.
    This follows immediately from the property with a = b. -/
theorem self_condition (A : Finset ℕ) (h : HasNonSqfreeProductProp A)
    (a : ℕ) (ha : a ∈ A) : ¬IsSquarefree (a * a + 1) :=
  h a ha a ha

/-- 4 never divides a²+1 for any natural number a.
    This means p = 2 can never provide the p² factor needed for non-squarefreeness.
    Proof: a² ≡ 0 or 1 (mod 4), so a²+1 ≡ 1 or 2 (mod 4). -/
theorem no_four_dvd_sq_plus_one (a : ℕ) : ¬(2 * 2 ∣ a * a + 1) := by
  intro ⟨k, hk⟩
  rcases Nat.even_or_odd a with ⟨m, rfl⟩ | ⟨m, rfl⟩
  · -- a = m + m: (m+m)²+1 = 4m²+1 ≡ 1 (mod 4)
    have : (m + m) * (m + m) + 1 = 4 * (m * m) + 1 := by ring
    rw [this] at hk; omega
  · -- a = 2m+1: (2m+1)²+1 = 4m²+4m+2 ≡ 2 (mod 4)
    have : (2 * m + 1) * (2 * m + 1) + 1 = 4 * (m * m + m) + 2 := by ring
    rw [this] at hk; omega

/-- 9 never divides a²+1 for any natural number a.
    This means p = 3 can never provide the p² factor.
    Proof: a² mod 3 ∈ {0, 1}, so a²+1 mod 3 ∈ {1, 2}, hence 3 ∤ a²+1, so 9 ∤ a²+1. -/
theorem no_nine_dvd_sq_plus_one (a : ℕ) : ¬(3 * 3 ∣ a * a + 1) := by
  intro ⟨k, hk⟩
  have : a % 3 = 0 ∨ a % 3 = 1 ∨ a % 3 = 2 := by omega
  rcases this with h | h | h
  all_goals (
    have ha : a = 3 * (a / 3) + a % 3 := (Nat.div_add_mod a 3).symm
    rw [h] at ha; rw [ha] at hk; set q := a / 3 with hq_def)
  · -- a ≡ 0: 9q²+1 = 9k
    have : (3 * q + 0) * (3 * q + 0) + 1 = 9 * (q * q) + 1 := by ring
    rw [this] at hk; omega
  · -- a ≡ 1: 9q²+6q+2 = 9k
    have : (3 * q + 1) * (3 * q + 1) + 1 = 9 * (q * q) + 6 * q + 2 := by ring
    rw [this] at hk; omega
  · -- a ≡ 2: 9q²+12q+5 = 9k
    have : (3 * q + 2) * (3 * q + 2) + 1 = 9 * (q * q) + 12 * q + 5 := by ring
    rw [this] at hk; omega

/-- Mixing elements from {7 mod 25} and {18 mod 25}: 5² does NOT divide ab+1.
    This shows the two extremal classes are incompatible via the 5² mechanism,
    a key step toward understanding why extremal sets must be homogeneous. -/
theorem mod25_incompatible (a b : ℕ) (ha : a % 25 = 7) (hb : b % 25 = 18) :
    ¬(5 * 5 ∣ a * b + 1) := by
  intro ⟨k, hk⟩
  have ha' : a = 25 * (a / 25) + 7 := by omega
  have hb' : b = 25 * (b / 25) + 18 := by omega
  rw [ha', hb'] at hk
  have : (25 * (a / 25) + 7) * (25 * (b / 25) + 18) + 1 =
         25 * (25 * (a / 25) * (b / 25) + 18 * (a / 25) + 7 * (b / 25) + 5) + 2 := by ring
  rw [this] at hk
  omega

/-- Complete characterization: 25 divides a²+1 if and only if a ≡ 7 or 18 (mod 25).
    These are the two square roots of -1 in ℤ/25ℤ, since 7² = 49 ≡ -1 and 18² = 324 ≡ -1 (mod 25).
    This establishes that the mod-25 residue classes are the ONLY way to use p = 5. -/
theorem mod25_characterization (a : ℕ) :
    5 * 5 ∣ (a * a + 1) ↔ (a % 25 = 7 ∨ a % 25 = 18) := by
  constructor
  · -- Forward: 25 | a²+1 → a ≡ 7 or 18 (mod 25)
    intro ⟨k, hk⟩
    have ha : a = 25 * (a / 25) + a % 25 := (Nat.div_add_mod a 25).symm
    have hr : a % 25 < 25 := Nat.mod_lt a (by norm_num)
    set r := a % 25 with hr_def
    rw [ha] at hk
    -- (25q + r)² + 1 = 25(25q² + 2qr) + (r² + 1)
    have hring : (25 * (a / 25) + r) * (25 * (a / 25) + r) + 1 =
        25 * (25 * (a / 25) * (a / 25) + 2 * r * (a / 25)) + (r * r + 1) := by ring
    rw [hring] at hk
    -- So 25 | r²+1, with r < 25. Check all 25 residues.
    interval_cases r <;> omega
  · -- Backward: a ≡ 7 or 18 (mod 25) → 25 | a²+1
    intro h
    rcases h with h | h
    · exact mod25_achieves a a h h
    · exact mod25_achieves_18 a a h h

/- ## Deep Results (Axiomatized) -/

/-- Van Doorn's upper bound: |A|/N ≤ 2 Σ_{p ≡ 1 (4)} 1/p² ≈ 0.108.
    So maxNonSqfreeSet(N) ≤ ⌊0.108 · N⌋ + O(1). -/
axiom vanDoorn_upper_bound :
  ∃ C : ℕ, ∀ N : ℕ, 1 ≤ N →
    maxNonSqfreeSet N * 1000 ≤ 108 * N + C

/-- Sawhney's theorem: for sufficiently large N, the maximum is exactly
    ⌊N/25⌋, achieved only by {n ≡ 7 (mod 25)} or {n ≡ 18 (mod 25)}. -/
axiom sawhney_solution :
  ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
    maxNonSqfreeSet N = N / 25

/-- Structural result: any extremal set for large N is contained in
    {n ≡ 7 (mod 25)} or {n ≡ 18 (mod 25)}. -/
axiom sawhney_structure :
  ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
    ∀ A : Finset ℕ, (∀ a ∈ A, 1 ≤ a ∧ a ≤ N) →
      HasNonSqfreeProductProp A → A.card = N / 25 →
        (∀ a ∈ A, a % 25 = 7) ∨ (∀ a ∈ A, a % 25 = 18)
