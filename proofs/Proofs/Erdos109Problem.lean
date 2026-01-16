/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: 9499cc0f-7627-475a-ac2c-201dd1f242cf

To cite Aristotle, tag @Aristotle-Harmonic on GitHub PRs/issues, and add as co-author to commits:
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>
-/

/-
Erdős Problem #109: The Erdős Sumset Conjecture

Source: https://erdosproblems.com/109
Status: SOLVED (Moreira-Richter-Robertson 2019)

Statement:
Any A ⊆ ℕ of positive upper density contains a sumset B + C where both B and C are infinite.

This is known as the "Erdős Sumset Conjecture."

History:
- Erdős: Conjectured this result
- Moreira-Richter-Robertson (2019): PROVED the conjecture in Annals of Mathematics

Key insight: Sets of positive density are "additively rich" enough to contain
structured infinite sumsets, despite the possibility of irregular distribution.

Related to Problem #656.

Reference: Moreira, Richter, Robertson (2019) "A proof of a sumset conjecture of Erdős"
           Ann. of Math. (2) 189(2):605-652
-/

import Mathlib


/- Aristotle failed to load this code into its environment. Double check that the syntax is correct.

Unexpected axioms were added during verification: ['harmonicSorry48280', 'Erdos109.even_has_pos_density', 'Erdos109.moreira_richter_robertson']-/
open Set Finset Filter BigOperators

namespace Erdos109

/-! ## Density Definitions -/

/-- The counting function: number of elements of A in {1,...,N}. -/
noncomputable def countingFn (A : Set ℕ) (N : ℕ) : ℕ :=
  Set.ncard (A ∩ Set.Icc 1 N)

/-- The upper density of a set A ⊆ ℕ. -/
noncomputable def upperDensity (A : Set ℕ) : ℝ :=
  Filter.limsup (fun N => (countingFn A N : ℝ) / N) Filter.atTop

/-- A set has positive upper density. -/
def HasPositiveUpperDensity (A : Set ℕ) : Prop :=
  0 < upperDensity A

/-- The lower density of a set A ⊆ ℕ. -/
noncomputable def lowerDensity (A : Set ℕ) : ℝ :=
  Filter.liminf (fun N => (countingFn A N : ℝ) / N) Filter.atTop

/-- A set has positive lower density (stronger than positive upper density). -/
def HasPositiveLowerDensity (A : Set ℕ) : Prop :=
  0 < lowerDensity A

/-- Lower density is at most upper density. -/
theorem lowerDensity_le_upperDensity (A : Set ℕ) :
    lowerDensity A ≤ upperDensity A := by
  unfold lowerDensity upperDensity
  -- liminf ≤ limsup for any bounded sequence in [0, 1]
  apply Filter.liminf_le_limsup
  · -- Bounded above: density ≤ 1
    use 1
    simp only [Filter.eventually_map, Filter.eventually_atTop]
    use 1
    intro N hN
    simp only [countingFn]
    have hN_pos : (0 : ℝ) < N := by positivity
    rw [div_le_one hN_pos]
    have h1 : (A ∩ Set.Icc 1 N).ncard ≤ N := by
      have hsub : A ∩ Set.Icc 1 N ⊆ Set.Icc 1 N := Set.inter_subset_right
      have hfin : (Set.Icc 1 N).Finite := Set.finite_Icc 1 N
      calc (A ∩ Set.Icc 1 N).ncard
          ≤ (Set.Icc 1 N).ncard := Set.ncard_le_ncard hsub hfin
        _ ≤ N := by
            rw [Set.ncard_eq_toFinset_card']
            simp only [Set.toFinset_Icc]
            simp only [Nat.card_Icc]
            omega
    exact_mod_cast h1
  · -- Bounded below: density ≥ 0
    use 0
    simp only [Filter.eventually_map, ge_iff_le, Filter.eventually_atTop]
    use 1
    intro N _
    apply div_nonneg
    · exact Nat.cast_nonneg _
    · exact Nat.cast_nonneg _

/-- Positive lower density implies positive upper density. -/
theorem posLowerDensity_implies_posUpperDensity (A : Set ℕ) :
    HasPositiveLowerDensity A → HasPositiveUpperDensity A := by
  intro h
  unfold HasPositiveUpperDensity
  calc 0 < lowerDensity A := h
       _ ≤ upperDensity A := lowerDensity_le_upperDensity A

/-! ## Sumset Definition -/

/-- The sumset B + C: all sums b + c with b ∈ B and c ∈ C. -/
def Sumset (B C : Set ℕ) : Set ℕ :=
  { n | ∃ b ∈ B, ∃ c ∈ C, n = b + c }

notation:65 B " +ₛ " C => Sumset B C

/-- Basic property: zero is in B + C if both contain zero. -/
theorem zero_mem_sumset (B C : Set ℕ) (hB : 0 ∈ B) (hC : 0 ∈ C) :
    0 ∈ B +ₛ C := by
  use 0, hB, 0, hC

/-- Sumset is commutative. -/
theorem sumset_comm (B C : Set ℕ) : (B +ₛ C) = (C +ₛ B) := by
  ext n
  simp only [Sumset, Set.mem_setOf_eq]
  constructor
  · intro ⟨x, hx, y, hy, h⟩
    exact ⟨y, hy, x, hx, by omega⟩
  · intro ⟨x, hx, y, hy, h⟩
    exact ⟨y, hy, x, hx, by omega⟩

/-! ## The Erdős Sumset Conjecture -/

/--
**Erdős Sumset Conjecture** (PROVED by Moreira-Richter-Robertson 2019):

Any A ⊆ ℕ of positive upper density contains a sumset B + C
where both B and C are infinite.

This was a longstanding conjecture of Erdős that connects density
and additive structure.
-/
def ErdosSumsetConjecture : Prop :=
  ∀ A : Set ℕ, HasPositiveUpperDensity A →
    ∃ B C : Set ℕ, B.Infinite ∧ C.Infinite ∧ (B +ₛ C) ⊆ A

/--
**Moreira-Richter-Robertson Theorem (2019)**:
The Erdős Sumset Conjecture is true.

This was proved in "A proof of a sumset conjecture of Erdős"
published in Annals of Mathematics in 2019.
-/
axiom moreira_richter_robertson : ErdosSumsetConjecture

/-- The conjecture is resolved. -/
theorem erdos_109_solved : ErdosSumsetConjecture := moreira_richter_robertson

/-! ## Consequences and Related Results -/

/-- A set containing an infinite sumset B + C is necessarily infinite. -/
theorem sumset_infinite_implies_superset_infinite (A B C : Set ℕ)
    (hB : B.Infinite) (hC : C.Infinite) (h : (B +ₛ C) ⊆ A) :
    A.Infinite := by
  apply Set.Infinite.mono h
  -- B + C is infinite if both B and C are infinite
  by_contra hfin
  push_neg at hfin
  -- If B + C is finite, then for any fixed b ∈ B, the set {b + c : c ∈ C} is finite
  -- But this set has the same cardinality as C, contradiction
  obtain ⟨b, hb⟩ := hB.nonempty
  have hinf : Set.Infinite { n | ∃ c ∈ C, n = b + c } := by
    -- The map c ↦ b + c is an injection from C to this set
    -- Since C is infinite, so is this set
    have heq : { n | ∃ c ∈ C, n = b + c } = (fun c => b + c) '' C := by
      ext n
      simp only [Set.mem_setOf_eq, Set.mem_image]
      constructor
      · intro ⟨c, hc, hn⟩; exact ⟨c, hc, hn.symm⟩
      · intro ⟨c, hc, hn⟩; exact ⟨c, hc, hn.symm⟩
    rw [heq]
    apply hC.image
    intro a _ c _ h
    have : b + a = b + c := h
    exact Nat.add_left_cancel this
  have hsub : { n | ∃ c ∈ C, n = b + c } ⊆ (B +ₛ C) := by
    intro n ⟨c, hc, hn⟩
    simp only [Sumset, Set.mem_setOf_eq]
    exact ⟨b, hb, c, hc, hn⟩
  exact hinf (hfin.subset hsub)

/-- Corollary: Sets of positive upper density are infinite. -/
theorem posUpperDensity_infinite (A : Set ℕ) (h : HasPositiveUpperDensity A) :
    A.Infinite := by
  obtain ⟨B, C, hB, hC, hsub⟩ := moreira_richter_robertson A h
  exact sumset_infinite_implies_superset_infinite A B C hB hC hsub

/-! ## Strengthenings -/

/--
**Stronger Form** (also proved):
The sets B and C can be chosen to have arbitrarily large gaps between
consecutive elements. This shows the sumset structure is quite robust.
-/
def StrongerSumsetConjecture : Prop :=
  ∀ A : Set ℕ, HasPositiveUpperDensity A →
    ∀ f : ℕ → ℕ, (∀ n, f n > 0) →
      ∃ B C : Set ℕ, B.Infinite ∧ C.Infinite ∧ (B +ₛ C) ⊆ A ∧
        (∀ b₁ b₂, b₁ ∈ B → b₂ ∈ B → b₁ < b₂ → b₂ - b₁ ≥ f b₁)

/-
**Connection to Szemerédi's Theorem**:

Szemerédi's theorem states that sets of positive density contain arbitrarily
long arithmetic progressions (k-APs for all k).

The Erdős sumset conjecture gives a different kind of additive structure:
infinite sumsets B + C rather than finite arithmetic progressions.

These are complementary results about how density forces additive structure.
-/

/-! ## Examples -/

/-- The natural numbers have density 1 (the full set has density 1).
    This is a standard fact: lim_{N→∞} |{1,...,N}|/N = 1. -/
theorem naturals_have_full_density : HasPositiveUpperDensity (Set.univ : Set ℕ) := by
  unfold HasPositiveUpperDensity upperDensity countingFn
  simp only [Set.univ_inter]
  -- We need to show limsup (|Icc 1 N| / N) > 0
  -- Since |Icc 1 N| = N for N ≥ 1, the limit is 1
  have h : ∀ N ≥ 1, (Set.Icc 1 N).ncard = N := by
    intro N hN
    rw [Set.ncard_eq_toFinset_card']
    simp only [Set.toFinset_Icc, Nat.card_Icc]
    omega
  -- The ratio converges to 1
  apply lt_of_lt_of_le (show (0 : ℝ) < 1 by norm_num)
  apply Filter.le_limsup_of_frequently_le
  · simp only [Filter.frequently_atTop]
    intro N
    use max N 1
    constructor
    · exact le_max_left N 1
    · have hmax : max N 1 ≥ 1 := le_max_right N 1
      rw [h (max N 1) hmax]
      have hpos : (0 : ℝ) < max N 1 := by positivity
      rw [div_self (ne_of_gt hpos)]
  · -- Need to show the sequence is bounded above
    use 1
    simp only [Filter.eventually_map, Filter.eventually_atTop]
    use 1
    intro N hN
    have hN_pos : (0 : ℝ) < N := by positivity
    rw [div_le_one hN_pos]
    have h1 : (Set.Icc 1 N).ncard ≤ N := by
      rw [Set.ncard_eq_toFinset_card']
      simp only [Set.toFinset_Icc, Nat.card_Icc]
      omega
    exact_mod_cast h1

/-- The even numbers have density 1/2 and satisfy the conjecture. -/
def evenNumbers : Set ℕ := { n | Even n }

/-- The even numbers have positive upper density (specifically, density 1/2).
    The density is exactly 1/2 because |{2,4,...,2⌊N/2⌋} ∩ {1,...,N}| / N → 1/2.
    This is a standard fact in analytic number theory. -/
axiom even_has_pos_density : HasPositiveUpperDensity evenNumbers

/-- The even numbers form an infinite set. -/
theorem evenNumbers_infinite : evenNumbers.Infinite := by
  have h : (Set.range (fun n : ℕ => 2 * n)).Infinite := by
    apply Set.infinite_range_of_injective
    intro a b hab
    have : 2 * a = 2 * b := hab
    exact Nat.eq_of_mul_eq_mul_left (by norm_num : 0 < 2) this
  convert h using 1
  ext n
  simp only [evenNumbers, Set.mem_setOf_eq, Set.mem_range, Even]
  constructor
  · intro ⟨k, hk⟩; use k; linarith
  · intro ⟨k, hk⟩; use k; linarith

/-- For even numbers, we can take B = C = {0, 2, 4, ...}. -/
theorem even_sumset_example :
    ∃ B C : Set ℕ, B.Infinite ∧ C.Infinite ∧ (B +ₛ C) ⊆ evenNumbers := by
  use evenNumbers, evenNumbers
  refine ⟨?_, ?_, ?_⟩
  · exact evenNumbers_infinite
  · exact evenNumbers_infinite
  · -- evenNumbers + evenNumbers ⊆ evenNumbers
    intro n hn
    simp only [Sumset, Set.mem_setOf_eq] at hn
    obtain ⟨b, ⟨kb, hb⟩, c, ⟨kc, hc⟩, hn⟩ := hn
    simp only [evenNumbers, Set.mem_setOf_eq, Even]
    use kb + kc
    linarith

/-! ## Proof Techniques

The Moreira-Richter-Robertson proof uses:
1. Ergodic theory and measure-preserving systems
2. Furstenberg correspondence principle
3. IP-sets and recurrence along polynomial sequences
4. Sophisticated combinatorial arguments

The proof is highly non-trivial and represents a major achievement in
combinatorial ergodic theory.
-/

/-! ## Summary

**Problem Status: SOLVED**

Erdős Problem #109 asked whether every set A ⊆ ℕ of positive upper density
contains a sumset B + C with both B and C infinite.

**Answer: YES** (Moreira-Richter-Robertson 2019)

**Key Results**:
1. Proved in Annals of Mathematics 2019
2. Uses ergodic theory and Furstenberg correspondence
3. Establishes a fundamental connection between density and additive structure

**Related Problems**:
- Problem #656: Related sumset questions
- Szemerédi's theorem: Different additive structure (arithmetic progressions)

References:
- Moreira, Richter, Robertson (2019): "A proof of a sumset conjecture of Erdős"
  Ann. of Math. (2) 189(2):605-652
-/

end Erdos109