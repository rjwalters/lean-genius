/-
Erdős Problem #877: Counting Maximal Sum-Free Subsets

Source: https://erdosproblems.com/877
Status: SOLVED

Statement:
Let f_m(n) count the number of maximal sum-free subsets A ⊆ {1,...,n} -
that is, there are no solutions to a = b + c in A and A is maximal with
this property. Estimate f_m(n) - is it true that f_m(n) = o(2^{n/2})?

History:
- Cameron-Erdős: Proved f_m(n) > 2^{n/4}
- Łuczak-Schoen (2001): Proved f_m(n) < 2^{cn} for some c < 1/2
- Balogh-Liu-Sharifzadeh-Treglown (2015): Proved f_m(n) = 2^{(1/4+o(1))n}
- Same authors (2018): Proved f_m(n) = (C_n + o(1))2^{n/4}

The problem is SOLVED: f_m(n) = o(2^{n/2}) is TRUE.

References:
- [LuSc01]: Łuczak-Schoen "On the number of maximal sum-free sets" (2001)
- [BLST15]: Balogh et al. "The number of maximal sum-free subsets" (2015)
- [BLST18]: Balogh et al. "Sharp bound on maximal sum-free subsets" (2018)
-/

import Mathlib

open Nat Finset
open scoped Classical

namespace Erdos877

/-
## Part I: Sum-Free Sets
-/

/--
**Sum-Free Set:**
A set A ⊆ ℕ is sum-free if there are no solutions to a = b + c with a, b, c ∈ A.
Equivalently, A ∩ (A + A) = ∅.
-/
def isSumFree (A : Finset ℕ) : Prop :=
  ∀ a b c : ℕ, a ∈ A → b ∈ A → c ∈ A → a ≠ b + c

/--
**Alternative definition via sumset:**
A is sum-free iff A and A + A are disjoint.
-/
def sumset (A : Finset ℕ) : Finset ℕ :=
  (A.product A).image (fun p => p.1 + p.2)

def isSumFree' (A : Finset ℕ) : Prop :=
  Disjoint A (sumset A)

/--
**Example: Odd numbers are sum-free:**
The set of odd numbers in {1,...,n} is sum-free since odd + odd = even.
-/
theorem odds_sum_free : isSumFree {1, 3, 5, 7, 9} := by
  intro a b c ha hb hc
  simp at ha hb hc
  omega

/--
**Example: {n/2 + 1, ..., n} is sum-free:**
The upper half of {1,...,n} is sum-free since the smallest possible
sum is (n/2+1) + (n/2+1) > n.
-/
theorem upper_half_sum_free (n : ℕ) (A : Finset ℕ)
    (hA : ∀ x ∈ A, n / 2 + 1 ≤ x ∧ x ≤ n) : isSumFree A := by
  intro a b c ha hb hc heq
  have ⟨ha1, ha2⟩ := hA a ha
  have ⟨hb1, _⟩ := hA b hb
  have ⟨hc1, _⟩ := hA c hc
  omega

/-
## Part II: Maximal Sum-Free Sets
-/

/--
**Maximal Sum-Free Set:**
A sum-free set A is maximal if adding any element x ∉ A to A
creates a sum (i.e., A ∪ {x} is not sum-free).
-/
def isMaximalSumFree (n : ℕ) (A : Finset ℕ) : Prop :=
  A ⊆ Finset.range (n + 1) ∧
  isSumFree A ∧
  ∀ x ∈ Finset.range (n + 1), x ∉ A → ¬isSumFree (insert x A)

/--
**Property of maximal sum-free sets:**
For a maximal sum-free A ⊆ {1,...,n}, every positive x ∉ A either:
- Has x = a + b for some a, b ∈ A, or
- Has a = x + b for some a, b ∈ A, or
- Has x + x = a for some a ∈ A.

The positivity hypothesis `0 < x` is necessary: for `x = 0`, the trivial
sum `0 = 0 + 0` witnesses `¬ isSumFree (insert 0 A)` for *any* maximal `A`
(indeed any sum-free `A`, since `0 ∉ A`), so none of the three structural
conclusions need hold (e.g. `A = ∅` is maximal sum-free for `n = 0`).
-/
theorem maximal_criterion (n : ℕ) (A : Finset ℕ)
    (hmax : isMaximalSumFree n A) (x : ℕ) (hx : x ∈ Finset.range (n + 1))
    (hxpos : 0 < x) (hxA : x ∉ A) :
    (∃ a b : ℕ, a ∈ A ∧ b ∈ A ∧ x = a + b) ∨
    (∃ a b : ℕ, a ∈ A ∧ b ∈ A ∧ a = x + b) ∨
    (∃ a : ℕ, a ∈ A ∧ x + x = a) := by
  obtain ⟨hsub, hsf, hmaximal⟩ := hmax
  have hns := hmaximal x hx hxA
  -- `A` is sum-free, hence `0 ∉ A` (else `0 = 0 + 0` is a forbidden sum).
  have h0 : (0 : ℕ) ∉ A := fun h => hsf 0 0 0 h h h rfl
  unfold isSumFree at hns
  push_neg at hns
  obtain ⟨a, b, c, ha, hb, hc, heq⟩ := hns
  simp only [Finset.mem_insert] at ha hb hc
  -- A genuine sum `a = b + c` in `insert x A` must involve the new element `x`,
  -- since `A` itself is sum-free.
  rcases ha with rfl | ha
  · -- a = x
    rcases hb with rfl | hb
    · -- b = x, so x = x + c forces c = 0, impossible (c = x > 0 or 0 ∈ A)
      exfalso
      rcases hc with rfl | hc
      · omega
      · have : c = 0 := by omega
        exact h0 (this ▸ hc)
    · -- b ∈ A, x = b + c
      rcases hc with rfl | hc
      · -- c = x ⇒ b = 0 ∈ A, contradiction
        have hb0 : b = 0 := by omega
        exact absurd (hb0 ▸ hb) h0
      · exact Or.inl ⟨b, c, hb, hc, heq⟩
  · -- a ∈ A
    rcases hb with rfl | hb
    · -- b = x, a = x + c
      rcases hc with rfl | hc
      · -- c = x, a = x + x
        exact Or.inr (Or.inr ⟨a, ha, heq.symm⟩)
      · exact Or.inr (Or.inl ⟨a, c, ha, hc, heq⟩)
    · -- b ∈ A
      rcases hc with rfl | hc
      · -- c = x, a = b + x = x + b
        exact Or.inr (Or.inl ⟨a, b, ha, hb, by omega⟩)
      · -- c ∈ A: a = b + c with a,b,c ∈ A contradicts sum-freeness
        exact absurd heq (hsf a b c ha hb hc)

/-
## Part III: Counting Functions
-/

/--
**f(n) - All sum-free subsets:**
Count of all sum-free subsets of {1,...,n}.
-/
noncomputable def f (n : ℕ) : ℕ :=
  ((Finset.range (n + 1)).powerset.filter isSumFree).card

/--
**f_m(n) - Maximal sum-free subsets:**
Count of maximal sum-free subsets of {1,...,n}.
-/
noncomputable def f_m (n : ℕ) : ℕ :=
  ((Finset.range (n + 1)).powerset.filter (isMaximalSumFree n)).card

/--
**Basic relationship:**
Every maximal sum-free set is sum-free, so f_m(n) ≤ f(n).
-/
theorem f_m_le_f (n : ℕ) : f_m n ≤ f n := by
  unfold f_m f
  apply Finset.card_le_card
  intro A
  simp only [Finset.mem_filter]
  exact fun ⟨hpow, hmax⟩ => ⟨hpow, hmax.2.1⟩

/-
## Part IV: The Cameron-Erdős Lower Bound
-/

/--
**Cameron-Erdős Lower Bound:**
f_m(n) > 2^{n/4}.
This is proved by constructing enough distinct maximal sum-free sets.
-/
axiom cameron_erdos_lower_bound :
    ∀ n : ℕ, n ≥ 4 → f_m n > 2 ^ (n / 4)

/--
**Construction intuition:**
The odd numbers in {1,...,n} form a sum-free set of size ~n/2.
Various subsets of odds can be extended to distinct maximal sets,
giving exponentially many maximal sum-free sets.
-/
theorem odds_construction (n : ℕ) : ∃ A : Finset ℕ,
    A ⊆ Finset.range (n + 1) ∧
    isSumFree A ∧
    A.card ≥ n / 2 := by
  -- The upper half {⌊n/2⌋+1, ..., n} is sum-free (smallest sum exceeds n)
  -- and has cardinality n - ⌊n/2⌋ = ⌈n/2⌉ ≥ ⌊n/2⌋.
  refine ⟨Finset.Ioc (n / 2) n, ?_, ?_, ?_⟩
  · intro x hx
    rw [Finset.mem_Ioc] at hx
    rw [Finset.mem_range]
    omega
  · apply upper_half_sum_free n
    intro x hx
    rw [Finset.mem_Ioc] at hx
    omega
  · rw [Nat.card_Ioc]
    omega

/-
## Part V: The Łuczak-Schoen Upper Bound (2001)
-/

/--
**Łuczak-Schoen Theorem:**
There exists c < 1/2 such that f_m(n) < 2^{cn}.
This proves f_m(n) = o(2^{n/2}).
-/
axiom luczak_schoen_theorem :
    ∃ c : ℝ, c < 1/2 ∧ ∀ n : ℕ, n ≥ 1 → (f_m n : ℝ) < (2 : ℝ) ^ (c * n)

/--
**Main question resolved:**
f_m(n) = o(2^{n/2}) is TRUE by Łuczak-Schoen.
-/
theorem main_question_resolved :
    ∃ c : ℝ, c < 1/2 ∧ ∀ n : ℕ, n ≥ 1 → (f_m n : ℝ) < (2 : ℝ) ^ (c * n) :=
  luczak_schoen_theorem

/-
**Corollary: f_m(n) = o(f(n)):**
Cameron-Erdős also asked if f_m(n) = o(f(n)).
Since f(n) ≥ 2^{cn} for some c close to 1/2 (the odds alone give ~2^{n/2}),
and f_m(n) < 2^{c'n} for c' < 1/2, this is also resolved.
-/

/-
## Part VI: The BLST Sharp Bounds (2015, 2018)
-/

/-
**BLST 2015 Result:**
f_m(n) = 2^{(1/4 + o(1))n}.
This pins down the exponent as 1/4.

**BLST 2018 Sharp Bound:**
f_m(n) = (C_n + o(1)) · 2^{n/4},
where C_n is an explicit constant depending only on n mod 4.

**The four cases of C_n:**
The constant C_n depends on n mod 4, reflecting the structure of
maximal sum-free sets in each residue class.
-/

/-
## Part VII: Structure of Maximal Sum-Free Sets
-/

/-
**The three canonical constructions:**
Most maximal sum-free sets fall into one of three types:
1. Subsets of odd numbers
2. Subsets of {n/3+1, ..., n}
3. Hybrid constructions
-/

/-
**Why 1/4?**
The exponent 1/4 arises because:
- The odds give ~n/2 elements, but maximal subsets are constrained
- Only ~n/4 elements can be chosen freely in typical maximal sets
-/

/-
**Container method:**
The BLST proof uses the container method: maximal sum-free sets
are contained in a small number of "containers", each with
limited freedom for element choices.
-/

/-
## Part VIII: Relationship to Erdős #748
-/

/-
**Erdős #748: All sum-free sets:**
Related problem asks about f(n), the count of all sum-free sets.
Cameron-Erdős conjectured f(n) = Θ(2^{n/2}).
-/

/--
**Comparison:**
- f(n) = Θ(2^{n/2}): All sum-free sets
- f_m(n) = Θ(2^{n/4}): Maximal sum-free sets
The ratio f_m(n)/f(n) → 0 as n → ∞.
-/
theorem maximal_vs_all :
    ∃ c : ℚ, c > 0 ∧
      ∀ n : ℕ, n ≥ 4 → 2 ^ (n / 4) ≤ f_m n ∧ f_m n < 2 ^ (n / 2) := by
  sorry

/-
## Part IX: Summary
-/

/--
**Erdős Problem #877 Summary:**

QUESTION: Is f_m(n) = o(2^{n/2})?

ANSWER: YES (SOLVED)

KEY RESULTS:
1. Cameron-Erdős: f_m(n) > 2^{n/4} (lower bound)
2. Łuczak-Schoen (2001): f_m(n) < 2^{cn} for c < 1/2 (upper bound, resolves question)
3. BLST (2015): f_m(n) = 2^{(1/4+o(1))n} (pins down exponent)
4. BLST (2018): f_m(n) = (C_n+o(1))·2^{n/4} (sharp asymptotics)

The answer is YES: f_m(n) grows like 2^{n/4}, which is o(2^{n/2}).
-/
theorem erdos_877_solved :
    -- The main question is resolved
    (∃ c : ℝ, c < 1/2 ∧ ∀ n : ℕ, n ≥ 1 → (f_m n : ℝ) < (2 : ℝ) ^ (c * n)) ∧
    -- And the sharp asymptotics are known
    (∀ n : ℕ, n ≥ 4 → f_m n > 2 ^ (n / 4)) := by
  exact ⟨luczak_schoen_theorem, cameron_erdos_lower_bound⟩

/--
**Main Theorem:**
f_m(n) = Θ(2^{n/4}), resolving Erdős Problem #877.
-/
theorem erdos_877 : ∃ c₁ c₂ : ℚ,
    c₁ > 0 ∧ c₂ > 0 ∧
    ∀ n : ℕ, n ≥ 4 →
      c₁ * 2 ^ (n / 4) ≤ (f_m n : ℚ) ∧ (f_m n : ℚ) ≤ c₂ * 2 ^ (n / 4) := by
  sorry

end Erdos877
