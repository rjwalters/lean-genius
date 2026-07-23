/-
Erdős Problem #876: Sum-Free Sets and Gap Growth

Source: https://erdosproblems.com/876
Status: PARTIALLY SOLVED / OPEN

Statement:
Let A = {a₁ < a₂ < ⋯} ⊂ ℕ be an infinite sum-free set - that is, there are
no solutions to a = b₁ + ⋯ + bᵣ with b₁ < ⋯ < bᵣ < a ∈ A.
How small can the gaps aₙ₊₁ - aₙ be? Is it possible that aₙ₊₁ - aₙ < n?

Background:
A sum-free set is a set where no element is expressible as a sum of
distinct smaller elements from the set. This is a stronger condition than
the classical "sum-free" (no x + y = z) condition.

Known Results:
- Erdős (1962): Sum-free sets have density zero
- Graham: There exists A with aₙ₊₁ - aₙ < n^{1+o(1)}
- Deshouillers-Erdős-Melfi (1999): A sum-free set with aₙ ~ n^{3+o(1)}
- Łuczak-Schoen (2000): |A ∩ [1,N]| ≪ (N log N)^{1/2}
- Sullivan: Σ_{n∈A} 1/n < 4 (improved from Erdős's < 100)

Open Questions:
- Is aₙ₊₁ - aₙ < n possible?
- What is max Σ_{n∈A} 1/n? (Conjectured: slightly > 2)

References:
- [DEM99] Deshouillers-Erdős-Melfi (1999)
- [LuSc00] Łuczak-Schoen (2000)
- See also Problem #790
-/

import Mathlib
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Set.Basic
import Mathlib.Data.Finset.Basic

open scoped Classical

open Finset BigOperators

namespace Erdos876

/-
## Part I: Sum-Free Sets

A set is sum-free if no element is a sum of distinct smaller elements.
-/

/--
**Sum-Free Set (Erdős definition):**
A set A ⊂ ℕ is sum-free if no element a ∈ A can be written as
a sum b₁ + b₂ + ⋯ + bᵣ of distinct smaller elements bᵢ ∈ A.

This is DIFFERENT from the classical definition where x + y ≠ z.
Here we forbid ANY sum of distinct predecessors.
-/
def IsSumFreeErdos (A : Set ℕ) : Prop :=
  ∀ a ∈ A, ∀ (S : Finset ℕ), (↑S : Set ℕ) ⊆ A → (∀ b ∈ S, b < a) →
    S.card ≥ 2 → S.sum id ≠ a

/--
**Classical Sum-Free Set:**
The classical definition: no a, b, c ∈ A with a + b = c.
-/
def IsSumFreeClassical (A : Set ℕ) : Prop :=
  ∀ a ∈ A, ∀ b ∈ A, a + b ∉ A

/--
**The naive implication `IsSumFreeErdos A → IsSumFreeClassical A` is FALSE.**

One might expect the Erdős definition (no element is a sum of *distinct* smaller
elements) to be strictly stronger than `IsSumFreeClassical` (no `a + b ∈ A`). It
is **not**: `A = {2, 4}` is Erdős-sum-free — there is no set of ≥ 2 distinct
smaller elements of `A` summing to any element — yet `2 + 2 = 4 ∈ A`, so `A`
fails `IsSumFreeClassical`, which permits the *repeated* summand `a + a`. The two
notions are incomparable precisely on the "doubling" relation `a + a = c`. -/
theorem not_isSumFreeErdos_imp_isSumFreeClassical :
    ¬ ∀ A : Set ℕ, IsSumFreeErdos A → IsSumFreeClassical A := by
  intro h
  have herdos : IsSumFreeErdos ({2, 4} : Set ℕ) := by
    intro a ha S hSsub hlt _hcard _hsum
    have ha' : a = 2 ∨ a = 4 := by simpa using ha
    -- every element of `S` is `< a` and lies in `{2, 4}`, forcing it to be `2`
    have hsub2 : ∀ x ∈ S, x = 2 := by
      intro x hx
      have hxA : x = 2 ∨ x = 4 := by simpa using hSsub hx
      have hxlt := hlt x hx
      rcases ha' with rfl | rfl <;> rcases hxA with rfl | rfl <;> omega
    have hss : S ⊆ {2} := fun x hx => by simp [hsub2 x hx]
    have hc := Finset.card_le_card hss
    rw [Finset.card_singleton] at hc
    omega
  exact (h {2, 4} herdos 2 (by simp) 2 (by simp)) (by simp)

/--
**Corrected implication: Erdős sum-free ⟹ no `a + b ∈ A` for distinct positive
`a, b`.**

The Erdős definition *does* forbid `a + b ∈ A` whenever `a` and `b` are
**distinct** and **positive**: applying the definition to the two-element set
`{a, b}` (whose elements are both `< a + b` when positive, with sum `a + b`)
contradicts `a + b ∈ A`. Both hypotheses are necessary: distinctness fails for
`a = b` (`2 + 2 = 4` in `{2, 4}`, see `not_isSumFreeErdos_imp_isSumFreeClassical`),
and positivity fails for `a = 0` (`0 + b = b ∈ A` trivially). This is the honest
form of "the Erdős definition is stronger". -/
theorem erdos_implies_classical_of_pos {A : Set ℕ} (hA : IsSumFreeErdos A)
    {a b : ℕ} (ha : a ∈ A) (hb : b ∈ A) (hpa : 0 < a) (hpb : 0 < b)
    (hab : a ≠ b) : a + b ∉ A := by
  intro hmem
  have hsub : (↑({a, b} : Finset ℕ) : Set ℕ) ⊆ A := by
    intro x hx
    simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
      Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl <;> assumption
  have hlt : ∀ x ∈ ({a, b} : Finset ℕ), x < a + b := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl <;> omega
  have hcard2 : ({a, b} : Finset ℕ).card = 2 := Finset.card_pair hab
  have hsum : ({a, b} : Finset ℕ).sum id = a + b := by
    simp [Finset.sum_pair hab]
  exact hA (a + b) hmem {a, b} hsub hlt (by omega) hsum

/-
## Part II: Gap Sequences

For a sequence A = {a₁ < a₂ < ⋯}, the gaps are aₙ₊₁ - aₙ.
-/

/--
**Strictly increasing sequence:**
An increasing enumeration of an infinite set.
-/
def IsIncreasingEnumeration (a : ℕ → ℕ) : Prop :=
  ∀ n : ℕ, a n < a (n + 1)

/--
**Gap sequence:**
The n-th gap is aₙ₊₁ - aₙ.
-/
def gap (a : ℕ → ℕ) (n : ℕ) : ℕ := a (n + 1) - a n

/--
**Gap bound condition:**
aₙ₊₁ - aₙ < f(n) for all n.
-/
def HasGapBound (a : ℕ → ℕ) (f : ℕ → ℕ) : Prop :=
  ∀ n : ℕ, gap a n < f n

/--
**Linear gap bound:**
aₙ₊₁ - aₙ < n for all n.
-/
def HasLinearGapBound (a : ℕ → ℕ) : Prop :=
  ∀ n : ℕ, n ≥ 1 → gap a n < n

/-
## Part III: Erdős Problem #876 Questions

The main questions about sum-free set gaps.
-/

/--
**Main Question (Open):**
Does there exist an infinite sum-free set with aₙ₊₁ - aₙ < n?
-/
def ErdosQuestion876 : Prop :=
  ∃ (a : ℕ → ℕ), IsIncreasingEnumeration a ∧
    IsSumFreeErdos (Set.range a) ∧
    HasLinearGapBound a

/--
**Graham's Result:**
There exists a sum-free set with aₙ₊₁ - aₙ < n^{1+o(1)}.

More precisely: for any ε > 0, eventually aₙ₊₁ - aₙ < n^{1+ε}.
-/
axiom graham_result :
  ∀ ε : ℝ, ε > 0 →
    ∃ (a : ℕ → ℕ), IsIncreasingEnumeration a ∧
      IsSumFreeErdos (Set.range a) ∧
      ∃ N : ℕ, ∀ n ≥ N, (gap a n : ℝ) < (n : ℝ)^(1 + ε)

/-
## Part IV: Density Results
-/

/- 
**Density Zero (Erdős 1962):**
Sum-free sets have asymptotic density zero.
-/
/- 
**Łuczak-Schoen Upper Bound (2000):**
|A ∩ [1,N]| ≪ (N log N)^{1/2}
-/
/- 
**Łuczak-Schoen Lower Bound (2000):**
There exists a sum-free set B with |B ∩ [1,N]| ≫ N^{1/2} / (log N)^{1/2+o(1)}
-/
/-
## Part V: Growth Rate
-/

/- 
**Deshouillers-Erdős-Melfi (1999):**
There exists a sum-free set with aₙ ~ n^{3+o(1)}.
-/
/--
**Cubic Growth:**
The exponent 3 in n^{3+o(1)} is significant - it relates to
the structure of sum-free sets.
-/
def cubicGrowthExponent : ℕ := 3

/-
## Part VI: Reciprocal Sum Bounds
-/

/--
**Reciprocal Sum Question:**
What is the maximum of Σ_{n∈A} 1/n over all sum-free sets A?
-/
noncomputable def reciprocalSum (A : Set ℕ) : ℝ :=
  ∑' n, if n ∈ A ∧ n ≥ 1 then (1 : ℝ) / n else 0

/- 
**Erdős Upper Bound:**
Erdős proved Σ 1/n < 100 for any sum-free set.
-/
/- 
**Sullivan's Improvement:**
Sullivan improved this to Σ 1/n < 4.
-/
/- 
**Sullivan's Conjecture:**
The maximum reciprocal sum is slightly larger than 2.
-/
/-
## Part VII: Examples
-/

/--
**Powers of 2:**
The set {2^n : n ∈ ℕ} is sum-free.

Proof: 2^n ≠ sum of smaller powers of 2 (binary representation).
-/
theorem powers_of_two_sumfree :
    IsSumFreeErdos {n | ∃ k : ℕ, n = 2^k} := by
  intro a ha S hS hlt _hcard
  obtain ⟨k, rfl⟩ := ha
  -- Each member of `S` is a power of two strictly below `2^k`, so `S` is
  -- contained in `{2^0, …, 2^(k-1)}`; that whole set sums to `2^k - 1 < 2^k`.
  have hsub : S ⊆ (Finset.range k).image (2 ^ ·) := by
    intro b hb
    obtain ⟨j, rfl⟩ := hS (Finset.mem_coe.mpr hb)
    have hj : j < k := by
      by_contra hjk
      have hle2 : (2 : ℕ) ^ k ≤ 2 ^ j :=
        Nat.pow_le_pow_right (by norm_num) (Nat.le_of_not_lt hjk)
      have hlt2 := hlt _ hb
      omega
    exact Finset.mem_image.mpr ⟨j, Finset.mem_range.mpr hj, rfl⟩
  have hle : S.sum id ≤ ((Finset.range k).image (2 ^ ·)).sum id :=
    Finset.sum_le_sum_of_subset hsub
  have himg : ((Finset.range k).image (2 ^ ·)).sum id
      = ∑ j ∈ Finset.range k, 2 ^ j := by
    rw [Finset.sum_image fun x _ y _ h => Nat.pow_right_injective le_rfl h]
    simp
  have hgeom : ∀ m : ℕ, ∑ j ∈ Finset.range m, 2 ^ j = 2 ^ m - 1 := by
    intro m
    induction m with
    | zero => simp
    | succ n ih =>
        rw [Finset.sum_range_succ, ih, pow_succ]
        have h1 : 0 < (2 : ℕ) ^ n := by positivity
        omega
  have hone : 0 < (2 : ℕ) ^ k := by positivity
  intro hsum
  have hk := hgeom k
  omega

/-
**Powers of 3 that are 1 mod 3:**
Another classical example of a sum-free set.
-/

/-
## Part VIII: Connection to Sidon Sets
-/

/-
**Sidon Set Connection:**
Sum-free sets are related to (but different from) Sidon sets
where all pairwise sums are distinct.
-/

/-
**B_h Sequences:**
Sum-free sets are a type of B_h sequence for h = infinity.
-/

/-
## Part IX: Summary
-/

/--
**Erdős Problem #876: PARTIALLY SOLVED**

**QUESTION 1:** How small can gaps aₙ₊₁ - aₙ be?
**ANSWER:** At least n^{1+o(1)} (Graham), possibly linear (OPEN)

**QUESTION 2:** Is aₙ₊₁ - aₙ < n possible?
**ANSWER:** OPEN

**QUESTION 3:** What is max Σ 1/n?
**ANSWER:** Between 2 and 4 (Sullivan conjectures ~2)

**KEY RESULTS:**
1. Sum-free sets have density zero (Erdős 1962)
2. |A ∩ [1,N]| = Θ((N log N)^{1/2}) (Łuczak-Schoen 2000)
3. Growth rate: aₙ ~ n^{3+o(1)} achievable (DEM 1999)
4. Gap bound: aₙ₊₁ - aₙ < n^{1+o(1)} achievable (Graham)
-/
theorem erdos_876_summary :
    ∀ ε : ℝ, ε > 0 → ∃ (a : ℕ → ℕ), IsSumFreeErdos (Set.range a) ∧
      ∃ N : ℕ, ∀ n ≥ N, (gap a n : ℝ) < (n : ℝ)^(1 + ε) := by
  intro ε hε
  obtain ⟨a, hincr, hsum, N, hgap⟩ := graham_result ε hε
  exact ⟨a, hsum, N, hgap⟩

end Erdos876
