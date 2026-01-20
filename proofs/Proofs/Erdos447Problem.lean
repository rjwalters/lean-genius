/-
Erdős Problem #447: Union-Free Collections of Sets

Source: https://erdosproblems.com/447
Status: SOLVED (Kleitman 1971)

Statement:
How large can a union-free collection ℱ of subsets of [n] be?
A collection is union-free if there are no distinct A, B, C ∈ ℱ
with A ∪ B = C.

Questions:
1. Must |ℱ| = o(2ⁿ)?
2. Is |ℱ| < (1+o(1)) C(n, ⌊n/2⌋)?

Solution (Kleitman 1971):
Yes to both! |ℱ| < (1+o(1)) C(n, ⌊n/2⌋)

The maximum is achieved by antichains, and the middle binomial
coefficient is optimal.

Reference: https://erdosproblems.com/447
-/

import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Combinatorics.SetFamily.Compression.Down

open Finset Nat

namespace Erdos447

/-
## Part I: Basic Definitions

Union-free collections and related concepts.
-/

/--
**The Ground Set:**
[n] = {0, 1, ..., n-1} represented as Finset (Fin n)
-/
abbrev GroundSet (n : ℕ) := Finset (Fin n)

/--
**Power Set:**
The collection of all subsets of [n].
-/
def powerSet (n : ℕ) : Finset (GroundSet n) :=
  Finset.univ.powerset

/--
**Union-Free Collection:**
A collection ℱ is union-free if there are no distinct A, B, C ∈ ℱ
with A ∪ B = C.

In other words: no set in ℱ is the union of two other distinct sets in ℱ.
-/
def IsUnionFree {n : ℕ} (F : Finset (GroundSet n)) : Prop :=
  ∀ A B C : GroundSet n, A ∈ F → B ∈ F → C ∈ F →
    A ≠ B → A ≠ C → B ≠ C →
    A ∪ B ≠ C

/--
**Alternative Definition (Symmetric):**
No three distinct sets have one being the union of the other two.
-/
def IsUnionFree' {n : ℕ} (F : Finset (GroundSet n)) : Prop :=
  ∀ A B C : GroundSet n, A ∈ F → B ∈ F → C ∈ F →
    A ≠ B ∧ A ≠ C ∧ B ≠ C →
    A ∪ B ≠ C ∧ A ∪ C ≠ B ∧ B ∪ C ≠ A

/-
## Part II: Trivial Bounds

Basic observations about union-free collections.
-/

/--
**Middle Layer:**
The collection of all subsets of [n] of size exactly ⌊n/2⌋.
-/
def middleLayer (n : ℕ) : Finset (GroundSet n) :=
  (Finset.univ : Finset (GroundSet n)).filter (fun S => S.card = n / 2)

/--
**Middle Layer is Union-Free:**
Subsets of the same size cannot have one be the union of two others
(since union increases or maintains size).
-/
theorem middleLayer_union_free (n : ℕ) : IsUnionFree (middleLayer n) := by
  intro A B C hA hB hC hAB hAC hBC hUnion
  simp only [middleLayer, mem_filter] at hA hB hC
  -- If A ∪ B = C and |A| = |B| = |C| = n/2, then A ⊆ C and B ⊆ C
  -- But |A ∪ B| ≥ max(|A|, |B|) with equality iff A ⊆ B or B ⊆ A
  -- Since A ∪ B = C and |C| = n/2, we need |A ∪ B| = n/2
  -- This forces A = B (contradiction) or one is subset of other
  sorry

/--
**Middle Binomial Coefficient:**
C(n, ⌊n/2⌋) is the largest binomial coefficient.
-/
def middleBinomial (n : ℕ) : ℕ := Nat.choose n (n / 2)

/--
**Antichain Bound:**
Any antichain has size at most C(n, ⌊n/2⌋) (Sperner's theorem).
-/
axiom sperner_theorem (n : ℕ) (F : Finset (GroundSet n)) :
    (∀ A B : GroundSet n, A ∈ F → B ∈ F → A ≠ B → ¬(A ⊆ B) ∧ ¬(B ⊆ A)) →
    F.card ≤ middleBinomial n

/-
## Part III: The Main Question

Is |ℱ| = o(2ⁿ)?
-/

/--
**Little-o Notation:**
f(n) = o(g(n)) means f(n)/g(n) → 0 as n → ∞.
-/
def IsLittleO (f g : ℕ → ℕ) : Prop :=
  ∀ ε : ℝ, ε > 0 → ∃ N : ℕ, ∀ n ≥ N, (f n : ℝ) ≤ ε * g n

/--
**Maximum Union-Free Size:**
The maximum size of a union-free collection over subsets of [n].
-/
noncomputable def maxUnionFreeSize (n : ℕ) : ℕ :=
  ((powerSet n).filter IsUnionFree).sup Finset.card

/-
## Part IV: Sárközy-Szemerédi Result (Unpublished)

The weaker bound: |ℱ| = o(2ⁿ).
-/

/--
**Sárközy-Szemerédi (Unpublished, reported 1965):**
maxUnionFreeSize(n) = o(2ⁿ)

This was reported by Erdős but the proof was never published.
It was superseded by Kleitman's stronger result.
-/
axiom sarkozy_szemeredi_bound :
    IsLittleO maxUnionFreeSize (fun n => 2 ^ n)

/-
## Part V: Kleitman's Theorem

The optimal bound: |ℱ| < (1+o(1)) C(n, ⌊n/2⌋).
-/

/--
**(1+o(1)) Factor:**
A function f(n) is asymptotically (1+o(1))·g(n) if
f(n)/g(n) → 1 as n → ∞.
-/
def AsymptoticTo (f g : ℕ → ℕ) : Prop :=
  ∀ ε : ℝ, ε > 0 → ∃ N : ℕ, ∀ n ≥ N,
    (1 - ε) * (g n : ℝ) ≤ f n ∧ (f n : ℝ) ≤ (1 + ε) * g n

/--
**Upper Bound Asymptotic:**
f(n) ≤ (1+o(1))·g(n) means f(n)/g(n) → 1⁺ from above.
-/
def AsymptoticUpperBound (f g : ℕ → ℕ) : Prop :=
  ∀ ε : ℝ, ε > 0 → ∃ N : ℕ, ∀ n ≥ N, (f n : ℝ) ≤ (1 + ε) * g n

/--
**Kleitman's Theorem (1971):**
maxUnionFreeSize(n) < (1+o(1)) · C(n, ⌊n/2⌋)

This is optimal because the middle layer achieves this bound.
-/
axiom kleitman_theorem :
    AsymptoticUpperBound maxUnionFreeSize middleBinomial

/--
**Kleitman's Paper:**
"Collections of subsets containing no two sets and their union"
Proceedings of the LA Meeting AMS (1971), 153-155.
-/
theorem kleitman_reference : True := trivial

/-
## Part VI: Lower Bound (Middle Layer)

The middle layer shows the bound is tight.
-/

/--
**Middle Layer Size:**
|middleLayer(n)| = C(n, ⌊n/2⌋)
-/
theorem middleLayer_card (n : ℕ) : (middleLayer n).card = middleBinomial n := by
  sorry  -- Counting argument

/--
**Lower Bound:**
maxUnionFreeSize(n) ≥ C(n, ⌊n/2⌋)

Achieved by taking the middle layer (antichain of middle-sized sets).
-/
theorem lower_bound (n : ℕ) : maxUnionFreeSize n ≥ middleBinomial n := by
  -- The middle layer is union-free and has size C(n, n/2)
  sorry

/--
**Tightness:**
The bound is asymptotically tight: maxUnionFreeSize(n) ~ C(n, ⌊n/2⌋)
-/
theorem bound_tight :
    AsymptoticTo maxUnionFreeSize middleBinomial := by
  -- Combine lower_bound and kleitman_theorem
  sorry

/-
## Part VII: Connection to Problem 487

Application to number theory.
-/

/--
**LCM Representation:**
If A ⊂ ℕ has positive density, then ∃ distinct a, b, c ∈ A with [a,b] = c.

This follows from |ℱ| = o(2ⁿ) via encoding.
-/
def lcmRepresentation (A : Set ℕ) : Prop :=
  ∃ a b c : ℕ, a ∈ A ∧ b ∈ A ∧ c ∈ A ∧
    a ≠ b ∧ a ≠ c ∧ b ≠ c ∧
    Nat.lcm a b = c

/--
**Positive Density:**
A ⊂ ℕ has positive density if liminf |A ∩ [1,n]|/n > 0.
-/
def hasPositiveDensity (A : Set ℕ) : Prop :=
  ∃ δ : ℝ, δ > 0 ∧ ∀ N : ℕ, N > 0 →
    ↑(Finset.card ((Finset.range N).filter (· ∈ A))) / N ≥ δ

/--
**Corollary of Union-Free Bound:**
If A ⊂ ℕ has positive density, then there are infinitely many
distinct a, b, c ∈ A with [a,b] = c.

This is Erdős Problem #487.
-/
axiom problem_487_from_447 (A : Set ℕ) (hA : hasPositiveDensity A) :
    ∀ N : ℕ, ∃ a b c : ℕ, a > N ∧ a ∈ A ∧ b ∈ A ∧ c ∈ A ∧
      a ≠ b ∧ a ≠ c ∧ b ≠ c ∧ Nat.lcm a b = c

/-
## Part VIII: Generalizations

Related problems about forbidden union structures.
-/

/--
**k-Union-Free:**
No set is the union of k other distinct sets in the collection.
-/
def IsKUnionFree {n : ℕ} (F : Finset (GroundSet n)) (k : ℕ) : Prop :=
  ∀ (S : Finset (GroundSet n)), S ⊆ F → S.card = k + 1 →
    ∀ C : GroundSet n, C ∈ S →
      (S.erase C).sup id ≠ C

/--
**Problem 1023:**
Forbid the union of ANY number of sets being in the family.

This is a much stronger condition than 2-union-free.
-/
def IsStrongUnionFree {n : ℕ} (F : Finset (GroundSet n)) : Prop :=
  ∀ (S : Finset (GroundSet n)), S ⊆ F → S.card ≥ 2 →
    S.sup id ∉ F ∨ S.sup id ∈ S

/-
## Part IX: Main Results

Summary of Erdős Problem #447.
-/

/--
**Erdős Problem #447: Summary**

Status: SOLVED (Kleitman 1971)

**Question:** How large can a union-free collection ℱ of subsets of [n] be?

**Answer:**
|ℱ| < (1+o(1)) · C(n, ⌊n/2⌋)

**Lower bound:** The middle layer achieves C(n, ⌊n/2⌋).

**Key insight:** Union-free collections are essentially antichains,
and Sperner's theorem bounds antichain size.

**Application:** Implies infinitely many LCM representations in
positive density sets (Problem 487).
-/
theorem erdos_447 :
    -- Upper bound: |F| < (1+o(1)) C(n, n/2)
    AsymptoticUpperBound maxUnionFreeSize middleBinomial ∧
    -- Lower bound: |F| ≥ C(n, n/2)
    (∀ n, maxUnionFreeSize n ≥ middleBinomial n) := by
  exact ⟨kleitman_theorem, lower_bound⟩

/--
**Historical Timeline:**
- Erdős posed the problem
- Sárközy & Szemerédi proved o(2ⁿ) (unpublished, 1965)
- Kleitman proved (1+o(1))C(n,n/2) (1971)
-/
theorem historical_timeline : True := trivial

end Erdos447
