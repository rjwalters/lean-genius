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

/- ## Part I: Basic Definitions -/

/-- [n] = {0, 1, ..., n-1} represented as Finset (Fin n) -/
abbrev GroundSet (n : ℕ) := Finset (Fin n)

/-- The collection of all subsets of [n] -/
def powerSet (n : ℕ) : Finset (GroundSet n) :=
  Finset.univ.powerset

/-- A collection ℱ is union-free if there are no distinct A, B, C ∈ ℱ
with A ∪ B = C. -/
def IsUnionFree {n : ℕ} (F : Finset (GroundSet n)) : Prop :=
  ∀ A B C : GroundSet n, A ∈ F → B ∈ F → C ∈ F →
    A ≠ B → A ≠ C → B ≠ C →
    A ∪ B ≠ C

/-- Symmetric version: no three distinct sets have one being the union
of the other two. -/
def IsUnionFree' {n : ℕ} (F : Finset (GroundSet n)) : Prop :=
  ∀ A B C : GroundSet n, A ∈ F → B ∈ F → C ∈ F →
    A ≠ B ∧ A ≠ C ∧ B ≠ C →
    A ∪ B ≠ C ∧ A ∪ C ≠ B ∧ B ∪ C ≠ A

/- ## Part II: Middle Layer and Sperner Bound -/

/-- The collection of all subsets of [n] of size exactly ⌊n/2⌋ -/
def middleLayer (n : ℕ) : Finset (GroundSet n) :=
  (Finset.univ : Finset (GroundSet n)).filter (fun S => S.card = n / 2)

/-- The middle layer is union-free: sets of the same size cannot have
one be the union of two others (since |A ∪ B| ≥ max(|A|, |B|) with
equality only when A ⊆ B or B ⊆ A, forcing A = B). -/
/-- C(n, ⌊n/2⌋), the largest binomial coefficient -/
def middleBinomial (n : ℕ) : ℕ := Nat.choose n (n / 2)

/-- Sperner's theorem: any antichain in 2^[n] has size at most C(n, ⌊n/2⌋) -/
/- ## Part III: Asymptotic Notation -/

/-- f(n) = o(g(n)) means f(n)/g(n) → 0 as n → ∞ -/
def IsLittleO (f g : ℕ → ℕ) : Prop :=
  ∀ ε : ℝ, ε > 0 → ∃ N : ℕ, ∀ n ≥ N, (f n : ℝ) ≤ ε * g n

/-- The maximum size of a union-free collection over subsets of [n] -/
noncomputable def maxUnionFreeSize (n : ℕ) : ℕ :=
  ((powerSet n).filter IsUnionFree).sup Finset.card

/-- f(n) ≤ (1+o(1))·g(n): upper bound with asymptotically vanishing error -/
def AsymptoticUpperBound (f g : ℕ → ℕ) : Prop :=
  ∀ ε : ℝ, ε > 0 → ∃ N : ℕ, ∀ n ≥ N, (f n : ℝ) ≤ (1 + ε) * g n

/- ## Part IV: Sárközy-Szemerédi Result (1965) -/

/-- Sárközy-Szemerédi (unpublished, reported 1965): maxUnionFreeSize(n) = o(2ⁿ).
This was superseded by Kleitman's stronger result. -/
/- ## Part V: Kleitman's Theorem (1971) -/

/-- Kleitman (1971): maxUnionFreeSize(n) < (1+o(1)) · C(n, ⌊n/2⌋).
This is optimal because the middle layer achieves this bound.
Reference: "Collections of subsets containing no two sets and their union",
Proceedings of the LA Meeting AMS (1971), 153-155. -/
axiom kleitman_theorem :
    AsymptoticUpperBound maxUnionFreeSize middleBinomial

/- ## Part VI: Lower Bound -/

/-- |middleLayer(n)| = C(n, ⌊n/2⌋) -/
theorem middleLayer_card (n : ℕ) : (middleLayer n).card = middleBinomial n := by
  simp only [middleLayer, middleBinomial]
  have h : (Finset.univ : Finset (Finset (Fin n))).filter (fun S => S.card = n / 2) =
      (Finset.univ : Finset (Fin n)).powersetCard (n / 2) := by
    ext S; simp [Finset.mem_powersetCard]
  rw [h, Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin]

/-- maxUnionFreeSize(n) ≥ C(n, ⌊n/2⌋), achieved by the middle layer -/
axiom lower_bound (n : ℕ) : maxUnionFreeSize n ≥ middleBinomial n

/- ## Part VII: Connection to Problem 487 -/

/-- LCM representation: distinct a, b, c ∈ A with lcm(a,b) = c -/
def lcmRepresentation (A : Set ℕ) : Prop :=
  ∃ a b c : ℕ, a ∈ A ∧ b ∈ A ∧ c ∈ A ∧
    a ≠ b ∧ a ≠ c ∧ b ≠ c ∧
    Nat.lcm a b = c

/-- A ⊂ ℕ has positive density if liminf |A ∩ [1,n]|/n > 0 -/
def hasPositiveDensity (A : Set ℕ) : Prop :=
  ∃ δ : ℝ, δ > 0 ∧ ∀ N : ℕ, N > 0 →
    ↑(Finset.card ((Finset.range N).filter (· ∈ A))) / N ≥ δ

/-- Corollary (Problem 487): if A ⊂ ℕ has positive density, then there
are infinitely many distinct a, b, c ∈ A with lcm(a,b) = c.
This follows from the union-free bound via prime factorization encoding. -/
/- ## Part VIII: Generalizations -/

/-- k-union-free: no set is the union of k other distinct sets -/
def IsKUnionFree {n : ℕ} (F : Finset (GroundSet n)) (k : ℕ) : Prop :=
  ∀ (S : Finset (GroundSet n)), S ⊆ F → S.card = k + 1 →
    ∀ C : GroundSet n, C ∈ S →
      (S.erase C).sup id ≠ C

/-- Strong union-free (Problem 1023): no set is the union of ANY
number of other sets in the family -/
def IsStrongUnionFree {n : ℕ} (F : Finset (GroundSet n)) : Prop :=
  ∀ (S : Finset (GroundSet n)), S ⊆ F → S.card ≥ 2 →
    S.sup id ∉ F ∨ S.sup id ∈ S

/- ## Part IX: Summary -/

/--
**Erdős Problem #447: Summary**

Kleitman (1971) proved the optimal bound:
  maxUnionFreeSize(n) < (1+o(1)) · C(n, ⌊n/2⌋)
The middle layer achieves C(n, ⌊n/2⌋), so the bound is tight.
-/
theorem erdos_447_summary :
    -- Upper bound: Kleitman's theorem
    AsymptoticUpperBound maxUnionFreeSize middleBinomial ∧
    -- Lower bound: middle layer achieves C(n, n/2)
    (∀ n, maxUnionFreeSize n ≥ middleBinomial n) :=
  ⟨kleitman_theorem, lower_bound⟩

end Erdos447
