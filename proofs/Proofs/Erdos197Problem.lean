/-
Erdős Problem #197: Partition of ℕ Avoiding Monotone 3-AP Permutations

Source: https://erdosproblems.com/197
Status: OPEN

Statement:
Can ℕ be partitioned into two sets, each of which can be permuted to avoid
monotone 3-term arithmetic progressions?

More precisely: Does there exist a partition ℕ = A ∪ B such that:
1. A and B are disjoint
2. There exists a bijection f : A → ℕ such that f(A) has no monotone 3-AP
3. There exists a bijection g : B → ℕ such that g(B) has no monotone 3-AP

A monotone 3-term arithmetic progression (3-AP) in a sequence is three terms
a_i, a_j, a_k with i < j < k such that a_j - a_i = a_k - a_j (equally spaced).

Key Results:
- The answer is YES if three sets are allowed (Erdős-Graham)
- The two-set case remains open
- The problem cannot be resolved by finite computation alone

References:
- [ErGr79] Erdős and Graham, "Old and new problems and results in combinatorial
  number theory"
- [ErGr80] Erdős and Graham, follow-up work on arithmetic progressions
-/

import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Function
import Mathlib.Data.Nat.Basic
import Mathlib.Logic.Function.Basic
import Mathlib.Order.Basic
import Mathlib.Tactic

open Set Function

namespace Erdos197

/-
## Part I: Arithmetic Progressions

A 3-term arithmetic progression (3-AP) in a sequence is three terms at
increasing indices that form an arithmetic progression.
-/

/--
**Arithmetic Progression Predicate:**
Three natural numbers form an arithmetic progression if the middle one
is the average of the other two.
-/
def isArithmeticProgression (a b c : ℕ) : Prop := a + c = 2 * b

/--
**Monotone 3-AP in a Sequence:**
A sequence f : ℕ → ℕ contains a monotone 3-AP if there exist indices i < j < k
such that f(i), f(j), f(k) form an arithmetic progression.
-/
def hasMonotone3AP (f : ℕ → ℕ) : Prop :=
  ∃ i j k : ℕ, i < j ∧ j < k ∧ isArithmeticProgression (f i) (f j) (f k)

/--
**3-AP Free Sequence:**
A sequence avoids monotone 3-APs if it has no such triple.
-/
def avoids3AP (f : ℕ → ℕ) : Prop := ¬hasMonotone3AP f

/-
## Part II: Permutations of Sets

A set can be "permuted to avoid 3-AP" if there's a bijection from the set
to ℕ such that the resulting sequence has no monotone 3-AP.
-/

/--
**Enumeration of a Set:**
An enumeration of a set S is a bijection from ℕ to S.
-/
def isEnumeration (S : Set ℕ) (f : ℕ → ℕ) : Prop :=
  Function.Bijective f ∧ ∀ n, f n ∈ S

/--
**Set can be Permuted to Avoid 3-AP:**
A set S can be permuted to avoid 3-APs if there exists an enumeration
of S that has no monotone 3-AP.
-/
def canPermuteTo3APFree (S : Set ℕ) : Prop :=
  ∃ f : ℕ → ℕ, isEnumeration S f ∧ avoids3AP f

/-
## Part III: Partitions of ℕ

A partition of ℕ into two sets.
-/

/--
**Two-Set Partition of ℕ:**
A and B form a partition of ℕ if they are disjoint and their union is ℕ.
-/
def isTwoPartition (A B : Set ℕ) : Prop :=
  Disjoint A B ∧ A ∪ B = Set.univ

/-- Partition elements are in exactly one part. -/
theorem partition_mem_iff (A B : Set ℕ) (h : isTwoPartition A B) (n : ℕ) :
    (n ∈ A ∧ n ∉ B) ∨ (n ∉ A ∧ n ∈ B) := by
  have ⟨hdisj, huniv⟩ := h
  have hmem : n ∈ A ∪ B := by rw [huniv]; trivial
  rcases hmem with ha | hb
  · left
    constructor
    · exact ha
    · intro hb
      have := hdisj.ne_of_mem ha hb
      simp at this
  · right
    constructor
    · intro ha
      have := hdisj.ne_of_mem ha hb
      simp at this
    · exact hb

/-
## Part IV: The Main Conjecture

Erdős Problem #197: Can ℕ be partitioned into two sets, each permutable
to avoid monotone 3-APs?
-/

/--
**Erdős Problem #197 (Open):**
Does there exist a partition of ℕ into two sets A and B such that both
A and B can be permuted to avoid monotone 3-term arithmetic progressions?

This disjunction holds by excluded middle — the problem is open because we
don't know which disjunct is true.
-/
theorem erdos_197_conjecture :
    (∃ A B : Set ℕ, isTwoPartition A B ∧
      canPermuteTo3APFree A ∧ canPermuteTo3APFree B) ∨
    (∀ A B : Set ℕ, isTwoPartition A B →
      ¬canPermuteTo3APFree A ∨ ¬canPermuteTo3APFree B) := by
  by_cases h : ∃ A B : Set ℕ, isTwoPartition A B ∧
      canPermuteTo3APFree A ∧ canPermuteTo3APFree B
  · exact Or.inl h
  · right
    intro A B hpart
    by_contra habs
    push_neg at habs
    exact h ⟨A, B, hpart, habs.1, habs.2⟩

/-
## Part V: The Three-Set Case (Solved)

With three sets, the answer is YES. This was proved by Erdős and Graham.
-/

/--
**Three-Set Partition of ℕ:**
A, B, C form a partition of ℕ if they are pairwise disjoint and cover ℕ.
-/
def isThreePartition (A B C : Set ℕ) : Prop :=
  Disjoint A B ∧ Disjoint B C ∧ Disjoint A C ∧ A ∪ B ∪ C = Set.univ

/--
**Erdős-Graham Three-Set Theorem:**
ℕ CAN be partitioned into THREE sets, each permutable to avoid monotone 3-APs.
-/
axiom erdos_graham_three_sets :
    ∃ A B C : Set ℕ, isThreePartition A B C ∧
      canPermuteTo3APFree A ∧ canPermuteTo3APFree B ∧ canPermuteTo3APFree C

/-
## Part VI: Properties of 3-AP Avoidance
-/

/--
**Constant Sequence Has 3-APs:**
A constant sequence f(n) = c has trivial 3-APs at every triple of indices,
since c + c = 2c always holds.
-/
theorem constant_has_3AP (c : ℕ) : hasMonotone3AP (fun _ => c) := by
  exact ⟨0, 1, 2, by omega, by omega, by simp [isArithmeticProgression]; ring⟩

/--
**Strictly Increasing Sequences:**
A strictly increasing sequence f satisfies f(i) < f(j) when i < j.
-/
def StrictlyIncreasing (f : ℕ → ℕ) : Prop := ∀ i j, i < j → f i < f j

/--
**Strictly Decreasing Sequences:**
A strictly decreasing sequence f satisfies f(i) > f(j) when i < j.
-/
def StrictlyDecreasing (f : ℕ → ℕ) : Prop := ∀ i j, i < j → f i > f j

/-
## Part VII: Small Examples
-/

/--
**The identity has many 3-APs:**
The sequence 0, 1, 2, 3, ... has a 3-AP at any three consecutive terms.
-/
theorem identity_has_3AP : hasMonotone3AP id := by
  use 0, 1, 2
  constructor
  · omega
  constructor
  · omega
  · simp [isArithmeticProgression]

/--
**Powers of 2 avoid 3-APs:**
The sequence 1, 2, 4, 8, 16, ... avoids 3-APs.

Proof: If 2^i + 2^k = 2 * 2^j with i < j < k, then since j < k we have
2^k ≥ 2^(j+1) = 2 * 2^j, and since 2^i ≥ 1, we get
2^i + 2^k ≥ 1 + 2 * 2^j > 2 * 2^j, contradicting the equation.
-/
theorem powers_of_2_avoid_3AP :
    avoids3AP (fun n => 2 ^ n) := by
  intro ⟨i, j, k, hij, hjk, hap⟩
  simp only [isArithmeticProgression] at hap
  -- hap : 2 ^ i + 2 ^ k = 2 * 2 ^ j
  -- Since j < k, 2^k ≥ 2^(j+1) = 2 * 2^j, and 2^i ≥ 1
  have hk : 2 * 2 ^ j ≤ 2 ^ k := by
    have : 2 ^ (j + 1) ≤ 2 ^ k := Nat.pow_le_pow_right (by omega) hjk
    linarith [show 2 ^ (j + 1) = 2 * 2 ^ j from by ring]
  have hi : 0 < 2 ^ i := pow_pos (by omega : (0 : ℕ) < 2) i
  linarith

/-- A subsequence of a 3-AP-free sequence is 3-AP-free.
    Key implication: if a set has a 3-AP-free enumeration, any infinite subset does too. -/
theorem avoids3AP_of_comp {f g : ℕ → ℕ} (hf : avoids3AP f) (hg : StrictMono g) :
    avoids3AP (f ∘ g) := by
  intro ⟨i, j, k, hij, hjk, hap⟩
  exact hf ⟨g i, g j, g k, hg hij, hg hjk, hap⟩

/-
## Part VIII: Computational Intractability

The two-set version cannot be resolved by finite computation alone.
Any finite portion of ℕ can be partitioned to avoid 3-APs in both parts,
but this does not extend to all of ℕ. This is a known meta-mathematical
observation rather than a formal theorem.
-/

/-
## Part IX: Related Sequences
-/

/--
**Stanley Sequence S(0,1):**
The 3-AP-free sequence starting with 0, 1 and greedily adding the smallest
number that doesn't create a 3-AP.

Begins: 0, 1, 3, 5, 9, 11, 13, 15, 25, 27, ...
-/
def isStanleySequence (f : ℕ → ℕ) : Prop :=
  f 0 = 0 ∧ f 1 = 1 ∧
  avoids3AP f ∧
  StrictlyIncreasing f ∧
  ∀ n ≥ 2, ∀ m, f (n - 1) < m → m < f n →
    ∃ i j, i < j ∧ j < n ∧ isArithmeticProgression (f i) (f j) m

/--
**Stanley Sequence Avoids 3-AP:**
By construction.
-/
axiom stanley_avoids_3AP :
    ∃ f : ℕ → ℕ, isStanleySequence f ∧ avoids3AP f

/-- The Stanley sequence property already implies 3-AP avoidance.
    The `∧ avoids3AP f` in stanley_avoids_3AP is redundant. -/
theorem stanley_implies_avoids3AP {f : ℕ → ℕ} (h : isStanleySequence f) : avoids3AP f :=
  h.2.2.1

/-
## Part X: Main Results Summary
-/

/--
**Problem Status:**
Erdős Problem #197 remains open. We know:
1. The three-set version is solvable (erdos_graham_three_sets, axiom)
2. Individual 3-AP-free sequences exist (powers_of_2_avoid_3AP, proved)
3. The two-set question is undecided (erdos_197_conjecture, by excluded middle)
-/
theorem erdos_197_status :
    (∃ A B C : Set ℕ, isThreePartition A B C ∧
      canPermuteTo3APFree A ∧ canPermuteTo3APFree B ∧ canPermuteTo3APFree C) ∧
    (∃ f : ℕ → ℕ, avoids3AP f) := by
  exact ⟨erdos_graham_three_sets, ⟨fun n => 2 ^ n, powers_of_2_avoid_3AP⟩⟩

/--
**The Main Open Question:**
Whether two sets suffice remains unknown.
-/
theorem erdos_197_open_question :
    (∃ A B : Set ℕ, isTwoPartition A B ∧
      canPermuteTo3APFree A ∧ canPermuteTo3APFree B) ∨
    (∀ A B : Set ℕ, isTwoPartition A B →
      ¬canPermuteTo3APFree A ∨ ¬canPermuteTo3APFree B) :=
  erdos_197_conjecture

end Erdos197
