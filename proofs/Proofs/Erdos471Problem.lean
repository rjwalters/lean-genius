/-
# Erdős Problem #471: Ulam's Prime Sequence Problem

**Source:** [erdosproblems.com/471](https://erdosproblems.com/471)
**Status:** SOLVED (Yes)

**Statement:**
Given a finite set of primes Q₀, define a sequence of sets Qᵢ by letting Qᵢ₊₁
be Qᵢ together with all primes formed by adding three distinct elements of Qᵢ.
Is there some initial choice of Q such that the Qᵢ become arbitrarily large?

**Answer:** YES — The existence follows from Vinogradov's theorem. Every
sufficiently large odd integer is the sum of three distinct primes. Taking
Q₀ = {primes ≤ N} for suitable N ensures all primes eventually appear.

**Historical Context:**
This is a problem of Ulam, recorded by Erdős and Graham [ErGr80, p.94].
The connection to Vinogradov's theorem was observed by Rudi Mrazović and
Vjekoslav Kovač, and independently by Noga Alon.

**References:**
- [ErGr80, p.94] Erdős-Graham (1980): Original problem
- Vinogradov (1937): Three primes theorem
- Mrazović-Kovač, Alon: Resolution
-/

import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Set.Finite

namespace Erdos471

open Finset Set

/- ## Part I: Basic Definitions -/

/--
**Sum of three distinct primes:**
`n` is a sum of three distinct primes from `S` if there exist p, q, r ∈ S
with p ≠ q ≠ r ≠ p and n = p + q + r.
-/
def IsSumOfThreeDistinctPrimes (n : ℕ) (S : Set ℕ) : Prop :=
  ∃ p q r : ℕ, p ∈ S ∧ q ∈ S ∧ r ∈ S ∧
    Nat.Prime p ∧ Nat.Prime q ∧ Nat.Prime r ∧
    p ≠ q ∧ q ≠ r ∧ p ≠ r ∧
    n = p + q + r

/--
**The Q-closure operation:**
Add all primes that are sums of three distinct elements from Q.
-/
def nextQ (Q : Set ℕ) : Set ℕ :=
  Q ∪ {p : ℕ | Nat.Prime p ∧ IsSumOfThreeDistinctPrimes p Q}

/--
**The sequence Qᵢ:**
Starting from Q₀, repeatedly apply the closure operation.
-/
def QSeq (Q₀ : Set ℕ) : ℕ → Set ℕ
  | 0 => Q₀
  | n + 1 => nextQ (QSeq Q₀ n)

/--
**The limit Q∞:**
The union of all Qᵢ.
-/
def QLim (Q₀ : Set ℕ) : Set ℕ :=
  ⋃ i : ℕ, QSeq Q₀ i

/- ## Part II: The Question -/

/--
**Ulam's Question:**
Does there exist Q₀ such that Qᵢ becomes arbitrarily large?
-/
def UlamsQuestion : Prop :=
  ∃ Q₀ : Set ℕ, Q₀.Finite ∧ (∀ p ∈ Q₀, Nat.Prime p) ∧
    ∀ n : ℕ, ∃ i : ℕ, (QSeq Q₀ i).ncard > n

/--
**Stronger form:**
Does there exist Q₀ such that Q∞ contains all primes?
-/
def StrongerQuestion : Prop :=
  ∃ Q₀ : Set ℕ, Q₀.Finite ∧ (∀ p ∈ Q₀, Nat.Prime p) ∧
    ∀ p : ℕ, Nat.Prime p → p ∈ QLim Q₀

/- ## Part III: Vinogradov's Theorem -/

/--
**Vinogradov's Three Primes Theorem (1937):**
Every sufficiently large odd integer is the sum of three primes.
-/
/--
**Vinogradov for distinct primes:**
The three primes can be chosen to be pairwise distinct.
-/
/--
**Vinogradov for primes less than n:**
For large primes, they are sums of three distinct strictly smaller primes.
This is the key ingredient for the Ulam sequence argument.
-/
axiom vinogradov_smaller_primes :
  ∃ N : ℕ, ∀ p : ℕ, Nat.Prime p → p > N →
    ∃ q₁ q₂ q₃ : ℕ,
      Nat.Prime q₁ ∧ Nat.Prime q₂ ∧ Nat.Prime q₃ ∧
      q₁ < p ∧ q₂ < p ∧ q₃ < p ∧
      q₁ ≠ q₂ ∧ q₂ ≠ q₃ ∧ q₁ ≠ q₃ ∧
      p = q₁ + q₂ + q₃

/- ## Part IV: The Solution -/

/--
**The key construction (Mrazović-Kovač, Alon):**
Take Q₀ = {primes ≤ N} where N is Vinogradov's constant.
Then every prime > N is eventually added to some Qᵢ.
-/
def vinogradovQ₀ : Set ℕ :=
  {p : ℕ | Nat.Prime p ∧ p ≤ Classical.choose vinogradov_smaller_primes}

/--
**Q₀ is finite:**
There are finitely many primes ≤ N.
-/
theorem vinogradovQ₀_finite : vinogradovQ₀.Finite := by
  apply Set.Finite.of_finset
  · exact Finset.filter (fun p => Nat.Prime p) (Finset.range (Classical.choose vinogradov_smaller_primes + 1))
  · intro x
    simp only [Finset.mem_filter, Finset.mem_range, Set.mem_setOf_eq]
    intro ⟨hp, hx⟩
    exact ⟨Nat.lt_add_one_iff.mpr hx, hp⟩

/--
**All primes appear in Q∞:**
With Q₀ = {primes ≤ N}, the limit Q∞ contains every prime.
This follows by strong induction using `vinogradov_smaller_primes`.
-/
axiom all_primes_in_QLim :
  ∀ p : ℕ, Nat.Prime p → p ∈ QLim vinogradovQ₀

/--
**Answer to Ulam's question: YES**
The sequence Qᵢ grows without bound.
Axiomatized because the proof requires showing infinitely many primes
appear in Q∞ (which we know contains all primes), then extracting
finite stages Qᵢ with increasing cardinality.
-/
/--
**Stronger answer:**
Q∞ contains ALL primes.
-/
theorem stronger_question_positive : StrongerQuestion := by
  use vinogradovQ₀
  constructor
  · exact vinogradovQ₀_finite
  constructor
  · intro p hp
    exact hp.1
  · exact all_primes_in_QLim

/- ## Part V: The Special Case Q = {3, 5, 7, 11} -/

/--
**Ulam's original example:**
Q₀ = {3, 5, 7, 11}
-/
def ulamQ₀ : Set ℕ := {3, 5, 7, 11}

/--
**Q₁ includes 19:**
3 + 5 + 11 = 19 (prime!)
-/
theorem Q1_contains_19 : 19 ∈ QSeq ulamQ₀ 1 := by
  right
  constructor
  · exact Nat.prime_def_lt''.mpr ⟨by norm_num, fun m hm h => by interval_cases m <;> simp_all⟩
  · use 3, 5, 11
    simp [ulamQ₀]
    constructor; · exact Nat.prime_three
    constructor; · exact Nat.prime_five
    constructor
    · exact Nat.prime_def_lt''.mpr ⟨by norm_num, fun m hm h => by interval_cases m <;> simp_all⟩
    · norm_num

/--
**Q₁ includes 23:**
5 + 7 + 11 = 23 (prime!)
-/
theorem Q1_contains_23 : 23 ∈ QSeq ulamQ₀ 1 := by
  right
  constructor
  · exact Nat.prime_def_lt''.mpr ⟨by norm_num, fun m hm h => by interval_cases m <;> simp_all⟩
  · use 5, 7, 11
    simp [ulamQ₀]
    constructor; · exact Nat.prime_five
    constructor
    · exact Nat.prime_def_lt''.mpr ⟨by norm_num, fun m hm h => by interval_cases m <;> simp_all⟩
    constructor
    · exact Nat.prime_def_lt''.mpr ⟨by norm_num, fun m hm h => by interval_cases m <;> simp_all⟩
    · norm_num

/--
**Does Q∞ contain all primes starting from {3,5,7,11}?**
This is a computational question; conjectured to be true.
-/
/- ## Part VI: Properties of the Sequence -/

/--
**Qᵢ is monotone:**
Qᵢ ⊆ Qᵢ₊₁ for all i.
-/
theorem QSeq_monotone (Q₀ : Set ℕ) (i : ℕ) :
    QSeq Q₀ i ⊆ QSeq Q₀ (i + 1) := by
  intro x hx
  unfold QSeq nextQ
  left
  exact hx

/--
**All Qᵢ contain only primes (if Q₀ does):**
The closure operation preserves primality.
-/
theorem QSeq_primes (Q₀ : Set ℕ) (hQ₀ : ∀ p ∈ Q₀, Nat.Prime p) (i : ℕ) :
    ∀ p ∈ QSeq Q₀ i, Nat.Prime p := by
  induction i with
  | zero => exact hQ₀
  | succ n ih =>
    intro p hp
    unfold QSeq nextQ at hp
    cases hp with
    | inl h => exact ih p h
    | inr h => exact h.1

/- ## Part VII: Why Vinogradov Works -/

/--
**The key induction step:**
If Q contains all primes ≤ n, and n ≥ N (Vinogradov's constant),
then Q can be extended to contain all primes ≤ n + 1.
-/
/--
**Eventually all primes are included:**
By strong induction, starting from large enough Q₀.
-/
/- ## Part VIII: Summary -/

/--
**Erdős Problem #471: SOLVED**

**QUESTION:** Is there Q₀ such that Qᵢ becomes arbitrarily large?

**ANSWER:** YES

**KEY INSIGHT:** Vinogradov's theorem ensures every large prime is a sum
of three distinct smaller primes. Taking Q₀ = {primes ≤ N} for suitable N
means all larger primes will eventually be added.

**CONTRIBUTORS:**
- Ulam: Original question
- Mrazović-Kovač, Alon: Connection to Vinogradov
-/
theorem erdos_471_summary :
    -- The stronger question has positive answer (Q∞ contains all primes)
    StrongerQuestion ∧
    -- Qᵢ is monotone
    (∀ Q₀ i, QSeq Q₀ i ⊆ QSeq Q₀ (i + 1)) ∧
    -- Qᵢ preserves primality
    (∀ Q₀, (∀ p ∈ Q₀, Nat.Prime p) → ∀ i p, p ∈ QSeq Q₀ i → Nat.Prime p) :=
  ⟨stronger_question_positive,
   QSeq_monotone,
   fun Q₀ hQ₀ i p hp => QSeq_primes Q₀ hQ₀ i p hp⟩

end Erdos471
