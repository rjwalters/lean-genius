/-
# Erdős Problem #949: Sum-Free Sets and Continuum-Sized Sumset Avoidance

Let S ⊆ ℝ be a set containing no solution to a + b = c (i.e., S is
sum-free). Must there exist A ⊆ ℝ \ S with |A| = 𝔠 (continuum)
such that A + A ⊆ ℝ \ S?

## Status: OPEN (general); SOLVED for Sidon sets

## References
- Erdős (original problem)
- Dillies–AlphaProof: proved the Sidon variant
-/

import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Finite.Basic
import Mathlib.SetTheory.Cardinal.Basic
import Mathlib.SetTheory.Cardinal.Continuum
import Mathlib.Tactic

/-
## Section I: Sum-Free Sets
-/

/-- A set S ⊆ ℝ is sum-free: no a, b, c ∈ S satisfy a + b = c.
Equivalently, (S + S) ∩ S = ∅. -/
def IsSumFreeSet (S : Set ℝ) : Prop :=
  ∀ a ∈ S, ∀ b ∈ S, a + b ∉ S

/-
## Section II: Sidon Sets
-/

/-- A Sidon set in ℝ: all pairwise sums a + b with a ≤ b are distinct.
Equivalently, a + b = c + d with a ≤ b, c ≤ d implies (a,b) = (c,d). -/
def IsSidonReal (S : Set ℝ) : Prop :=
  ∀ a ∈ S, ∀ b ∈ S, ∀ c ∈ S, ∀ d ∈ S,
    a ≤ b → c ≤ d → a + b = c + d → a = c ∧ b = d

/-
## Section III: The Sumset
-/

/-- The sumset A + A = {a + b : a, b ∈ A}. -/
def realSumset (A : Set ℝ) : Set ℝ :=
  {x | ∃ a ∈ A, ∃ b ∈ A, x = a + b}

/-
## Section IV: The Main Problem
-/

/-- **Erdős Problem #949**: If S ⊆ ℝ is sum-free, must there exist
A ⊆ ℝ \ S with |A| = 𝔠 such that A + A ⊆ ℝ \ S?

This asks whether sum-free sets always leave enough room in their
complement for a continuum-sized set whose sumset also avoids S. -/
def ErdosProblem949 : Prop :=
  ∀ S : Set ℝ, IsSumFreeSet S →
    ∃ A : Set ℝ, A ⊆ Sᶜ ∧
      Cardinal.mk A = Cardinal.continuum ∧
      realSumset A ⊆ Sᶜ

/-
## Section V: The Sidon Variant (Solved)
-/

/-- The Sidon variant: if S is Sidon, then a continuum-sized
sumset-avoiding subset of the complement exists.

This was proved by Dillies using a result discovered by AlphaProof. -/
axiom sidon_variant_solved :
    ∀ S : Set ℝ, IsSidonReal S →
      ∃ A : Set ℝ, A ⊆ Sᶜ ∧
        Cardinal.mk A = Cardinal.continuum ∧
        realSumset A ⊆ Sᶜ

/-- Every Sidon set is sum-free (since if a + b = c with a,b,c ∈ S,
the Sidon property forces a = c or b = c, giving 0 ∈ S or a = 0). -/
axiom sidon_is_sum_free (S : Set ℝ) (hS : IsSidonReal S) (h0 : (0 : ℝ) ∉ S) :
    IsSumFreeSet S

/-
## Section VI: Proof Strategy for Sidon Case
-/

/-- Key ingredient: if S is Sidon with |S| < 𝔠, then Sᶜ is large
enough to find A by Zorn's lemma. -/
axiom sidon_small_case (S : Set ℝ) (hS : IsSidonReal S)
    (hcard : Cardinal.mk S < Cardinal.continuum) :
    ∃ A : Set ℝ, A ⊆ Sᶜ ∧
      Cardinal.mk A = Cardinal.continuum ∧
      realSumset A ⊆ Sᶜ

/-- Key ingredient: if S is Sidon with |S| = 𝔠, pick a ∈ S with
a ≠ 0 and form A = ((S \ {a}) - a/2) \ S. The Sidon property
ensures the intersection is at most a singleton. -/
axiom sidon_continuum_case (S : Set ℝ) (hS : IsSidonReal S)
    (hcard : Cardinal.mk S = Cardinal.continuum) :
    ∃ A : Set ℝ, A ⊆ Sᶜ ∧
      Cardinal.mk A = Cardinal.continuum ∧
      realSumset A ⊆ Sᶜ

/-
## Section VII: General Sum-Free Case
-/

/-- The general problem remains open. Sum-free sets are much more
general than Sidon sets, and the proof technique for Sidon sets
(which crucially uses the injectivity of the sum function) does
not extend to the sum-free case. -/
axiom sum_free_open_problem :
    ErdosProblem949 ∨ ¬ ErdosProblem949
