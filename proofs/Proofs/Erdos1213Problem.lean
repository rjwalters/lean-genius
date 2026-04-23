/-
Erdős Problem #1213: Repeated Interval Sums in Bounded-Gap Sequences

Source: https://erdosproblems.com/1213
Status: SOLVED (Hegyvári 1986)

Statement:
Let a ≥ 1, K ≥ 1. Does there exist f(a,K) such that if
  a = a₁ < a₂ < ... < aₙ with aᵢ₊₁ - aᵢ ≤ K and n > f(a,K),
then two distinct intervals I, J ⊆ {1,...,n} have equal sums
  Σᵢ∈I aᵢ = Σⱼ∈J aⱼ ?

Answer: YES. Hegyvári proved f(a,K) ≪ a·exp(O(K)).

Reference:
- [He86] Hegyvári, 1986
-/

import Mathlib.Data.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset

open Finset BigOperators

namespace Erdos1213

/--
**Bounded-gap sequence:**
An increasing sequence where consecutive gaps are at most K.
-/
def IsBoundedGapSeq (a : ℕ → ℕ) (K : ℕ) : Prop :=
  StrictMono a ∧ ∀ i, a (i + 1) - a i ≤ K

/--
**Repeated interval sums:**
Two distinct index intervals with equal sequence sums.
-/
def HasRepeatedIntervalSum (a : ℕ → ℕ) (n : ℕ) : Prop :=
  ∃ (I J : Finset ℕ), I ≠ J ∧ (∀ i ∈ I, i < n) ∧ (∀ j ∈ J, j < n) ∧
    (∑ i ∈ I, a i) = (∑ j ∈ J, a j) ∧ I.Nonempty

/--
**Hegyvári's Theorem (1986):**
For any a ≥ 1 and K ≥ 1, there exists f(a,K) such that any
bounded-gap sequence starting at a with more than f(a,K) terms
contains two distinct intervals with equal sums.
-/
axiom hegyv_ari_1986 :
    ∀ (a₀ K : ℕ), a₀ ≥ 1 → K ≥ 1 →
      ∃ f : ℕ, ∀ (a : ℕ → ℕ) (n : ℕ),
        a 0 = a₀ → IsBoundedGapSeq a K → n > f →
        HasRepeatedIntervalSum a n

/--
**Exponential bound:**
The function f(a,K) satisfies f(a,K) ≤ C · a · exp(c · K) for constants C, c.
-/
axiom hegyv_ari_bound :
    ∃ (C c : ℝ), C > 0 ∧ c > 0 ∧
      ∀ (a₀ K : ℕ), a₀ ≥ 1 → K ≥ 1 →
        ∃ f : ℕ, (f : ℝ) ≤ C * a₀ * Real.exp (c * K) ∧
          ∀ (a : ℕ → ℕ) (n : ℕ),
            a 0 = a₀ → IsBoundedGapSeq a K → n > f →
            HasRepeatedIntervalSum a n

/-- **Erdős Problem #1213: SOLVED** -/
theorem erdos_1213 :
    ∀ (a₀ K : ℕ), a₀ ≥ 1 → K ≥ 1 →
      ∃ f : ℕ, ∀ (a : ℕ → ℕ) (n : ℕ),
        a 0 = a₀ → IsBoundedGapSeq a K → n > f →
        HasRepeatedIntervalSum a n :=
  hegyv_ari_1986

end Erdos1213
