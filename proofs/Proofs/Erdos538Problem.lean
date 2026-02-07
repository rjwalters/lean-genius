/-
Erdős Problem #538: Reciprocal Sums with Bounded Prime Representations

Let r ≥ 2 and A ⊆ {1,...,N} be such that for any m, there are at most r
solutions to m = p · a where p is prime and a ∈ A. Give the best possible
upper bound for Σ_{n ∈ A} 1/n.

## Status: OPEN

Erdős observed the upper bound r · log N / log log N via double counting.
The optimal bound remains open.

## References
- Erdős (1973), [Er73]
- Related: Problems 536, 537
-/

import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

/-
## Section I: Representation Count
-/

/-- The set of pairs (p, a) with p prime, a ∈ A, and m = p · a. -/
noncomputable def primeReprSet (A : Finset ℕ) (m : ℕ) : Finset (ℕ × ℕ) :=
  (A.product (Finset.range (m + 1))).filter (fun pa =>
    pa.2.Prime ∧ m = pa.2 * pa.1 ∧ pa.1 ∈ A)

/-- The number of representations of m as p · a where p is prime and a ∈ A.
    Counts elements a ∈ A such that there exists a prime p with m = p * a. -/
noncomputable def reprCount (A : Finset ℕ) (m : ℕ) : ℕ :=
  (A.filter (fun a => ∃ p : ℕ, p.Prime ∧ m = p * a)).card

/-- A set A has r-bounded prime representations: for every m,
there are at most r solutions to m = p · a with p prime and a ∈ A. -/
def HasBoundedRepr (A : Finset ℕ) (r : ℕ) : Prop :=
  ∀ m : ℕ, reprCount A m ≤ r

/-
## Section II: Basic Properties of reprCount
-/

/-- The representation count of the empty set is 0 for any m. -/
theorem reprCount_empty (m : ℕ) : reprCount ∅ m = 0 := by
  simp [reprCount]

/-- The representation count is bounded by the cardinality of A. -/
theorem reprCount_le_card (A : Finset ℕ) (m : ℕ) :
    reprCount A m ≤ A.card :=
  Finset.card_filter_le A _

/-- The empty set has r-bounded representations for any r. -/
theorem hasBoundedRepr_empty (r : ℕ) : HasBoundedRepr ∅ r := by
  intro m
  simp [reprCount_empty]

/-- If A has r-bounded representations, it also has r'-bounded
    representations for any r' ≥ r. -/
theorem hasBoundedRepr_mono {A : Finset ℕ} {r r' : ℕ} (h : HasBoundedRepr A r)
    (hr : r ≤ r') : HasBoundedRepr A r' := by
  intro m
  exact le_trans (h m) hr

/-- A subset of a set with r-bounded representations also has r-bounded
    representations. -/
theorem hasBoundedRepr_subset {A B : Finset ℕ} {r : ℕ} (h : HasBoundedRepr B r)
    (hAB : A ⊆ B) : HasBoundedRepr A r := by
  intro m
  calc reprCount A m
      = (A.filter (fun a => ∃ p : ℕ, p.Prime ∧ m = p * a)).card := rfl
    _ ≤ (B.filter (fun a => ∃ p : ℕ, p.Prime ∧ m = p * a)).card := by
        apply Finset.card_le_card
        exact Finset.filter_subset_filter _ hAB
    _ = reprCount B m := rfl
    _ ≤ r := h m

/-
## Section III: The Reciprocal Sum
-/

/-- The reciprocal sum Σ_{n ∈ A} 1/n (with 0 contributing nothing). -/
noncomputable def reciprocalSum (A : Finset ℕ) : ℝ :=
  ∑ n ∈ A, if n > 0 then (1 : ℝ) / (n : ℝ) else 0

/-- The reciprocal sum of the empty set is 0. -/
theorem reciprocalSum_empty : reciprocalSum ∅ = 0 := by
  simp [reciprocalSum]

/-- The reciprocal sum is non-negative. -/
theorem reciprocalSum_nonneg (A : Finset ℕ) : 0 ≤ reciprocalSum A := by
  apply Finset.sum_nonneg
  intro n _
  split_ifs with h
  · exact div_nonneg one_pos.le (Nat.cast_nonneg n)
  · le_refl

/-- The reciprocal sum is monotone: if A ⊆ B then Σ_{a ∈ A} 1/a ≤ Σ_{b ∈ B} 1/b. -/
theorem reciprocalSum_mono {A B : Finset ℕ} (h : A ⊆ B) :
    reciprocalSum A ≤ reciprocalSum B := by
  apply Finset.sum_le_sum_of_subset_of_nonneg h
  intro n _ _
  split_ifs with h
  · exact div_nonneg one_pos.le (Nat.cast_nonneg n)
  · le_refl

/-- Adding a positive element to A increases the reciprocal sum. -/
theorem reciprocalSum_insert {A : Finset ℕ} {n : ℕ} (hn : n > 0) (hna : n ∉ A) :
    reciprocalSum A + (1 : ℝ) / (n : ℝ) = reciprocalSum (insert n A) := by
  simp only [reciprocalSum, Finset.sum_insert hna]
  rw [if_pos hn]
  ring

/-
## Section IV: The Problem Statement
-/

/-- **Erdős Problem #538**: Give the best possible upper bound for the
reciprocal sum of A ⊆ {1,...,N} with r-bounded prime representations.

The conjecture seeks the optimal f(r,N) such that
Σ_{n ∈ A} 1/n ≤ f(r,N) whenever HasBoundedRepr A r. -/
def ErdosProblem538 : Prop :=
  ∃ f : ℕ → ℕ → ℝ,
    (∀ r N : ℕ, r ≥ 2 →
      ∀ A : Finset ℕ, A ⊆ Finset.range (N + 1) → HasBoundedRepr A r →
        reciprocalSum A ≤ f r N) ∧
    (∀ g : ℕ → ℕ → ℝ,
      (∀ r N : ℕ, r ≥ 2 →
        ∀ A : Finset ℕ, A ⊆ Finset.range (N + 1) → HasBoundedRepr A r →
          reciprocalSum A ≤ g r N) →
      ∀ r N : ℕ, r ≥ 2 → N ≥ 2 → f r N ≤ g r N)

/-
## Section V: Erdős Upper Bound

Erdős's key observation uses double counting:
  (Σ_{a ∈ A} 1/a) · (Σ_{p ≤ N} 1/p) ≤ r · (Σ_{m ≤ N²} 1/m)

Since Σ_{p ≤ N} 1/p ~ log log N (Mertens' theorem) and
Σ_{m ≤ N²} 1/m ~ 2 log N, this gives:
  Σ_{a ∈ A} 1/a ≤ r · 2 log N / log log N = O(r · log N / log log N)
-/

/-- Erdős proved: Σ_{n ∈ A} 1/n ≪ r · log N / log log N.
    This requires Mertens' theorem and harmonic sum asymptotics. -/
theorem erdos_upper_bound :
    ∃ C : ℝ, C > 0 ∧
      ∀ r N : ℕ, r ≥ 2 → N ≥ 3 →
        ∀ A : Finset ℕ, A ⊆ Finset.range (N + 1) → HasBoundedRepr A r →
          reciprocalSum A ≤ C * (r : ℝ) * Real.log (N : ℝ) /
            Real.log (Real.log (N : ℝ)) := by
  sorry

/-
## Section VI: Trivial Bound Without Constraint
-/

/-- Without the representation constraint, the maximum reciprocal sum
of A ⊆ {1,...,N} is bounded by 1 + log N (harmonic sum bound). -/
theorem harmonic_upper_bound (N : ℕ) (hN : N ≥ 1) :
    ∀ A : Finset ℕ, A ⊆ Finset.range (N + 1) →
      reciprocalSum A ≤ 1 + Real.log (N : ℝ) := by
  sorry

/-
## Section VII: Double Counting Identity

The key combinatorial identity underlying Erdős's argument.
For A ⊆ {1,...,N} with r-bounded representations:

Σ_{a ∈ A} (1/a) · |{p prime : p ≤ N/a}|
  = Σ_{m ≤ N} reprCount(A, m) / m    (approximately)
  ≤ r · Σ_{m ≤ N} 1/m
-/

/-- For each a ∈ A, the number of primes p with pa ≤ N is at most N/a. -/
theorem primes_for_element_bound (A : Finset ℕ) (N : ℕ) (a : ℕ)
    (ha : a ∈ A) (hA : A ⊆ Finset.range (N + 1)) (ha0 : a > 0) :
    ((Finset.range (N + 1)).filter (fun p => p.Prime ∧ p * a ≤ N)).card ≤ N / a := by
  sorry

/-- The double counting inequality: bounding the sum of reprCount.
    Σ_{m=1}^{N} reprCount(A, m) ≤ |A| · N since each a ∈ A contributes
    at most N/a ≤ N values of m = pa. -/
theorem sum_reprCount_bound (A : Finset ℕ) (N : ℕ)
    (hA : A ⊆ Finset.range (N + 1)) :
    ∑ m ∈ Finset.range (N + 1), reprCount A m ≤ A.card * N := by
  sorry

/-
## Section VIII: Connections to Multiplicative Structure
-/

/-- The problem is related to the multiplicative energy of A with primes.
    The set E = {(a₁, a₂) ∈ A × A : ∃ p₁ p₂ prime, p₁a₁ = p₂a₂} measures
    how "multiplicatively correlated" A is with the primes. -/
theorem multiplicative_energy_bound (A : Finset ℕ) (N r : ℕ)
    (hA : A ⊆ Finset.range (N + 1)) (hr : HasBoundedRepr A r) :
    (Finset.card ((A ×ˢ A).filter (fun p =>
      ∃ q₁ q₂ : ℕ, q₁.Prime ∧ q₂.Prime ∧
        q₁ * p.1 = q₂ * p.2)) : ℝ)
    ≤ (r : ℝ) ^ 2 * (A.card : ℝ) := by
  sorry

/-
## Section IX: Special Cases
-/

/-- For r = 1, the constraint means each element of A appears in at most
    one product p · a = m. This forces A to be "multiplicatively thin". -/
theorem r_eq_1_card_bound (A : Finset ℕ) (N : ℕ)
    (hA : A ⊆ Finset.range (N + 1)) (hr : HasBoundedRepr A 1) :
    (A.card : ℝ) ≤ (N : ℝ) := by
  have h := Finset.card_le_card hA
  simp [Finset.card_range] at h
  exact Nat.cast_le.mpr h

/-- A singleton set always has 1-bounded representations. -/
theorem singleton_hasBoundedRepr {a : ℕ} : HasBoundedRepr {a} 1 := by
  intro m
  simp only [reprCount]
  calc (Finset.filter (fun x => ∃ p, p.Prime ∧ m = p * x) {a}).card
      ≤ ({a} : Finset ℕ).card := Finset.card_filter_le _ _
    _ = 1 := Finset.card_singleton a
