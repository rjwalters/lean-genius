/-
Erdős Problem #433: Maximum Frobenius Numbers

Source: https://erdosproblems.com/433
Status: SOLVED (Dixmier, 1990)

Statement:
If A ⊂ ℕ is a finite set, let G(A) denote the greatest integer which is not
expressible as a finite sum of elements from A (with repetitions allowed).

Let g(k,n) = max G(A) where the maximum is over all A ⊆ {1,...,n} of size k
with gcd(A) = 1.

Question: Is it true that g(k,n) ~ n²/(k-1)?

Answer: YES (Dixmier, 1990)

Dixmier proved:
  ⌊(n-2)/(k-1)⌋(n-k+1) - 1 ≤ g(k,n) ≤ (⌊(n-1)/(k-1)⌋ - 1)n - 1

This gives g(k,n) ~ n²/(k-1) as n → ∞ with k fixed.

Key Concepts:
- The Frobenius number G(A): largest non-representable integer
- For gcd(A) = 1, G(A) is finite (fundamental theorem)
- The classical Sylvester-Frobenius formula: G({a,b}) = ab - a - b
- Extremal sets that maximize G(A) among k-subsets of {1,...,n}

References:
- Erdős-Graham (1972): Proved g(k,n) < 2n²/k
- Dixmier (1990): Proved the asymptotic g(k,n) ~ n²/(k-1)
-/

import Mathlib
import Proofs.Erdos433Aristotle

open Nat Finset BigOperators

namespace Erdos433

/-
## Part I: The Frobenius Number
-/

/--
**Numerical Semigroup:**
The set of all non-negative integer linear combinations of elements of A.
-/
def NumericalSemigroup (A : Finset ℕ) : Set ℕ :=
  {n : ℕ | ∃ (coeffs : A → ℕ), n = ∑ a : A, coeffs a * a.val}

/--
**The Frobenius Number G(A):**
The largest integer not representable as a sum of elements from A.
Defined only when gcd(A) = 1 (otherwise infinitely many are missing).
-/
noncomputable def frobeniusNumber (A : Finset ℕ) : ℕ :=
  sSup {n : ℕ | n ∉ NumericalSemigroup A}

/--
Notation: G(A) for the Frobenius number.
-/
notation "G(" A ")" => frobeniusNumber A

/-
## Part II: Fundamental Properties
-/

/--
**Sylvester-Frobenius Formula:**
For two coprime positive integers a, b:
  G({a, b}) = ab - a - b

This is the classical result from 1884.
-/
axiom sylvester_frobenius (a b : ℕ) (ha : a ≥ 1) (hb : b ≥ 1) (hcop : Nat.Coprime a b) :
    G(({a, b} : Finset ℕ)) = a * b - a - b

/--
**Example: G({3, 5}) = 7**
The numbers 1, 2, 4, 7 are not representable; 7 is the largest.
-/
theorem frobenius_3_5 : G(({3, 5} : Finset ℕ)) = 7 := by
  have h : Nat.Coprime 3 5 := by decide
  rw [sylvester_frobenius 3 5 (by norm_num) (by norm_num) h]

/--
**Example: G({2, 3}) = 1**
Only 1 is not representable as 2a + 3b.
-/
theorem frobenius_2_3 : G(({2, 3} : Finset ℕ)) = 1 := by
  have h : Nat.Coprime 2 3 := by decide
  rw [sylvester_frobenius 2 3 (by norm_num) (by norm_num) h]

/-
**Fundamental Theorem:**
If gcd(A) = 1 and A is nonempty, then G(A) is finite.
More precisely, there exists N such that all n ≥ N are representable.
-/

/-
**Monotonicity:**
Adding more elements to A can only decrease G(A) (more combinations available).
-/

/-
## Part III: The Function g(k, n)
-/

/--
**Coprimality condition:**
A finite set A ⊆ ℕ has gcd equal to 1.
-/
def SetGCDOne (A : Finset ℕ) : Prop := A.gcd id = 1

/--
**The function g(k, n):**
Maximum Frobenius number over all k-element subsets of {0,...,n} with gcd = 1.
-/
noncomputable def g (k n : ℕ) : ℕ :=
  sSup {v : ℕ | ∃ A : Finset ℕ, A ⊆ Finset.range (n + 1) ∧ A.card = k ∧ SetGCDOne A ∧ v = G(A)}

/-
## Part IV: Erdős-Graham Bounds
-/

/-
**Erdős-Graham Upper Bound (1972):**
g(k, n) < 2n²/k

This was the first general bound.
-/

/-
**Lower Bound Construction:**
For k ≥ 2, there exist sets A achieving:
  G(A) ≥ n²/(k-1) - 5n

The extremal set is approximately {n-k+1, n-k+2, ..., n}.
-/

/-
## Part V: Dixmier's Theorem (1990)
-/

/--
**Dixmier's Lower Bound:**
For all 2 ≤ k < n:
  g(k, n) ≥ ⌊(n-2)/(k-1)⌋ · (n-k+1) - 1
-/
axiom dixmier_lower_bound (k n : ℕ) (hk : 2 ≤ k) (hkn : k < n) :
    g k n ≥ (n - 2) / (k - 1) * (n - k + 1) - 1

/--
**Dixmier's Upper Bound:**
For all 2 ≤ k < n:
  g(k, n) ≤ (⌊(n-1)/(k-1)⌋ - 1) · n - 1
-/
axiom dixmier_upper_bound (k n : ℕ) (hk : 2 ≤ k) (hkn : k < n) :
    g k n ≤ ((n - 1) / (k - 1) - 1) * n - 1

/--
**Asymptotic Formula:**
As n → ∞ with k fixed:
  g(k, n) ~ n²/(k-1)

This confirms Erdős and Graham's conjecture.
-/
def AsymptoticFormula : Prop :=
  ∀ (k : ℕ), k ≥ 2 → ∀ (ε : ℝ), ε > 0 → ∃ N : ℕ, ∀ n ≥ N,
    (1 - ε) * (n ^ 2 : ℝ) / ((k : ℝ) - 1) ≤ (g k n : ℝ) ∧
    (g k n : ℝ) ≤ (1 + ε) * (n : ℝ) ^ 2 / ((k : ℝ) - 1)

/--
**Erdős Problem #433: SOLVED**
The asymptotic formula g(k,n) ~ n²/(k-1) is true.
-/
axiom erdos_433_solved : AsymptoticFormula

/-
## Part VI: Exact Values
-/

/-
**Dixmier's Exact Formula:**
When (k-1) | n, (k-1) | (n-1), or (k-1) | (n-2), exact values are known.
-/

/--
**Special Case k = 2:**
g(2, n) = G({n-1, n}) = (n-1)·n - (n-1) - n = n² - 3n + 1

Using Sylvester-Frobenius when gcd(n-1, n) = 1.
-/
-- Helper: Every natural number is in NumericalSemigroup {0, 1}.
-- Proof: take coefficient m for element 1, coefficient 0 for element 0.
private lemma every_mem_num_sem_01 (m : ℕ) :
    m ∈ NumericalSemigroup ({0, 1} : Finset ℕ) := by
  simp only [NumericalSemigroup, Set.mem_setOf_eq]
  refine ⟨fun a => if a.val = 1 then m else 0, ?_⟩
  -- Rewrite Finset.univ for ↥{0,1} to the explicit pair {⟨0,_⟩, ⟨1,_⟩}, then compute
  have huniv : (Finset.univ : Finset ↥({0, 1} : Finset ℕ)) =
      {⟨0, by simp⟩, ⟨1, by simp⟩} := by
    ext ⟨x, hx⟩
    simp only [Finset.mem_univ, true_iff, Finset.mem_insert, Finset.mem_singleton,
               Subtype.mk.injEq]
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx; exact hx
  rw [huniv, Finset.sum_insert
      (show (⟨0, by simp⟩ : ↥({0, 1} : Finset ℕ)) ∉
             ({⟨1, by simp⟩} : Finset ↥({0, 1} : Finset ℕ)) from by
        simp [Finset.mem_singleton, Subtype.mk.injEq]),
      Finset.sum_singleton]
  norm_num

-- G({0, 1}) = 0: every natural is representable using {0, 1}.
private lemma frobenius_zero_one : G(({0, 1} : Finset ℕ)) = 0 := by
  simp only [frobeniusNumber]
  suffices h : {n : ℕ | n ∉ NumericalSemigroup ({0, 1} : Finset ℕ)} = ∅ by
    rw [h]; simp
  ext m
  simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_not]
  exact every_mem_num_sem_01 m

theorem g_two (n : ℕ) (hn : n ≥ 3) : g 2 n = n ^ 2 - 3 * n + 1 := by
  apply Nat.le_antisymm
  · -- Upper bound: g 2 n ≤ n² - 3n + 1
    -- Every G(A) for valid 2-element A is ≤ n²-3n+1; achieved by A = {n-1,n}.
    unfold g
    apply csSup_le
    · -- Nonemptiness: {n-1, n} witnesses that G({n-1,n}) is in the set
      exact ⟨G(({n - 1, n} : Finset ℕ)), {n - 1, n},
             Erdos433Aristotle.pair_subset_range n (by omega),
             Erdos433Aristotle.pair_card n (by omega),
             Erdos433Aristotle.finset_gcd_pred_self n (by omega),
             rfl⟩
    · -- Upper bound: for any valid set A with G(A) in the set, G(A) ≤ n²-3n+1
      intro v ⟨A, hA_sub, hA_card, hA_gcd, hvA⟩
      rw [hvA]
      -- Extract the two elements a, b from the 2-element finset A
      rw [Finset.card_eq_two] at hA_card
      obtain ⟨a, b, hab, rfl⟩ := hA_card
      -- Get bounds from A ⊆ range(n+1)
      have ha_le : a ≤ n := by
        have : a ∈ Finset.range (n + 1) := hA_sub (Finset.mem_insert_self a _)
        simpa using Nat.lt_succ_iff.mp (Finset.mem_range.mp this)
      have hb_le : b ≤ n := by
        have : b ∈ Finset.range (n + 1) := hA_sub (by simp)
        simpa using Nat.lt_succ_iff.mp (Finset.mem_range.mp this)
      -- Extract gcd = 1 from SetGCDOne {a, b}
      have hgcd : Nat.gcd a b = 1 := by
        have hag := hA_gcd
        unfold SetGCDOne at hag  -- hag : ({a,b} : Finset ℕ).gcd id = 1
        apply Nat.dvd_one.mp
        -- Nat.gcd a b divides each element, hence divides Finset.gcd
        have hfin : Nat.gcd a b ∣ ({a, b} : Finset ℕ).gcd id :=
          Finset.dvd_gcd (fun x hx => by
            simp only [Finset.mem_insert, Finset.mem_singleton, id_eq] at hx ⊢
            cases hx with
            | inl h => rw [h]; exact Nat.gcd_dvd_left a b
            | inr h => rw [h]; exact Nat.gcd_dvd_right a b)
        rwa [hag] at hfin
      -- Case on whether a or b is zero (degenerate case: G = 0)
      rcases Nat.eq_zero_or_pos a with rfl | ha_pos
      · -- a = 0: gcd(0, b) = b = 1, so b = 1, G({0,1}) = 0
        simp only [Nat.gcd_zero_left] at hgcd; subst hgcd
        simp [frobenius_zero_one]
      · rcases Nat.eq_zero_or_pos b with rfl | hb_pos
        · -- b = 0: gcd(a, 0) = a = 1, so a = 1, G({1,0}) = G({0,1}) = 0
          simp only [Nat.gcd_zero_right] at hgcd; subst hgcd
          rw [show ({1, 0} : Finset ℕ) = {0, 1} from by ext; simp [or_comm]]
          simp [frobenius_zero_one]
        · -- a ≥ 1, b ≥ 1: apply Sylvester-Frobenius then arithmetic bound
          rw [sylvester_frobenius a b ha_pos hb_pos hgcd]
          -- G({a, b}) = a*b - a - b ≤ n²-3n+1
          -- Need a ≤ n-1 or b ≤ n-1 (since a ≠ b and both ≤ n)
          rcases le_or_lt a b with hab2 | hab2
          · -- a ≤ b, a < b (since a ≠ b), so a ≤ n-1
            exact Erdos433Aristotle.frobenius_ub_pair a b n hn ha_pos hb_pos
              (by omega : a ≤ n - 1) hb_le
          · -- b < a ≤ n, so b ≤ n-1; use symmetry a*b - a - b = b*a - b - a
            have heq : a * b - a - b = b * a - b - a := by rw [Nat.mul_comm]; omega
            rw [heq]
            exact Erdos433Aristotle.frobenius_ub_pair b a n hn hb_pos ha_pos
              (by omega : b ≤ n - 1) ha_le
  · -- Lower bound: n² - 3n + 1 ≤ g 2 n, from Dixmier's lower bound
    have h := dixmier_lower_bound 2 n (by omega) (by omega)
    -- Simplify: (2-1) = 1, so (n-2)/1 = n-2, and (n-2)*(n-1) - 1 = n²-3n+1
    simp only [show (2 : ℕ) - 1 = 1 from rfl, Nat.div_one] at h
    linarith [Erdos433Aristotle.dixmier_k2_arith n hn]

/-
## Part VII: Extremal Sets
-/

/-
**Extremal Set Structure:**
The sets achieving g(k, n) are concentrated near {n-k+1, ..., n}.

When these elements have gcd = 1, the Frobenius number is maximized.
-/

/-
**Why Large Elements Maximize G(A):**
If all elements of A are near n, then their linear combinations
leave more gaps, maximizing the Frobenius number.
-/

/-
## Part VIII: Connection to Classical Frobenius Problem
-/

/-
**The Chicken McNugget Theorem:**
With nuggets sold in packs of 6, 9, 20, the largest non-buyable quantity is 43.
G({6, 9, 20}) = 43. This popularized the Frobenius number problem.
-/

/--
**General Upper Bound (Schur):**
For a, b coprime: G({a, b}) = ab - a - b < ab.
-/
theorem schur_bound (a b : ℕ) (ha : a ≥ 1) (hb : b ≥ 1) (hcop : Nat.Coprime a b) :
    G(({a, b} : Finset ℕ)) < a * b := by
  rw [sylvester_frobenius a b ha hb hcop]
  calc a * b - a - b ≤ a * b - a := Nat.sub_le _ _
    _ < a * b := Nat.sub_lt (Nat.mul_pos ha hb) (by omega)

/-
**Frobenius for 3 generators:**
No closed formula exists for G({a, b, c}), but bounds are known.
Ramirez Alfonsin showed the problem is NP-hard in general.
-/

/-
## Part IX: Counting Gaps
-/

/-
**Number of Gaps:**
For coprime a, b, the number of gaps (non-representable numbers) is:
  (a-1)(b-1)/2

This is exactly half the "conductor" ab - a - b + 1.
-/

/-
**Symmetric Property:**
The gaps for {a, b} are symmetric around (ab - a - b)/2.
If n is a gap, so is (ab - a - b) - n.
-/

/-
## Part X: Summary
-/

/--
**Erdős Problem #433: Summary**

PROBLEM:
For g(k,n) = max{G(A) : A ⊆ {1,...,n}, |A| = k, gcd(A) = 1},
prove that g(k,n) ~ n²/(k-1).

STATUS: SOLVED (Dixmier, 1990)

BOUNDS:
- Upper: g(k,n) ≤ (⌊(n-1)/(k-1)⌋ - 1)·n - 1
- Lower: g(k,n) ≥ ⌊(n-2)/(k-1)⌋·(n-k+1) - 1

Both are ~ n²/(k-1), confirming the conjecture.

KEY INSIGHTS:
1. Extremal sets are concentrated near n
2. The Sylvester-Frobenius formula is key for k = 2
3. Larger elements in A lead to larger Frobenius numbers
4. The asymptotic follows from careful analysis of floor functions
-/
theorem erdos_433_summary :
    -- Dixmier's bounds bracket the asymptotic
    (∀ k n : ℕ, 2 ≤ k → k < n →
      (n - 2) / (k - 1) * (n - k + 1) - 1 ≤ g k n ∧
      g k n ≤ ((n - 1) / (k - 1) - 1) * n - 1) ∧
    -- The asymptotic formula holds
    AsymptoticFormula := by
  constructor
  · intro k n hk hkn
    constructor
    · exact dixmier_lower_bound k n hk hkn
    · exact dixmier_upper_bound k n hk hkn
  · exact erdos_433_solved

/--
**Status Theorem:**
-/
theorem erdos_433_status :
    -- The asymptotic g(k,n) ~ n²/(k-1) is proved
    AsymptoticFormula := erdos_433_solved

end Erdos433
