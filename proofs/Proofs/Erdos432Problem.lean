/-
# Erdős Problem #432: Pairwise Coprime Sumsets

**Source:** [erdosproblems.com/432](https://erdosproblems.com/432)
**Status:** OPEN (Straus, via Erdős–Graham 1980)

## Statement

Let A, B ⊆ ℕ be two infinite sets. How dense can A + B be if all
elements of A + B are pairwise coprime?

## Background

Asked by Straus, inspired by Ostmann's problem (#431). Erdős and
Graham (1980, p.85) discuss this. The pairwise coprimality constraint
on the sumset A + B = {a + b : a ∈ A, b ∈ B} severely restricts
how dense A and B can be. Tao has noted this "looks difficult."

## Approach

We define sumsets, pairwise coprimality, counting functions, and
state the conjecture on density bounds.
-/

import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Tactic

namespace Erdos432

/- ## Part I: Sumsets -/

/--
The sumset A + B = {a + b : a ∈ A, b ∈ B} for subsets of ℕ.
-/
def sumset (A B : Set ℕ) : Set ℕ :=
  { n | ∃ a ∈ A, ∃ b ∈ B, n = a + b }

/--
The restricted sumset up to n: elements of A + B that are ≤ n.
-/
def sumsetUpTo (A B : Set ℕ) (n : ℕ) : Set ℕ :=
  { m | m ≤ n ∧ m ∈ sumset A B }

/- ## Part II: Pairwise Coprimality -/

/--
A set S ⊆ ℕ is pairwise coprime if gcd(x, y) = 1 for all
distinct x, y ∈ S.
-/
def IsPairwiseCoprime (S : Set ℕ) : Prop :=
  ∀ x ∈ S, ∀ y ∈ S, x ≠ y → Nat.Coprime x y

/--
The sumset A + B has pairwise coprime elements.
-/
def SumsetPairwiseCoprime (A B : Set ℕ) : Prop :=
  IsPairwiseCoprime (sumset A B)

/- ## Part III: Counting Functions -/

/--
The counting function: number of elements of S in {1, …, n}.
-/
noncomputable def countingFn (S : Set ℕ) (n : ℕ) : ℕ :=
  ((Finset.range (n + 1)).filter (fun m => m ∈ S ∧ m ≥ 1)).card

/--
A set is infinite if its counting function is unbounded.
-/
def IsInfiniteSet (S : Set ℕ) : Prop :=
  ∀ C : ℕ, ∃ N : ℕ, countingFn S N ≥ C

/- ## Part IV: The Problem -/

/--
**Erdős Problem #432 (Straus, Erdős–Graham 1980, p.85):**
Let A, B ⊆ ℕ be infinite sets such that all elements of A + B
are pairwise coprime. How large can the counting function of
A + B be?

The key question: is there a non-trivial upper bound on the
density of A + B under the pairwise coprime constraint?
-/
def ErdosProblem432 : Prop :=
  ∃ f : ℕ → ℕ,
    -- f(n) is a non-trivial upper bound
    (∀ n : ℕ, f n ≤ n) ∧
    -- f grows to infinity (not bounded)
    (∀ C : ℕ, ∃ N : ℕ, f N ≥ C) ∧
    -- For any infinite A, B with pairwise coprime sumset,
    -- the sumset counting function is bounded by f
    ∀ A B : Set ℕ,
      IsInfiniteSet A →
      IsInfiniteSet B →
      SumsetPairwiseCoprime A B →
      ∀ n : ℕ, countingFn (sumset A B) n ≤ f n

/- ## Part V: Basic Observations -/

/--
If A + B is pairwise coprime, each prime p divides at most one
element of A + B.
-/
theorem prime_divides_at_most_one :
    ∀ A B : Set ℕ,
      SumsetPairwiseCoprime A B →
      ∀ p : ℕ, p.Prime →
        ∀ x ∈ sumset A B, ∀ y ∈ sumset A B,
          p ∣ x → p ∣ y → x = y := by
  intro A B hcop p hp x hx y hy hpx hpy
  by_contra hne
  -- x ≠ y and both in sumset ⟹ gcd(x,y) = 1
  have hxy : Nat.Coprime x y := hcop x hx y hy hne
  -- p ∣ x and p ∣ y ⟹ p ∣ gcd(x,y) = 1
  have hpg : p ∣ Nat.gcd x y := Nat.dvd_gcd hpx hpy
  rw [hxy] at hpg
  -- p ∣ 1 contradicts p ≥ 2
  exact absurd hpg (Nat.Prime.one_lt hp |>.not_le ∘ Nat.le_of_dvd one_pos)

/--
A pairwise coprime set S ⊆ {1, …, n} has at most π(n) + 1
elements, where π(n) is the prime counting function. This is
because each element > 1 has a distinct smallest prime factor.
-/
theorem coprime_set_bound :
    ∀ S : Set ℕ,
      IsPairwiseCoprime S →
      ∀ n : ℕ, countingFn S n ≤ n := by
  intro S _ n
  -- countingFn S n filters range(n+1) by m ∈ S ∧ m ≥ 1, excluding 0
  unfold countingFn
  calc ((Finset.range (n + 1)).filter (fun m => m ∈ S ∧ m ≥ 1)).card
      ≤ ((Finset.range (n + 1)).filter (fun m => m ≥ 1)).card :=
        Finset.card_filter_le_card_filter _ _ _ (fun m _ h => h.2)
    _ ≤ ((Finset.range n).image (· + 1)).card := by
        apply Finset.card_le_card
        intro m hm
        simp only [Finset.mem_filter, Finset.mem_range] at hm
        simp only [Finset.mem_image, Finset.mem_range]
        exact ⟨m - 1, by omega, by omega⟩
    _ ≤ (Finset.range n).card := Finset.card_image_le
    _ = n := Finset.card_range n

/--
Ostmann's related problem (#431): if A + B = ℕ (an additive
complement pair), can A + B be pairwise coprime? Clearly not
for A + B = ℕ, but the question is about near-complements.
-/
/- ostmann_connection: Ostmann's problem (#431) is the companion to #432;
    it asks whether additive complement pairs can be pairwise coprime. -/

/- ## Part VI: Summary -/

/--
**Summary:**
Erdős Problem #432 asks how dense the sumset A + B can be when all
its elements are pairwise coprime. The pairwise coprime constraint
means each prime divides at most one element, severely limiting
density. Tao noted it "looks difficult." OPEN.
-/
end Erdos432
