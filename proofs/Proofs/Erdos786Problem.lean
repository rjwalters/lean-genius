/-
  Erdős Problem #786: Multiplicative Cardinality Sets

  **Question**: For any ε > 0, is there a set A ⊂ ℕ of density > 1 - ε such that
  a₁···aᵣ = b₁···bₛ with aᵢ, bⱼ ∈ A implies r = s?

  **Status**: OPEN — the main questions remain unsolved.

  **Known Results**:
  - Integers ≡ 2 (mod 4) form such a set with density 1/4
  - Selfridge: consecutive prime construction achieves density 1/e - ε
  - Ruzsa (unpublished): maximum size in {1,...,N} is ≤ (1-c)N for some c > 0

  A "multiplicative cardinality set" is one where equal products must come from
  equal numbers of factors.

  Reference: https://erdosproblems.com/786
-/

import Mathlib.NumberTheory.ArithmeticFunction
import Mathlib.Data.Finset.Card
import Mathlib.Analysis.Asymptotics.Asymptotics
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

namespace Erdos786

open Finset Filter BigOperators
open scoped Topology

/-! ## The Main Definition -/

/--
A set A is a **multiplicative cardinality set** (or MulCardSet) if whenever
a₁ · a₂ · ··· · aᵣ = b₁ · b₂ · ··· · bₛ with all aᵢ, bⱼ ∈ A,
we must have r = s.

In other words, equal products from elements of A must have equal numbers of factors.
-/
def Set.IsMulCardSet {α : Type*} [CommMonoid α] (A : Set α) : Prop :=
  ∀ (a b : Finset α), ↑a ⊆ A → ↑b ⊆ A → a.prod id = b.prod id → a.card = b.card

/-! ## Natural Density -/

/--
A set A ⊂ ℕ has natural density δ if |A ∩ {1,...,n}| / n → δ as n → ∞.
-/
def Set.HasDensity (A : Set ℕ) (δ : ℝ) : Prop :=
  Filter.Tendsto (fun n => (A ∩ Set.Icc 1 n).ncard / n) atTop (𝓝 δ)

/-! ## The Open Questions -/

/--
**Erdős Problem #786 (Part I - Open)**: For any ε > 0, does there exist a
multiplicative cardinality set A ⊂ ℕ with density > 1 - ε?

Can we get arbitrarily close to density 1?
-/
def DensityConjecture : Prop :=
  ∀ ε > 0, ε ≤ 1 →
    ∃ (A : Set ℕ) (δ : ℝ), 0 ∉ A ∧ 1 - ε < δ ∧ A.HasDensity δ ∧ A.IsMulCardSet

/--
**Erdős Problem #786 (Part II - Open)**: For each N, can we find
A ⊂ {1,...,N} of size ≥ (1-o(1))N that is a multiplicative cardinality set?
-/
def FiniteConjecture : Prop :=
  ∃ (A : ℕ → Set ℕ) (f : ℕ → ℝ),
    Asymptotics.IsLittleO atTop f (fun _ : ℕ => (1 : ℝ)) ∧
    ∀ N, A N ⊆ Set.Icc 1 (N + 1) ∧ (1 - f N) * N ≤ (A N).ncard ∧ (A N).IsMulCardSet

/-! ## Known Examples -/

/--
**Example**: The integers ≡ 2 (mod 4) form a multiplicative cardinality set
with density 1/4.

The key observation: 2 (mod 4) means exactly one factor of 2. If a product has
k factors from this set, it has exactly k factors of 2. So equal products from
this set must have equal numbers of factors.
-/
axiom mod4_example :
    let A := {n : ℕ | n % 4 = 2}
    A.HasDensity (1 / 4) ∧ A.IsMulCardSet

/-! ## Selfridge's Construction -/

/--
Consecutive primes: p is a strictly increasing sequence of consecutive primes.
-/
def ConsecutivePrimes {k : ℕ} (p : Fin k.succ → ℕ) : Prop :=
  (∀ i, (p i).Prime) ∧ StrictMono p ∧
  ∀ i : Fin k, ∀ m ∈ Set.Ioo (p i.castSucc) (p i.succ), ¬m.Prime

/--
**Selfridge's Construction**: For any ε > 0, there exists a multiplicative
cardinality set with density 1/e - ε.

Construction: Take consecutive primes p₁ < ··· < pₖ where
∑(1/pᵢ) for i ≤ k is < 1 but ∑(1/pᵢ) for i ≤ k+1 is > 1.
Let A be those integers divisible by exactly one of p₁,...,pₖ.

Then A has density 1/e - ε (for large enough primes) and is a MulCardSet.
-/
axiom selfridge_construction :
    ∀ ε > 0, ε ≤ 1 →
      ∃ (A : Set ℕ), A.HasDensity (1 / Real.exp 1 - ε) ∧ A.IsMulCardSet

/-! ## Upper Bounds -/

/--
**Ruzsa (unpublished)**: The maximum size of a multiplicative cardinality set
in {1,...,N} is at most (1-c)N for some constant c > 0.

This would show that density 1 is impossible, but the proof was never published.
-/
axiom ruzsa_upper_bound_unpublished :
    ∃ c > 0, ∀ᶠ N in atTop,
      ∀ A : Set ℕ, A ⊆ Set.Icc 1 N → A.IsMulCardSet → A.ncard ≤ (1 - c) * N

/--
A simple lower bound: integers with a prime factor > √N form a MulCardSet
of size ≥ (log 2)N.
-/
axiom log2_lower_bound :
    ∀ᶠ N in atTop,
      let A := {n ∈ Set.Icc 1 N | ∃ p : ℕ, p.Prime ∧ p > Nat.sqrt N ∧ p ∣ n}
      A.IsMulCardSet ∧ (Real.log 2 : ℝ) * N ≤ A.ncard

/-! ## Why These Sets Work -/

/--
The key insight: in a MulCardSet, factorization patterns are unique.

For mod 4 residues ≡ 2: each element has exactly one factor of 2.
A product of r elements has exactly r factors of 2.
So equal products must have equal counts.

For Selfridge's construction: each element is divisible by exactly one
of the selected primes. A product of r elements has "exactly r prime signatures"
in a suitable sense, forcing equal counts.
-/

/-! ## Examples -/

/-- 2 ≡ 2 (mod 4) -/
example : (2 : ℕ) % 4 = 2 := by native_decide

/-- 6 ≡ 2 (mod 4) -/
example : (6 : ℕ) % 4 = 2 := by native_decide

/-- 10 ≡ 2 (mod 4) -/
example : (10 : ℕ) % 4 = 2 := by native_decide

/-- Product example: 2 · 6 = 12 and we'd need 2 factors from the set -/
example : (2 : ℕ) * 6 = 12 := by native_decide

end Erdos786
