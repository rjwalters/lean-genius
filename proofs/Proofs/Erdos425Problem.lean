/-
Erdős Problem #425: Multiplicative Sidon Sets

Source: https://erdosproblems.com/425
Status: PARTIALLY SOLVED

Statement:
Let F(n) be the maximum size of a subset A ⊆ {1, ..., n} such that all
pairwise products ab (with a < b) are distinct.

Questions:
1. Is there a constant c such that F(n) = π(n) + (c + o(1))·n^(3/4)·(log n)^(-3/2)?
2. If products a₁···aᵣ (with a₁ < ··· < aᵣ) are all distinct, is |A| ≤ π(n) + O(n^((r+1)/(2r)))?

Key Results:
- Erdős (1968): π(n) + c₁·n^(3/4)·(log n)^(-3/2) ≤ F(n) ≤ π(n) + c₂·n^(3/4)·(log n)^(-3/2)
- The set of primes ≤ n gives F(n) ≥ π(n) (products distinct by unique factorization)
- The order of magnitude is determined, but the exact constant c is unknown

Real Number Version:
- What is max |A| for A ⊂ [1,x] with |ab - cd| ≥ 1 for distinct a,b,c,d ∈ A?
- Erdős conjectured |A| = o(x) (FALSE!)
- Alexander disproved this: |A| ≫ x is possible using Sidon sets

References:
- [Er68] Erdős (1968): On some applications of graph theory to number theoretic problems
- [Er73] Erdős (1973): Problems and results on combinatorial number theory
- [ErGr80] Erdős-Graham (1980): Old and new problems and results in combinatorial number theory
-/

import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.NumberTheory.Primorial
import Mathlib.Data.Real.Basic

namespace Erdos425

/-
## Part I: Basic Definitions
-/

/--
**A subset of {1, ..., n}:**
-/
def SubsetOfInterval (n : ℕ) := {A : Finset ℕ // ∀ a ∈ A, 1 ≤ a ∧ a ≤ n}

/--
**Ordered pair (a, b) with a < b:**
-/
def OrderedPair (A : Finset ℕ) := {p : ℕ × ℕ // p.1 ∈ A ∧ p.2 ∈ A ∧ p.1 < p.2}

/--
**The product set {ab : a, b ∈ A, a < b}:**
All pairwise products of distinct elements from A.
-/
def ProductSet (A : Finset ℕ) : Finset ℕ :=
  (A.product A).filter (fun p => p.1 < p.2) |>.image (fun p => p.1 * p.2)

/--
**Multiplicative Sidon Set (B₂⁺):**
A set A is a multiplicative Sidon set if all pairwise products ab (a < b) are distinct.
Equivalently, ab = cd implies {a,b} = {c,d}.
-/
def IsMultiplicativeSidon (A : Finset ℕ) : Prop :=
  ∀ a b c d : ℕ, a ∈ A → b ∈ A → c ∈ A → d ∈ A →
    a < b → c < d → a * b = c * d → (a = c ∧ b = d)

/--
**Alternative characterization:**
The map (a, b) ↦ ab is injective on ordered pairs from A.
-/
def IsMultiplicativeSidon' (A : Finset ℕ) : Prop :=
  ((A.product A).filter (fun p => p.1 < p.2)).card =
    ((A.product A).filter (fun p => p.1 < p.2) |>.image (fun p => p.1 * p.2)).card

/-
## Part II: The Function F(n)
-/

/--
**F(n):** Maximum size of a multiplicative Sidon subset of {1, ..., n}.
-/
noncomputable def F (n : ℕ) : ℕ :=
  Finset.sup' (Finset.filter
    (fun A : Finset ℕ => A.card ≤ n ∧ (∀ a ∈ A, a ≤ n) ∧ IsMultiplicativeSidon A)
    (Finset.powerset (Finset.range (n + 1))))
    (by
      use ∅
      simp [IsMultiplicativeSidon])
    Finset.card

/--
**Primes form a multiplicative Sidon set:**
By unique prime factorization, if p₁·p₂ = q₁·q₂ with p₁ < p₂ and q₁ < q₂ primes,
then {p₁, p₂} = {q₁, q₂}. Axiomatized since the formal proof requires
unique factorization machinery.
-/
/--
**Lower bound: F(n) ≥ π(n):**
The primes ≤ n form a multiplicative Sidon set of size π(n).
-/
/-
## Part III: Erdős's Bounds
-/

/--
**Erdős's bounds (1968):**
There exist constants 0 < c₁ ≤ c₂ such that
  π(n) + c₁·n^(3/4)·(log n)^(-3/2) ≤ F(n) ≤ π(n) + c₂·n^(3/4)·(log n)^(-3/2)
-/
axiom erdos_bounds :
    ∃ c₁ c₂ : ℝ, c₁ > 0 ∧ c₂ > 0 ∧ c₁ ≤ c₂ ∧
      ∀ n : ℕ, n ≥ 2 →
        let π_n := ((Finset.range (n + 1)).filter Nat.Prime).card
        let extra := (n : ℝ)^(3/4 : ℝ) * (Real.log n)^(-(3/2) : ℝ)
        π_n + c₁ * extra ≤ F n ∧ (F n : ℝ) ≤ π_n + c₂ * extra

/--
**The main question (OPEN):**
Is there a constant c such that F(n) = π(n) + (c + o(1))·n^(3/4)·(log n)^(-3/2)?
-/
def MainQuestion : Prop :=
  ∃ c : ℝ, ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N,
    let π_n := ((Finset.range (n + 1)).filter Nat.Prime).card
    let extra := (n : ℝ)^(3/4 : ℝ) * (Real.log n)^(-(3/2) : ℝ)
    |(F n : ℝ) - (π_n + c * extra)| ≤ ε * extra

/-
## Part IV: The r-Product Generalization
-/

/--
**r-Multiplicative Sidon Set:**
All r-fold products a₁···aᵣ (with a₁ < ··· < aᵣ) are distinct.
-/
def IsRMultiplicativeSidon (A : Finset ℕ) (r : ℕ) : Prop :=
  ∀ S T : Finset ℕ, S ⊆ A → T ⊆ A → S.card = r → T.card = r →
    S.prod id = T.prod id → S = T

/--
**Conjectured bound for r-products:**
If A ⊆ {1, ..., n} is r-multiplicatively Sidon, then |A| ≤ π(n) + O(n^((r+1)/(2r))).

For r = 2: |A| ≤ π(n) + O(n^(3/4))
For r = 3: |A| ≤ π(n) + O(n^(2/3))
For r → ∞: |A| → π(n) + O(n^(1/2))
-/
def RProductConjecture : Prop :=
  ∀ r : ℕ, r ≥ 2 →
    ∃ C : ℝ, C > 0 ∧ ∀ n : ℕ, ∀ A : Finset ℕ,
      (∀ a ∈ A, a ≤ n) → IsRMultiplicativeSidon A r →
        (A.card : ℝ) ≤ ((Finset.range (n + 1)).filter Nat.Prime).card +
          C * (n : ℝ)^((r + 1 : ℝ) / (2 * r))

/-
## Part V: The Real Number Version
-/

/--
**Real multiplicative Sidon set:**
A ⊂ [1, x] such that |ab - cd| ≥ 1 for all distinct pairs (a,b), (c,d) ∈ A.
-/
def RealMultSidon (A : Set ℝ) : Prop :=
  ∀ a b c d : ℝ, a ∈ A → b ∈ A → c ∈ A → d ∈ A →
    a ≠ b → c ≠ d → (a, b) ≠ (c, d) → (a, b) ≠ (d, c) →
    |a * b - c * d| ≥ 1

/--
**Erdős's conjecture (FALSE!):**
Erdős conjectured that max |A| = o(x) for A ⊂ [1, x] with RealMultSidon A.

This was disproved by Alexander!
-/
/--
**Alexander's construction:**
Let B ⊆ [1, X²] be a Sidon set of integers with |B| ≫ X.
Let A = {X · e^(b/X²) : b ∈ B}.

Then |ab - cd| ≥ X² · |1 - e^(1/X²)| ≫ 1 for distinct pairs, and |A| ≫ X.
After rescaling, this gives a set of size Θ(x) in [1, O(x)].
-/
axiom alexander_construction :
    ∃ c : ℝ, c > 0 ∧ ∀ x : ℝ, x > 0 →
      ∃ A : Finset ℝ, (∀ a ∈ A, 1 ≤ a ∧ a ≤ x) ∧ RealMultSidon A ∧
        (A.card : ℝ) ≥ c * x

/-
## Part VI: Connection to Additive Sidon Sets
-/

/--
**Sidon set (additive, B₂):**
A set S where all pairwise sums a + b (a ≤ b) are distinct.
-/
def IsSidonSet (S : Finset ℕ) : Prop :=
  ∀ a b c d : ℕ, a ∈ S → b ∈ S → c ∈ S → d ∈ S →
    a ≤ b → c ≤ d → a + b = c + d → (a = c ∧ b = d)

/--
**Multiplicative Sidon via logarithms:**
Taking logarithms converts multiplicative Sidon to additive Sidon.
If A is multiplicative Sidon (all products ab distinct), then
{log a : a ∈ A} is additive Sidon (all sums log a + log b distinct),
since log(ab) = log a + log b.
-/
/--
**Classical Sidon set bounds:**
Max |S| for additive Sidon S ⊆ {1, ..., n} is (1 + o(1))·√n.
-/
/-
## Part VII: Examples
-/

/--
**Example: {1, 2, 3, 6} is NOT multiplicative Sidon**
1·6 = 6 = 2·3, so products are not distinct.
-/
example : ¬IsMultiplicativeSidon {1, 2, 3, 6} := by
  intro h
  have : 1 * 6 = 2 * 3 := by norm_num
  have := h 1 6 2 3 (by simp) (by simp) (by simp) (by simp)
    (by norm_num) (by norm_num) this
  simp at this

/-
## Part VIII: Summary
-/

/--
**Erdős Problem #425: Summary**

PROBLEM:
1. Find F(n) = max |A| for multiplicative Sidon A ⊆ {1,...,n}
2. Is F(n) = π(n) + (c + o(1))·n^(3/4)·(log n)^(-3/2) for some constant c?
3. For r-fold products, is |A| ≤ π(n) + O(n^((r+1)/(2r)))?

STATUS: PARTIALLY SOLVED

KNOWN:
- π(n) + c₁·n^(3/4)·(log n)^(-3/2) ≤ F(n) ≤ π(n) + c₂·n^(3/4)·(log n)^(-3/2)
- The order of magnitude is determined
- The exact constant c (if it exists) is unknown

REAL VERSION:
- Erdős conjectured max |A| = o(x) for [1,x] - FALSE!
- Alexander showed |A| ≫ x is achievable using Sidon sets

KEY INSIGHT: Primes form the core of any large multiplicative Sidon set.
-/
theorem erdos_425_summary :
    -- Erdős bounds exist
    (∃ c₁ c₂ : ℝ, c₁ > 0 ∧ c₂ > 0 ∧ c₁ ≤ c₂ ∧
      ∀ n : ℕ, n ≥ 2 →
        let π_n := ((Finset.range (n + 1)).filter Nat.Prime).card
        let extra := (n : ℝ)^(3/4 : ℝ) * (Real.log n)^(-(3/2) : ℝ)
        π_n + c₁ * extra ≤ F n ∧ (F n : ℝ) ≤ π_n + c₂ * extra) ∧
    -- Alexander's counterexample to real conjecture
    (∃ c : ℝ, c > 0 ∧ ∀ x : ℝ, x > 0 →
      ∃ A : Finset ℝ, (∀ a ∈ A, 1 ≤ a ∧ a ≤ x) ∧ RealMultSidon A ∧
        (A.card : ℝ) ≥ c * x) :=
  ⟨erdos_bounds, alexander_construction⟩

end Erdos425
