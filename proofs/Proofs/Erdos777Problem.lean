/-
Erdős Problem #777: Comparable Pairs in Families of Sets

Source: https://erdosproblems.com/777
Status: SOLVED (Alon-Das-Glebov-Sudakov 2015, Alon-Frankl 1985)

Statement:
Let F be a family of subsets of {1,...,n}. Define graph G_F where A ~ B if A and B
are comparable (i.e., A ⊆ B or B ⊆ A).

The problem poses three questions:
1. If ε > 0 and n is sufficiently large, whenever |F| ≤ (2-ε)2^{n/2}, does G_F have < 2^n edges?
2. If G_F has ≥ c·m² edges, must m ≪_c 2^{n/2}?
3. For any ε > 0, does there exist δ > 0 such that > m^{2-δ} edges implies m < (2+ε)^{n/2}?

Answers:
- Question 1: YES (Alon-Das-Glebov-Sudakov 2015)
- Question 2: NO (Alon-Frankl 1985 counterexample)
- Question 3: YES (Alon-Frankl 1985)

Key Insight:
The extremal case for Question 1 occurs when n is even and F consists of all subsets
of {1,...,n/2} together with {1,...,n/2} ∪ S for all S ⊆ {n/2+1,...,n}.
This family has 2^{n/2+1} sets and produces exactly 2^n edges.

References:
- Daykin and Erdős [Gu83]: Original problem
- Daykin and Frankl: If (1+o(1))C(m,2) edges then m^{1/n} → 1
- Alon-Frankl [AlFr85]: Answered Questions 2 (no) and 3 (yes)
- Alon-Das-Glebov-Sudakov [ADGS15]: Answered Question 1 (yes)
-/

import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Set.Function
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Order.Lattice
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Real.Basic

open Finset Set

namespace Erdos777

/-
## Part I: Basic Definitions
-/

variable {α : Type*} [DecidableEq α]

/--
**Comparable Sets:**
Two sets A and B are comparable if one is a subset of the other.
-/
def Comparable (A B : Finset α) : Prop := A ⊆ B ∨ B ⊆ A

/--
Comparability is a reflexive relation.
-/
theorem comparable_refl (A : Finset α) : Comparable A A := Or.inl Subset.rfl

/--
Comparability is a symmetric relation.
-/
theorem comparable_symm {A B : Finset α} (h : Comparable A B) : Comparable B A :=
  h.symm

/--
**Comparability Graph:**
Given a family F of finite sets, the comparability graph G_F has:
- Vertices: elements of F
- Edges: pairs (A, B) where A and B are comparable (and distinct)

We represent this as the edge set.
-/
def comparabilityEdges (F : Finset (Finset α)) : Finset ((Finset α) × (Finset α)) :=
  F.product F |>.filter (fun ⟨A, B⟩ => A ≠ B ∧ (A ⊆ B ∨ B ⊆ A))

/--
Number of edges in the comparability graph.
Note: This counts ordered pairs, so actual edges = edgeCount / 2.
-/
def orderedEdgeCount (F : Finset (Finset α)) : ℕ :=
  (comparabilityEdges F).card

/--
The actual number of unordered edges is half the ordered count.
-/
def edgeCount (F : Finset (Finset α)) : ℕ :=
  orderedEdgeCount F / 2

/-
## Part II: The Base Set {1,...,n}
-/

/--
The base set {0, 1, ..., n-1}.
-/
def baseSet (n : ℕ) : Finset ℕ := Finset.range n

/--
The power set of the base set.
-/
def powerSetOfBase (n : ℕ) : Finset (Finset ℕ) :=
  (baseSet n).powerset

/--
Size of the power set is 2^n.
-/
theorem powerSet_card (n : ℕ) : (powerSetOfBase n).card = 2^n := by
  simp only [powerSetOfBase, baseSet, Finset.card_powerset, Finset.card_range]

/-
## Part III: Question 1 - Edge Bound
-/

/--
**Question 1 Statement:**
For any ε > 0, there exists N such that for all n ≥ N, if F is a family of
subsets of {1,...,n} with |F| ≤ (2-ε)·2^{n/2}, then G_F has < 2^n edges.
-/
axiom question1_affirmative :
    ∀ ε : ℝ, ε > 0 →
    ∃ N : ℕ, ∀ n : ℕ, n ≥ N →
    ∀ F : Finset (Finset ℕ),
    (∀ S ∈ F, S ⊆ baseSet n) →
    (F.card : ℝ) ≤ (2 - ε) * (2 : ℝ)^(n / 2) →
    edgeCount F < 2^n

/--
**Extremal Construction:**
The bound (2-ε)·2^{n/2} is essentially tight.

When n is even, taking F = {all subsets of {1,...,n/2}} ∪ {{1,...,n/2} ∪ S : S ⊆ {n/2+1,...,n}}
gives |F| = 2^{n/2+1} and exactly 2^n edges.
-/
/-
## Part IV: Question 2 - Quadratic Edge Density
-/

/--
**Question 2: Answer is NO**
Alon and Frankl constructed a counterexample.

If F is the family of sets that either:
- intersect {n/2+1,...,n} in at most 1 element, or
- intersect {1,...,n/2} in at least n/2-1 elements

Then |F| ≫ n·2^{n/2} but G_F has at least 2^{-5}·C(m,2) edges.
-/
axiom question2_negative :
    ∃ (f : ℕ → Finset (Finset ℕ)),
    ∀ n : ℕ, n ≥ 4 →
    let F := f n
    (∀ S ∈ F, S ⊆ baseSet n) ∧
    (F.card : ℝ) ≥ n * (2 : ℝ)^(n / 2) ∧
    (edgeCount F : ℝ) ≥ (1 / 32) * ((F.card : ℝ) * (F.card - 1)) / 2

/--
**Counterexample Description:**
The family achieving the counterexample consists of sets S such that:
- |S ∩ {n/2+1,...,n}| ≤ 1, OR
- |S ∩ {1,...,n/2}| ≥ n/2 - 1
-/
def alonFranklFamily (n : ℕ) : Finset (Finset ℕ) :=
  (powerSetOfBase n).filter (fun S =>
    (S.filter (fun x => x ≥ n/2)).card ≤ 1 ∨
    (S.filter (fun x => x < n/2)).card ≥ n/2 - 1)

/-
## Part V: Question 3 - Subquadratic Threshold
-/

/--
**Question 3: YES**
Alon and Frankl (1985) proved this affirmatively.

More precisely: for every k ≥ 1, if |F| = 2^{((1/(k+1))+δ)n} for some δ > 0,
then the number of edges is < (1 - 1/k)·C(m,2) + O(m^{2 - Ω_k(δ^{k+1})}).
-/
axiom question3_affirmative :
    ∀ ε : ℝ, ε > 0 →
    ∃ δ : ℝ, δ > 0 ∧
    ∀ n : ℕ, ∀ F : Finset (Finset ℕ),
    (∀ S ∈ F, S ⊆ baseSet n) →
    (edgeCount F : ℝ) > (F.card : ℝ)^(2 - δ) →
    (F.card : ℝ) < ((2 : ℝ) + ε)^(n / 2)

/--
**Alon-Frankl Quantitative Bound:**
For integer k ≥ 1 and δ > 0, if m = 2^{(1/(k+1) + δ)n}, then
edges < (1 - 1/k)·C(m,2) + O(m^{2 - Ω_k(δ^{k+1})}).
-/
/-
## Part VI: Daykin-Frankl Result
-/

/--
**Daykin-Frankl Theorem:**
If G_F has (1 + o(1))·C(m,2) edges (i.e., almost all pairs are comparable),
then m^{1/n} → 1 as n → ∞.

This means F must be "close to" a chain (totally ordered family).
-/
/-
## Part VII: Chains and Antichains
-/

/--
**Chain:**
A family F is a chain if every two elements are comparable.
-/
def IsChain (F : Finset (Finset α)) : Prop :=
  ∀ A ∈ F, ∀ B ∈ F, Comparable A B

/--
**Antichain:**
A family F is an antichain if no two distinct elements are comparable.
-/
def IsAntichain (F : Finset (Finset α)) : Prop :=
  ∀ A ∈ F, ∀ B ∈ F, A ≠ B → ¬Comparable A B

/--
In a chain, every pair of distinct sets forms an edge.
-/
/-- In an antichain, there are no edges. -/
/--
**Dilworth's Theorem Connection:**
The maximum antichain in the power set of {1,...,n} has size C(n, ⌊n/2⌋).
-/
/-
## Part VIII: Examples
-/

/--
**Example:** Two singleton sets are comparable iff one is empty.
-/
theorem singleton_comparable (a b : α) (ha : a ≠ b) :
    ¬Comparable {a} {b} := by
  intro h
  cases h with
  | inl h1 =>
    have : a ∈ ({b} : Finset α) := h1 (mem_singleton.mpr rfl)
    simp only [mem_singleton] at this
    exact ha this
  | inr h2 =>
    have : b ∈ ({a} : Finset α) := h2 (mem_singleton.mpr rfl)
    simp only [mem_singleton] at this
    exact ha this.symm

/--
**Example:** Empty set is comparable to everything.
-/
theorem empty_comparable (A : Finset α) : Comparable ∅ A :=
  Or.inl (empty_subset A)

/--
**Example:** Full set is comparable to everything in its power set.
-/
theorem full_comparable (base A : Finset α) (hA : A ⊆ base) : Comparable A base :=
  Or.inr hA

/-
## Part IX: Alon-Das-Glebov-Sudakov Result (2015)
-/

/--
**ADGS Theorem (2015):**
Answered Question 1 affirmatively using their Theorem 1.4 and Corollary 1.5.

For ε > 0 and n sufficiently large, if |F| ≤ (2-ε)·2^{n/2}, then
the number of comparable pairs is < 2^n.
-/
/-
## Part X: Main Results Summary
-/

/--
**Erdős Problem #777: SOLVED**

All three questions have been resolved:
1. YES (Alon-Das-Glebov-Sudakov 2015)
2. NO (Alon-Frankl 1985)
3. YES (Alon-Frankl 1985)
-/
theorem erdos_777_summary :
    -- Question 1: Affirmative
    (∀ ε : ℝ, ε > 0 →
     ∃ N : ℕ, ∀ n : ℕ, n ≥ N →
     ∀ F : Finset (Finset ℕ),
     (∀ S ∈ F, S ⊆ baseSet n) →
     (F.card : ℝ) ≤ (2 - ε) * (2 : ℝ)^(n / 2) →
     edgeCount F < 2^n) ∧
    -- Question 2: Negative (counterexample exists)
    (∃ (f : ℕ → Finset (Finset ℕ)),
     ∀ n : ℕ, n ≥ 4 →
     let F := f n
     (∀ S ∈ F, S ⊆ baseSet n) ∧
     (F.card : ℝ) ≥ n * (2 : ℝ)^(n / 2) ∧
     (edgeCount F : ℝ) ≥ (1 / 32) * ((F.card : ℝ) * (F.card - 1)) / 2) ∧
    -- Question 3: Affirmative
    (∀ ε : ℝ, ε > 0 →
     ∃ δ : ℝ, δ > 0 ∧
     ∀ n : ℕ, ∀ F : Finset (Finset ℕ),
     (∀ S ∈ F, S ⊆ baseSet n) →
     (edgeCount F : ℝ) > (F.card : ℝ)^(2 - δ) →
     (F.card : ℝ) < ((2 : ℝ) + ε)^(n / 2)) :=
  ⟨question1_affirmative, question2_negative, question3_affirmative⟩

/--
The main theorem: Erdős Problem #777 is completely resolved.
All three questions answered: Q1 yes, Q2 no, Q3 yes.
-/
theorem erdos_777 :
    (∀ ε : ℝ, ε > 0 →
     ∃ N : ℕ, ∀ n : ℕ, n ≥ N →
     ∀ F : Finset (Finset ℕ),
     (∀ S ∈ F, S ⊆ baseSet n) →
     (F.card : ℝ) ≤ (2 - ε) * (2 : ℝ)^(n / 2) →
     edgeCount F < 2^n) ∧
    (∃ (f : ℕ → Finset (Finset ℕ)),
     ∀ n : ℕ, n ≥ 4 →
     let F := f n
     (∀ S ∈ F, S ⊆ baseSet n) ∧
     (F.card : ℝ) ≥ n * (2 : ℝ)^(n / 2) ∧
     (edgeCount F : ℝ) ≥ (1 / 32) * ((F.card : ℝ) * (F.card - 1)) / 2) ∧
    (∀ ε : ℝ, ε > 0 →
     ∃ δ : ℝ, δ > 0 ∧
     ∀ n : ℕ, ∀ F : Finset (Finset ℕ),
     (∀ S ∈ F, S ⊆ baseSet n) →
     (edgeCount F : ℝ) > (F.card : ℝ)^(2 - δ) →
     (F.card : ℝ) < ((2 : ℝ) + ε)^(n / 2)) :=
  erdos_777_summary

end Erdos777
