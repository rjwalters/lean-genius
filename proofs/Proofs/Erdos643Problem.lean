/-
Erdős Problem #643: Crossed Pairs in Hypergraphs

Let f(n;t) be the minimal number of edges such that any t-uniform hypergraph
on n vertices with at least f(n;t) edges must contain four edges A,B,C,D with:
  A ∪ B = C ∪ D  and  A ∩ B = C ∩ D = ∅

**Status**: OPEN

**Known Results**:
- For t=2: f(n;2) = (1/2 + o(1))n^{3/2} (related to C₄-free graphs)
- For t=3: f(n;3) ≤ (13/9)·C(n,2) [Pikhurko-Verstraëte]
- General: C(n-1,t-1) + ⌊(n-1)/t⌋ ≤ f(n;t) < (7/2)·C(n,t-1)

**Conjecture**: f(n;t) = (1 + o(1))·C(n,t-1) for t ≥ 3

Reference: https://erdosproblems.com/643
-/

import Mathlib

namespace Erdos643

open scoped Classical
open Finset

/-!
## Hypergraph Definitions

A t-uniform hypergraph on vertex set V is a collection of t-element subsets of V.
-/

/-- A hypergraph is a collection of edges (subsets of vertices) -/
abbrev Hypergraph (V : Type*) := Set (Finset V)

/-- A hypergraph is t-uniform if all edges have exactly t vertices -/
def IsUniform (H : Hypergraph V) (t : ℕ) : Prop :=
  ∀ e : Finset V, e ∈ H → e.card = t

/-- The number of edges in a hypergraph -/
noncomputable def edgeCount (H : Hypergraph V) : ℕ := H.ncard

/-!
## The Crossed Pair Configuration

Four edges A,B,C,D form a "crossed pair" if:
- A ∪ B = C ∪ D (same union)
- A ∩ B = C ∩ D = ∅ (both pairs are disjoint)
- {A,B} ≠ {C,D} (not the same pair)

This configuration is also called a "Berge 2-cover" or "symmetric difference system".
-/

/-- Four edges form a crossed pair configuration -/
def IsCrossedPair (A B C D : Finset V) : Prop :=
  A ∪ B = C ∪ D ∧
  A ∩ B = ∅ ∧
  C ∩ D = ∅ ∧
  ({A, B} : Set (Finset V)) ≠ {C, D}

/-- A hypergraph contains a crossed pair -/
def HasCrossedPair (H : Hypergraph V) : Prop :=
  ∃ A B C D : Finset V, A ∈ H ∧ B ∈ H ∧ C ∈ H ∧ D ∈ H ∧ IsCrossedPair A B C D

/-!
## The Extremal Function f(n,t)

f(n,t) is the minimal number of edges that forces a crossed pair.
-/

/-- A hypergraph on n vertices with no crossed pair and exactly k edges -/
def CrossedPairFreeWithEdges (n t k : ℕ) : Prop :=
  ∃ H : Hypergraph (Fin n),
    IsUniform H t ∧
    edgeCount H = k ∧
    ¬HasCrossedPair H

/-- f(n,t) is the minimal m such that any t-uniform hypergraph on n vertices
    with m edges must contain a crossed pair -/
noncomputable def f (n t : ℕ) : ℕ :=
  Nat.find (⟨Nat.choose n t + 1, by
    intro H_exists
    -- The number of t-subsets is finite
    sorry⟩ : ∃ m, ∀ k ≥ m, ¬CrossedPairFreeWithEdges n t k)

/-!
## Case t = 2: Connection to C₄-free Graphs

For ordinary graphs (t=2), a crossed pair is essentially a 4-cycle C₄.
The edges A,B,C,D with A ∪ B = C ∪ D and all pairwise disjoint
form an alternating path structure.
-/

/-- In a graph, a crossed pair corresponds to a 4-cycle -/
theorem graph_crossed_pair_iff_four_cycle (A B C D : Finset (Fin n))
    (hA : A.card = 2) (hB : B.card = 2) (hC : C.card = 2) (hD : D.card = 2) :
    IsCrossedPair A B C D ↔
    ∃ v₁ v₂ v₃ v₄ : Fin n,
      ({v₁, v₂} = A ∨ {v₁, v₂} = C) ∧
      ({v₂, v₃} = B ∨ {v₂, v₃} = D) ∧
      ({v₃, v₄} = A ∨ {v₃, v₄} = C) ∧
      ({v₄, v₁} = B ∨ {v₄, v₁} = D) := by
  sorry

/-- The Kővári–Sós–Turán theorem gives f(n,2) = Θ(n^{3/2}) -/
theorem f_two_asymptotic :
    ∃ C₁ C₂ : ℝ, C₁ > 0 ∧ C₂ > 0 ∧
    ∀ n ≥ 1, C₁ * n^(3/2 : ℝ) ≤ f n 2 ∧ (f n 2 : ℝ) ≤ C₂ * n^(3/2 : ℝ) := by
  sorry

/-!
## Case t = 3: Pikhurko-Verstraëte Bound

For 3-uniform hypergraphs, significant progress has been made.
-/

/-- Pikhurko-Verstraëte (2009): f(n,3) ≤ (13/9)·C(n,2) -/
axiom pikhurko_verstrate_bound (n : ℕ) (hn : n ≥ 3) :
    (f n 3 : ℚ) ≤ (13 : ℚ) / 9 * Nat.choose n 2

/-- Lower bound: f(n,3) ≥ C(n-1,2) + ⌊(n-1)/3⌋ -/
theorem f_three_lower_bound (n : ℕ) (hn : n ≥ 3) :
    f n 3 ≥ Nat.choose (n - 1) 2 + (n - 1) / 3 := by
  sorry

/-!
## General Bounds

The general theory gives bounds in terms of binomial coefficients.
-/

/-- Lower bound: f(n,t) ≥ C(n-1,t-1) + ⌊(n-1)/t⌋ -/
theorem f_lower_bound (n t : ℕ) (ht : t ≥ 2) (hn : n ≥ t) :
    f n t ≥ Nat.choose (n - 1) (t - 1) + (n - 1) / t := by
  sorry

/-- Upper bound: f(n,t) < (7/2)·C(n,t-1) -/
axiom f_upper_bound (n t : ℕ) (ht : t ≥ 2) (hn : n ≥ t) :
    (f n t : ℚ) < (7 : ℚ) / 2 * Nat.choose n (t - 1)

/-!
## The Main Conjecture

Erdős conjectured that f(n,t) = (1 + o(1))·C(n,t-1) for t ≥ 3.
-/

/-- **Erdős Problem #643** (OPEN)

For t ≥ 3, is f(n,t) = (1 + o(1))·C(n,t-1)?

Equivalently: lim_{n→∞} f(n,t) / C(n,t-1) = 1 for all fixed t ≥ 3. -/
def Erdos643Conjecture : Prop :=
  ∀ t ≥ 3, Filter.Tendsto
    (fun n => (f n t : ℝ) / Nat.choose n (t - 1))
    Filter.atTop
    (nhds 1)

/-!
## Constructions Avoiding Crossed Pairs

To achieve lower bounds, we need constructions of hypergraphs
without crossed pairs.
-/

/-- A "sunflower" construction avoids crossed pairs.
    All edges share a common (t-1)-element core, with one unique petal each. -/
def SunflowerHypergraph (n t : ℕ) (core : Finset (Fin n)) (hcore : core.card = t - 1)
    (petals : Finset (Fin n)) (hdisjoint : Disjoint core petals) : Hypergraph (Fin n) :=
  {e | ∃ p ∈ petals, e = core ∪ {p}}

/-- The sunflower has no crossed pairs because all edges share the core.

All edges in a sunflower share the (t-1)-element core. For a crossed pair,
we need A ∩ B = ∅, but any two sunflower edges intersect in the core.
Since t ≥ 2, the core is nonempty, giving a contradiction. -/
theorem sunflower_no_crossed_pair (n t : ℕ) (core : Finset (Fin n))
    (hcore : core.card = t - 1) (ht : t ≥ 2) (petals : Finset (Fin n))
    (hdisjoint : Disjoint core petals) :
    ¬HasCrossedPair (SunflowerHypergraph n t core hcore petals hdisjoint) := by
  -- All edges share the nonempty core, so no two can be disjoint
  sorry

/-!
## Small Cases

We can verify the extremal function for small parameters.
-/

/-- f(4,2) = 3: The complete bipartite graph K_{2,2} has 4 edges and contains C₄ -/
theorem f_four_two : f 4 2 = 3 := by
  sorry

/-- f(5,2) = 5: Related to the Petersen graph -/
theorem f_five_two : f 5 2 = 5 := by
  sorry

/-!
## Connection to Other Extremal Problems

This problem is related to:
- The Zarankiewicz problem (C₄-free graphs)
- The Turán problem for hypergraphs
- Sunflower lemma (Erdős-Rado)
-/

/-- The Erdős-Rado Sunflower Lemma: large uniform families contain sunflowers -/
axiom sunflower_lemma (k r : ℕ) :
    ∃ F : ℕ, ∀ n : ℕ, ∀ H : Hypergraph (Fin n),
      IsUniform H k → edgeCount H ≥ F →
      ∃ (edges : Finset (Finset (Fin n))) (core : Finset (Fin n)),
        edges.card ≥ r ∧
        (∀ e ∈ edges, e ∈ H) ∧
        ∀ e₁ ∈ edges, ∀ e₂ ∈ edges, e₁ ≠ e₂ → e₁ ∩ e₂ = core

/-!
## Historical Context

This problem connects to Füredi's work on hypergraph Turán problems
and the broader study of forbidden configurations in extremal combinatorics.

The conjecture that f(n,t) ~ C(n,t-1) would show that the "sunflower-type"
construction is essentially optimal.
-/

end Erdos643
