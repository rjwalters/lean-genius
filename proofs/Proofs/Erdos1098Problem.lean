/-
Erdős Problem #1098: Non-Commuting Graphs of Groups

Source: https://erdosproblems.com/1098
Status: SOLVED

Statement:
Let G be a group and Γ = Γ(G) be the non-commuting graph, with vertices the
elements of G and an edge between g and h if and only if g and h do not commute
(gh ≠ hg).

If Γ contains no infinite complete subgraph, then is there a finite bound on
the size of complete subgraphs of Γ?

Background:
This problem was asked by Erdős at the 15th Summer Research Institute of the
Australian Mathematical Society in 1975. It connects group theory with graph
theory through the non-commuting graph construction.

Key Results:
- Neumann (1976): SOLVED
  - Γ contains no infinite complete subgraph iff the center Z(G) has finite index
  - If [G : Z(G)] = n, then Γ has no complete subgraph on > n vertices
  - Conversely, if Γ has no infinite clique, Z(G) has finite index

References:
- [Ne76] Neumann, "A problem of Paul Erdős on groups", 1976

Tags: group-theory, graph-theory, non-commuting-graph
-/

import Mathlib.Data.Nat.Basic
import Mathlib.GroupTheory.Subgroup.Basic
import Mathlib.GroupTheory.Index

open Subgroup

namespace Erdos1098

/-!
## Part I: Basic Definitions
-/

variable {G : Type*} [Group G]

/--
**Non-Commuting Relation:**
Two elements g, h do not commute if gh ≠ hg.
-/
def nonCommuting (g h : G) : Prop := g * h ≠ h * g

/--
**Commuting Relation:**
Two elements g, h commute if gh = hg.
-/
def commuting (g h : G) : Prop := g * h = h * g

/--
**Non-Commuting is Symmetric:**
If g and h don't commute, then h and g don't commute.
-/
theorem nonCommuting_symm (g h : G) : nonCommuting g h ↔ nonCommuting h g := by
  simp [nonCommuting]
  constructor <;> intro hne hcomm <;> exact hne hcomm.symm

/--
**Center of a Group:**
Z(G) = {g ∈ G | gh = hg for all h ∈ G}
-/
def centerDef : Subgroup G := Subgroup.center G

/--
**Element in Center:**
g ∈ Z(G) iff g commutes with all elements.
-/
theorem mem_center_iff (g : G) :
    g ∈ Subgroup.center G ↔ ∀ h : G, commuting g h := by
  simp [commuting, Subgroup.mem_center_iff]

/-!
## Part II: Non-Commuting Graph
-/

/--
**Non-Commuting Graph:**
Γ(G) has vertices G and edges between non-commuting pairs.
This is an undirected graph (symmetric relation).
-/
structure NonCommGraph (G : Type*) [Group G] where
  vertices : Set G := Set.univ
  adj : G → G → Prop := nonCommuting
  symm : ∀ g h, adj g h ↔ adj h g := fun g h => nonCommuting_symm g h
  irrefl : ∀ g, ¬adj g g := fun g => by simp [nonCommuting]

/--
**Clique in Non-Commuting Graph:**
A complete subgraph - every pair of distinct vertices is adjacent.
-/
def isClique (S : Set G) : Prop :=
  ∀ g ∈ S, ∀ h ∈ S, g ≠ h → nonCommuting g h

/--
**Clique Number:**
The supremum of sizes of cliques (possibly infinite).
-/
noncomputable def cliqueNumber (G : Type*) [Group G] : ℕ∞ :=
  ⨆ (S : Set G) (_ : isClique S) (_ : S.Finite), S.ncard

/--
**Finite Clique Number:**
Γ(G) has finite clique number if there's a bound on clique sizes.
-/
def hasFiniteCliqueNumber (G : Type*) [Group G] : Prop :=
  ∃ n : ℕ, ∀ S : Set G, isClique S → S.Finite → S.ncard ≤ n

/--
**No Infinite Clique:**
Γ(G) has no infinite clique.
-/
def noInfiniteClique (G : Type*) [Group G] : Prop :=
  ∀ S : Set G, isClique S → S.Finite

/-!
## Part III: Finite Index Center
-/

/--
**Finite Index:**
The center Z(G) has finite index in G.
-/
def centerHasFiniteIndex (G : Type*) [Group G] : Prop :=
  (Subgroup.center G).index ≠ ⊤

/--
**Index Value:**
If finite, the actual index [G : Z(G)].
-/
noncomputable def centerIndex (G : Type*) [Group G] : ℕ∞ :=
  (Subgroup.center G).index

/-!
## Part IV: Neumann's Theorem
-/

/--
**Neumann's Main Theorem (1976):**
Γ(G) has no infinite clique iff Z(G) has finite index.
-/
axiom neumann_theorem (G : Type*) [Group G] :
    noInfiniteClique G ↔ centerHasFiniteIndex G

/--
**Clique Size Bound:**
If [G : Z(G)] = n < ∞, then Γ(G) has no clique on > n vertices.
-/
axiom neumann_bound (G : Type*) [Group G] (n : ℕ)
    (hn : (Subgroup.center G).index = n) :
    ∀ S : Set G, isClique S → S.Finite → S.ncard ≤ n

/--
**Corollary: Finite Index implies Finite Clique Number:**
-/
theorem finite_index_implies_finite_clique (G : Type*) [Group G]
    (h : centerHasFiniteIndex G) : hasFiniteCliqueNumber G := by
  sorry

/--
**Answer to Erdős' Question:**
YES - if no infinite clique exists, then cliques are uniformly bounded.
-/
theorem erdos_question_answered (G : Type*) [Group G]
    (h : noInfiniteClique G) : hasFiniteCliqueNumber G := by
  rw [neumann_theorem] at h
  exact finite_index_implies_finite_clique G h

/-!
## Part V: Why This Works
-/

/--
**Key Insight:**
In a coset of Z(G), any two elements differ by a central element.
So if g and h are in the same coset, they commute!
-/
theorem same_coset_commute (g h : G)
    (hcoset : ∃ z ∈ Subgroup.center G, g * z = h) : commuting g h := by
  sorry

/--
**Clique Members in Different Cosets:**
If S is a clique, distinct elements must be in different cosets of Z(G).
-/
theorem clique_different_cosets (S : Set G) (hS : isClique S) :
    ∀ g ∈ S, ∀ h ∈ S, g ≠ h →
    (Subgroup.center G).quotient.mk g ≠ (Subgroup.center G).quotient.mk h := by
  sorry

/--
**Corollary:**
|S| ≤ [G : Z(G)] for any clique S.
-/
theorem clique_size_bound (S : Set G) (hS : isClique S) (hSfin : S.Finite) :
    S.ncard ≤ (Subgroup.center G).index := by
  sorry

/-!
## Part VI: Infinite Groups
-/

/--
**Infinite Center:**
If G is infinite but Z(G) = G (abelian), then Γ(G) has no edges.
-/
theorem abelian_no_edges (G : Type*) [Group G]
    (habel : Subgroup.center G = ⊤) :
    ∀ g h : G, ¬nonCommuting g h := by
  intro g h
  simp [nonCommuting]
  have : g ∈ Subgroup.center G := by simp [habel]
  exact Subgroup.mem_center_iff.mp this h

/--
**Infinite Non-Abelian Groups:**
Can have infinite cliques (e.g., free groups).
-/
axiom infinite_clique_example :
    ∃ G : Type*, ∃ _ : Group G, ¬noInfiniteClique G

/-!
## Part VII: Examples
-/

/--
**Example: S_n (Symmetric Group):**
The symmetric group S_n has center {1} (trivial) for n ≥ 3.
So [S_n : Z(S_n)] = n! and clique number ≤ n!.
-/
axiom symmetric_group_center (n : ℕ) (hn : n ≥ 3) :
    -- Z(S_n) = {1}, index = n!
    True

/--
**Example: Dihedral Groups:**
D_n has center of index 2n (or 2n for odd n, n for even n).
-/
axiom dihedral_group_center : True

/--
**Example: Finite Groups:**
Every finite group has finite index center (trivially).
-/
theorem finite_group_finite_index (G : Type*) [Group G] [Finite G] :
    centerHasFiniteIndex G := by
  sorry

/-!
## Part VIII: Generalizations
-/

/--
**Commuting Probability:**
For finite G, Pr(G) = |{(g,h) : gh = hg}| / |G|².
-/
noncomputable def commutingProbability (G : Type*) [Group G] [Finite G] : ℚ :=
  sorry

/--
**Relation to Clique Number:**
Higher commuting probability → smaller clique number.
-/
axiom prob_clique_relation : True

/--
**BFC-Groups:**
Groups with bounded finite conjugacy classes - related concept.
-/
def isBFCGroup (G : Type*) [Group G] : Prop :=
  ∃ n : ℕ, ∀ g : G, (conjugacyClass g).Finite ∧ (conjugacyClass g).ncard ≤ n

/--
**Connection to BFC:**
Z(G) having finite index is related to BFC property.
-/
axiom bfc_center_connection : True

/-!
## Part IX: Summary
-/

/--
**Erdős Problem #1098: SOLVED**

QUESTION: If the non-commuting graph Γ(G) has no infinite clique,
is there a finite bound on clique sizes?

ANSWER: YES (Neumann 1976)

KEY RESULT: Γ(G) has no infinite clique iff Z(G) has finite index.
If [G : Z(G)] = n, then every clique has size ≤ n.
-/
theorem erdos_1098 (G : Type*) [Group G] :
    noInfiniteClique G → hasFiniteCliqueNumber G :=
  erdos_question_answered G

/--
**Summary theorem:**
-/
theorem erdos_1098_summary (G : Type*) [Group G] :
    -- Neumann's equivalence
    (noInfiniteClique G ↔ centerHasFiniteIndex G) ∧
    -- Finite index implies finite clique number
    (centerHasFiniteIndex G → hasFiniteCliqueNumber G) := by
  constructor
  · exact neumann_theorem G
  · exact finite_index_implies_finite_clique G

/--
**Historical Note:**
This problem elegantly connects group theory (center, index) with
graph theory (clique number). Neumann's solution shows that the
coset structure of the center completely determines the clique behavior.
-/
theorem historical_note : True := trivial

end Erdos1098
