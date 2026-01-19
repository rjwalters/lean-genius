/-
Erdős Problem #207: High-Girth Steiner Triple Systems

Source: https://erdosproblems.com/207
Status: SOLVED (Kwan-Sah-Sawhney-Simkin 2022)

Statement:
For any g ≥ 2, if n is sufficiently large and n ≡ 1, 3 (mod 6), then there
exists a 3-uniform hypergraph on n vertices such that:
1. Every pair of vertices is contained in exactly one edge (Steiner triple system)
2. For any 2 ≤ j ≤ g, any collection of j edges contains at least j+3 vertices

This establishes the existence of high-girth Steiner triple systems.

Background:
- A Steiner triple system (STS) of order n is a collection of 3-element subsets
  (triples) of an n-element set such that every pair appears in exactly one triple.
- The girth condition ensures no "small configurations" - j edges must span at
  least j+3 vertices, preventing tight overlaps.
- n ≡ 1, 3 (mod 6) is the necessary and sufficient condition for STS existence.

References:
- Kwan, M., Sah, A., Sawhney, M., Simkin, M. (2022): High-girth Steiner triple
  systems. arXiv:2201.04554
- Erdős, P. (1976): Problems and results in combinatorial analysis [Er76]
-/

import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Nat.Basic

open Finset

namespace Erdos207

/-
## Part I: Hypergraphs and Steiner Triple Systems
-/

/--
**3-uniform hypergraph:**
A collection of 3-element subsets (edges) of a vertex set V.
-/
structure Hypergraph3 (V : Type*) [Fintype V] where
  edges : Finset (Finset V)
  uniform : ∀ e ∈ edges, e.card = 3

/--
**Edge contains pair:**
A pair {a, b} is contained in edge e if both a, b ∈ e.
-/
def edgeContainsPair {V : Type*} [DecidableEq V] (e : Finset V) (a b : V) : Prop :=
  a ∈ e ∧ b ∈ e ∧ a ≠ b

/--
**Steiner triple system property:**
A 3-uniform hypergraph is a Steiner triple system if every pair of
distinct vertices is contained in exactly one edge.
-/
def IsSteinerTripleSystem {V : Type*} [Fintype V] [DecidableEq V]
    (H : Hypergraph3 V) : Prop :=
  ∀ a b : V, a ≠ b → ∃! e ∈ H.edges, edgeContainsPair e a b

/-
## Part II: Girth Conditions
-/

/--
**Vertex span of edge collection:**
The number of distinct vertices appearing in a collection of edges.
-/
def vertexSpan {V : Type*} [DecidableEq V] (edges : Finset (Finset V)) : ℕ :=
  (edges.biUnion id).card

/--
**High-girth property:**
A hypergraph has girth at least g if any j edges (2 ≤ j ≤ g) contain at least j+3 vertices.
-/
def HasGirthAtLeast {V : Type*} [Fintype V] [DecidableEq V]
    (H : Hypergraph3 V) (g : ℕ) : Prop :=
  ∀ S : Finset (Finset V), S ⊆ H.edges → 2 ≤ S.card → S.card ≤ g →
    vertexSpan S ≥ S.card + 3

/--
**Why j+3?:**
- A single edge has 3 vertices.
- Two disjoint edges have 6 vertices = 2 + 4.
- The condition j+3 ensures edges don't share too many vertices.
- For j=2: two edges must have ≥ 5 vertices, so they share ≤ 1 vertex.
- This prevents "short cycles" in the hypergraph structure.
-/
def girthExplanation : String :=
  "j+3 vertices for j edges prevents tight configurations"

/-
## Part III: The Admissibility Condition
-/

/--
**Admissible order:**
A positive integer n is admissible for STS if n ≡ 1 or 3 (mod 6).
-/
def IsAdmissible (n : ℕ) : Prop :=
  n % 6 = 1 ∨ n % 6 = 3

/--
**Kirkman's Theorem (1847):**
A Steiner triple system of order n exists if and only if n ≡ 1, 3 (mod 6).
-/
axiom kirkman_theorem (n : ℕ) :
    (∃ (V : Type) [Fintype V] [DecidableEq V] (H : Hypergraph3 V),
      Fintype.card V = n ∧ IsSteinerTripleSystem H) ↔
    (n ≥ 1 ∧ IsAdmissible n)

/--
**Number of triples in an STS:**
An STS(n) has exactly n(n-1)/6 triples.
-/
def stsTripleCount (n : ℕ) : ℕ := n * (n - 1) / 6

theorem sts_triple_count_formula (n : ℕ) (hn : IsAdmissible n) :
    6 ∣ n * (n - 1) := by
  sorry

/-
## Part IV: The Erdős Conjecture
-/

/--
**Erdős Problem #207 (Conjecture):**
For any g ≥ 2, there exists N(g) such that for all n ≥ N(g) with n ≡ 1, 3 (mod 6),
there exists an STS(n) with girth at least g.
-/
def erdos207Conjecture : Prop :=
  ∀ g : ℕ, g ≥ 2 → ∃ N : ℕ, ∀ n : ℕ, n ≥ N → IsAdmissible n →
    ∃ (V : Type) [Fintype V] [DecidableEq V] (H : Hypergraph3 V),
      Fintype.card V = n ∧ IsSteinerTripleSystem H ∧ HasGirthAtLeast H g

/-
## Part V: The Solution
-/

/--
**Kwan-Sah-Sawhney-Simkin Theorem (2022):**
The Erdős conjecture on high-girth STS is true.

For any g ≥ 2, if n is sufficiently large and admissible, there exists
a Steiner triple system of order n with girth at least g.
-/
axiom kwan_sah_sawhney_simkin_2022 : erdos207Conjecture

/--
**Erdős Problem #207: Main Theorem**
-/
theorem erdos_207 : erdos207Conjecture :=
  kwan_sah_sawhney_simkin_2022

/-
## Part VI: Special Cases and Bounds
-/

/--
**Girth 2 (trivial case):**
Any STS has girth at least 2 (2 edges span at least 5 vertices if they
share at most 1 vertex, which is always achievable).
-/
theorem sts_has_girth_at_least_2 {V : Type*} [Fintype V] [DecidableEq V]
    (H : Hypergraph3 V) (hSTS : IsSteinerTripleSystem H) :
    HasGirthAtLeast H 2 := by
  sorry

/--
**Girth 3 case:**
An STS has girth ≥ 3 iff it contains no Pasch configuration (4 triples
on 6 vertices forming a specific pattern).
-/
def IsPaschConfiguration {V : Type*} [DecidableEq V] (triples : Finset (Finset V)) : Prop :=
  triples.card = 4 ∧ vertexSpan triples = 6

def IsPaschFree {V : Type*} [Fintype V] [DecidableEq V] (H : Hypergraph3 V) : Prop :=
  ∀ S : Finset (Finset V), S ⊆ H.edges → ¬IsPaschConfiguration S

theorem girth_3_iff_pasch_free {V : Type*} [Fintype V] [DecidableEq V]
    (H : Hypergraph3 V) (hSTS : IsSteinerTripleSystem H) :
    HasGirthAtLeast H 3 ↔ IsPaschFree H := by
  sorry

/--
**Anti-Pasch STS:**
Steiner triple systems avoiding the Pasch configuration have been studied
extensively. The KSSS result generalizes this to arbitrary girth.
-/
axiom anti_pasch_sts_exist (n : ℕ) (hn : IsAdmissible n) (hn' : n ≥ 7) :
    ∃ (V : Type) [Fintype V] [DecidableEq V] (H : Hypergraph3 V),
      Fintype.card V = n ∧ IsSteinerTripleSystem H ∧ IsPaschFree H

/-
## Part VII: Proof Techniques
-/

/--
**Random Construction:**
The KSSS proof uses a random greedy algorithm:
1. Order pairs randomly
2. Greedily add triples avoiding forbidden configurations
3. Show with positive probability this succeeds

Key tools: Rödl nibble method, spread measure, concentration inequalities.
-/
axiom ksss_random_construction : True

/--
**The Spread Measure:**
A key technical tool measuring how "spread out" a partial STS is,
ensuring the greedy process maintains the high-girth property.
-/
axiom spread_measure_technique : True

/-
## Part VIII: Related Problems
-/

/--
**Resolvable STS:**
An STS is resolvable if its triples can be partitioned into parallel classes
(partitions of the vertex set).
-/
def IsResolvable {V : Type*} [Fintype V] [DecidableEq V] (H : Hypergraph3 V) : Prop :=
  ∃ classes : Finset (Finset (Finset V)),
    (∀ c ∈ classes, ∀ t ∈ c, t ∈ H.edges) ∧
    (∀ c ∈ classes, (c.biUnion id).card = Fintype.card V)

/--
**Kirkman Schoolgirl Problem:**
Related to resolvable STS - can 15 schoolgirls walk in groups of 3 for 7 days
without any pair walking together twice?
-/
def kirkmanSchoolgirlProblem : Prop :=
  ∃ (V : Type) [Fintype V] [DecidableEq V] (H : Hypergraph3 V),
    Fintype.card V = 15 ∧ IsSteinerTripleSystem H ∧ IsResolvable H

axiom kirkman_schoolgirl_solution : kirkmanSchoolgirlProblem

/-
## Part IX: Main Results Summary
-/

/--
**Erdős Problem #207: Summary**

1. **Conjecture:** High-girth STS exist for all admissible n ≥ N(g)
2. **Proved:** Kwan-Sah-Sawhney-Simkin (2022)
3. **Method:** Random greedy algorithm with spread measure analysis
4. **Special case:** Anti-Pasch STS (girth ≥ 3) were known earlier
5. **Condition:** n ≡ 1, 3 (mod 6) is necessary (Kirkman's condition)

Status: SOLVED
-/
theorem erdos_207_summary :
    -- The conjecture is true
    erdos207Conjecture ∧
    -- Kirkman's condition is necessary and sufficient for STS existence
    (∀ n : ℕ, n ≥ 1 → (∃ (V : Type) [Fintype V] [DecidableEq V] (H : Hypergraph3 V),
      Fintype.card V = n ∧ IsSteinerTripleSystem H) ↔ IsAdmissible n) := by
  constructor
  · exact kwan_sah_sawhney_simkin_2022
  · intro n hn
    have h := kirkman_theorem n
    constructor
    · intro ⟨V, _, _, H, hcard, hSTS⟩
      exact (h.mp ⟨V, _, _, H, hcard, hSTS⟩).2
    · intro hadm
      exact h.mpr ⟨hn, hadm⟩

/--
**Problem Status:**
Solved by Kwan, Sah, Sawhney, and Simkin in 2022.
-/
axiom erdos_207_status : True

end Erdos207
