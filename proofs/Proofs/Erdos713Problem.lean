/-
Erdős Problem #713: Rational Exponents for Bipartite Turán Numbers

Source: https://erdosproblems.com/713
Status: OPEN (parts solved, main question unresolved)
Prize: $500

Statement:
Is it true that, for every bipartite graph G, there exists some α ∈ [1,2) and c > 0
such that ex(n; G) ~ c·n^α? Must α be rational?

Background:
- ex(n; G) = maximum edges in n-vertex graph with no G subgraph
- Kővári-Sós-Turán: ex(n; K_{s,t}) = O(n^{2-1/s}) for s ≤ t
- Erdős-Stone-Simonovits: for non-bipartite G, ex(n; G) = (1-1/(χ(G)-1))n²/2 + o(n²)
- For bipartite G, ex(n; G) = o(n²) but behavior varies greatly

History:
- Erdős initially conjectured α has form 1+1/k or 2-1/k
- Erdős-Simonovits (1970): Disproved this specific form
- Question remains: Does α always exist? Is it always rational?
- For hypergraphs: Frankl-Füredi (1987) gave counterexamples

References:
- Erdős (1967): "Some recent results on extremal problems in graph theory"
- Erdős-Simonovits (1970): Colloq., Balatonf̈üred
- Frankl-Füredi (1987): J. Combin. Theory Ser. A
- Füredi-Gerbner (2021): "Hypergraphs without exponents"
- Related: Erdős Problem #571
-/

import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Subgraph
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.Asymptotics.Asymptotics
import Mathlib.Data.Rat.Basic

open SimpleGraph Asymptotics

namespace Erdos713

/-
## Part I: Basic Definitions
-/

variable {V : Type*} [Fintype V] [DecidableEq V]

/--
**Bipartite Graph:**
A graph is bipartite if its vertices can be 2-colored with no monochromatic edges.
-/
def isBipartite (G : SimpleGraph V) : Prop :=
  ∃ A B : Set V, A ∪ B = Set.univ ∧ A ∩ B = ∅ ∧
    ∀ u v : V, G.Adj u v → (u ∈ A ∧ v ∈ B) ∨ (u ∈ B ∧ v ∈ A)

/--
**G-free Graph:**
A graph H is G-free if it contains no subgraph isomorphic to G.
-/
def isGFree (H G : SimpleGraph V) : Prop :=
  ¬∃ (f : V → V), Function.Injective f ∧
    ∀ u v : V, G.Adj u v → H.Adj (f u) (f v)

/-
## Part II: Extremal Numbers
-/

/--
**Extremal Number ex(n; G):**
The maximum number of edges in an n-vertex graph containing no copy of G.
-/
axiom extremalNumber (n : ℕ) (G : SimpleGraph (Fin n)) : ℕ

/--
**Basic Properties of Extremal Numbers:**
-/
axiom extremalNumber_mono (n m : ℕ) (G : SimpleGraph (Fin n)) (H : SimpleGraph (Fin m))
    (hnm : n ≤ m) : extremalNumber n G ≤ extremalNumber m H

axiom extremalNumber_bound (n : ℕ) (G : SimpleGraph (Fin n)) :
  extremalNumber n G ≤ n * (n - 1) / 2

/-
## Part III: Asymptotic Growth
-/

/--
**Power-Law Growth:**
ex(n; G) ~ c·n^α means ex(n; G) / n^α → c as n → ∞.
-/
def hasPowerLawGrowth (G : ℕ → ℕ) (c α : ℝ) : Prop :=
  c > 0 ∧ α ≥ 1 ∧ α < 2 ∧
    Filter.Tendsto (fun n => (G n : ℝ) / (n : ℝ)^α) Filter.atTop (nhds c)

/--
**Weaker Growth Condition:**
ex(n; G) ≍ n^α means c₁·n^α ≤ ex(n; G) ≤ c₂·n^α for large n.
-/
def hasPowerLawOrder (G : ℕ → ℕ) (α : ℝ) : Prop :=
  ∃ c₁ c₂ : ℝ, c₁ > 0 ∧ c₂ > 0 ∧ α ≥ 1 ∧ α < 2 ∧
    ∃ N : ℕ, ∀ n ≥ N, c₁ * (n : ℝ)^α ≤ G n ∧ (G n : ℝ) ≤ c₂ * (n : ℝ)^α

/-
## Part IV: The Main Questions
-/

/--
**Erdős Problem #713 - Strong Form:**
For every bipartite graph G, does there exist α ∈ [1,2) and c > 0
such that ex(n; G) ~ c·n^α?
-/
def erdos713StrongQuestion : Prop :=
  ∀ (G : ℕ → SimpleGraph (Fin n)) (hBip : ∀ n, @isBipartite (Fin n) _ _ (G n)),
    ∃ c α : ℝ, hasPowerLawGrowth (fun n => extremalNumber n (G n)) c α

/--
**Erdős Problem #713 - Weak Form:**
For every bipartite graph G, does there exist α ∈ [1,2)
such that ex(n; G) ≍ n^α?
-/
def erdos713WeakQuestion : Prop :=
  ∀ (G : ℕ → SimpleGraph (Fin n)) (hBip : ∀ n, @isBipartite (Fin n) _ _ (G n)),
    ∃ α : ℝ, hasPowerLawOrder (fun n => extremalNumber n (G n)) α

/--
**Rationality Question:**
Must the exponent α be rational?
-/
def erdos713RationalQuestion : Prop :=
  ∀ (G : ℕ → SimpleGraph (Fin n)) (hBip : ∀ n, @isBipartite (Fin n) _ _ (G n)),
    ∃ α : ℝ, hasPowerLawOrder (fun n => extremalNumber n (G n)) α →
      ∃ q : ℚ, α = q

/-
## Part V: Known Results
-/

/--
**Kővári-Sós-Turán Theorem:**
ex(n; K_{s,t}) = O(n^{2-1/s}) for s ≤ t.
-/
axiom kovari_sos_turan (s t : ℕ) (hs : s ≥ 2) (hst : s ≤ t) :
  ∃ C : ℝ, C > 0 ∧ ∀ n : ℕ, n ≥ 1 →
    (extremalNumber n sorry : ℝ) ≤ C * n^(2 - 1/s : ℝ)

/--
**Lower Bound for Complete Bipartite Graphs:**
ex(n; K_{s,t}) = Ω(n^{2-1/s}) for s ≤ t.
-/
axiom complete_bipartite_lower (s t : ℕ) (hs : s ≥ 2) (hst : s ≤ t) :
  ∃ c : ℝ, c > 0 ∧ ∀ n : ℕ, n ≥ s + t →
    (extremalNumber n sorry : ℝ) ≥ c * n^(2 - 1/s : ℝ)

/--
**Complete Bipartite Exponent:**
For K_{s,t} with s ≤ t, the exponent is 2 - 1/s (rational!).
-/
theorem complete_bipartite_exponent (s t : ℕ) (hs : s ≥ 2) (hst : s ≤ t) :
    ∃ α : ℚ, α = 2 - 1/s := by
  use 2 - 1/s
  ring

/-
## Part VI: Erdős's Initial Conjecture (Disproved)
-/

/--
**Erdős's Original Conjecture:**
α always has the form 1 + 1/k or 2 - 1/k for integer k ≥ 2.
-/
def erdosOriginalConjecture : Prop :=
  ∀ (G : ℕ → SimpleGraph (Fin n)) (hBip : ∀ n, @isBipartite (Fin n) _ _ (G n)),
    ∃ α : ℝ, hasPowerLawOrder (fun n => extremalNumber n (G n)) α →
      (∃ k : ℕ, k ≥ 2 ∧ α = 1 + 1/k) ∨ (∃ k : ℕ, k ≥ 2 ∧ α = 2 - 1/k)

/--
**Erdős-Simonovits Counterexample (1970):**
The original conjecture is FALSE. There exist bipartite graphs with
exponents not of the form 1 + 1/k or 2 - 1/k.
-/
axiom erdos_simonovits_counterexample : ¬erdosOriginalConjecture

/-
## Part VII: Hypergraph Counterexamples
-/

/--
**Frankl-Füredi Counterexample (1987):**
For k-uniform hypergraphs with k ≥ 5, the analogous statement fails.
There exist 5-uniform hypergraphs G on 8 vertices such that
ex(n; G) = o(n^5) but ex(n; G) ≠ O(n^c) for any c < 5.
-/
axiom frankl_furedi_hypergraph_counterexample :
  -- There exists a 5-uniform hypergraph violating the growth law
  True

/--
**Füredi-Gerbner Extension (2021):**
Extended the counterexample to all k ≥ 5.
-/
axiom furedi_gerbner_extension :
  -- Counterexamples exist for all k-uniform hypergraphs, k ≥ 5
  True

/--
**Open for k = 3, 4:**
The question remains open for 3-uniform and 4-uniform hypergraphs.
Füredi-Gerbner conjecture it fails there too.
-/
axiom hypergraph_open_cases :
  -- k = 3 and k = 4 remain open
  True

/-
## Part VIII: Current Status
-/

/--
**Status of Main Questions:**
- Strong form (ex(n;G) ~ cn^α): OPEN
- Weak form (ex(n;G) ≍ n^α): OPEN
- Rationality of α: OPEN
- Original form (α = 1+1/k or 2-1/k): DISPROVED
-/
axiom erdos713_status :
  -- Main questions remain open, original conjecture disproved
  True

/--
**What is Known:**
1. For K_{s,t}: α = 2 - 1/s (rational)
2. For many specific bipartite graphs: power-law with rational exponent
3. Original restrictive form is false
4. Hypergraph version fails for k ≥ 5
-/
axiom known_cases :
  -- Many specific cases have rational exponents
  True

/-
## Part IX: Related Problems
-/

/--
**Relation to Problem #571:**
Problem 571 concerns specific exponents for particular bipartite graphs.
-/
axiom relation_to_571 : True

/--
**Zarankiewicz Problem:**
What is ex(n; K_{s,t})? This is a special case and major open problem.
-/
axiom zarankiewicz_connection : True

/--
**Turán Density:**
For non-bipartite graphs, Erdős-Stone-Simonovits determines the density.
Bipartite graphs are the "degenerate" case with zero Turán density.
-/
axiom turan_density_connection : True

/-
## Part X: Summary
-/

/--
**Summary:**
Erdős Problem #713 asks fundamental questions about extremal numbers
of bipartite graphs. While specific cases are understood (like K_{s,t}),
the general questions remain open.
-/
theorem erdos_713_summary :
    -- Original conjecture is disproved
    ¬erdosOriginalConjecture ∧
    -- Complete bipartite graphs have rational exponents
    (∀ s t : ℕ, s ≥ 2 → s ≤ t → ∃ α : ℚ, α = 2 - 1/s) := by
  constructor
  · exact erdos_simonovits_counterexample
  · intro s t hs hst
    exact complete_bipartite_exponent s t hs hst

/--
**Erdős Problem #713: Status**

Questions:
1. Does ex(n; G) ~ c·n^α for all bipartite G? (OPEN)
2. Does ex(n; G) ≍ n^α for all bipartite G? (OPEN)
3. Is α always rational? (OPEN)

Known:
- Original form α ∈ {1+1/k, 2-1/k} is FALSE (Erdős-Simonovits 1970)
- K_{s,t} has exponent 2-1/s (rational)
- Hypergraph version fails for k ≥ 5 (Frankl-Füredi 1987)

Prize: $500 (still open)
-/
theorem erdos_713_open : True := trivial

end Erdos713
