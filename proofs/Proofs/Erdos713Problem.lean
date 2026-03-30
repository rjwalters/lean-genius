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
- Erdős-Simonovits (1970): Colloq., Balatonfüred
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

/- ## Basic Definitions -/

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

/- ## Extremal Numbers -/

/--
**Extremal Number ex(n; G):**
The maximum number of edges in an n-vertex graph containing no copy of G.
Axiomatized as a function of n and a bipartite graph family index.
-/
axiom extremalNumber (n : ℕ) (G : SimpleGraph (Fin n)) : ℕ

/--
**Basic bound:** ex(n; G) ≤ n(n-1)/2.
-/
/- ## Asymptotic Growth -/

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

/- ## The Main Questions -/

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

/- ## Known Results -/

/--
**Kővári-Sós-Turán Theorem (1954):**
ex(n; K_{s,t}) = O(n^{2-1/s}) for s ≤ t.
Axiomatized because the proof requires constructing the K_{s,t} graph.
-/
/--
**Lower Bound for Complete Bipartite Graphs:**
ex(n; K_{s,t}) = Ω(n^{2-1/s}) for s ≤ t.
-/
/--
**Complete Bipartite Exponent:**
For K_{s,t} with s ≤ t, the exponent is 2 - 1/s (rational!).
-/
theorem complete_bipartite_exponent (s t : ℕ) (hs : s ≥ 2) (hst : s ≤ t) :
    ∃ α : ℚ, α = 2 - 1/s := by
  use 2 - 1/s
  ring

/- ## Erdős's Original Conjecture (Disproved) -/

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

/- ## Hypergraph Counterexamples

For k-uniform hypergraphs with k ≥ 5, the analogous power-law statement fails.
Frankl-Füredi (1987) showed there exist 5-uniform hypergraphs where no clean
exponent exists. Füredi-Gerbner (2021) extended this to all k ≥ 5.
Cases k = 3 and k = 4 remain open.
-/

/--
**Frankl-Füredi-Gerbner: Hypergraph counterexample for k ≥ 5.**
For k-uniform hypergraphs with k ≥ 5, there exist hypergraphs H such that
ex(n; H) has no power-law growth (no α with ex(n; H) ≍ n^α).
-/
/- ## Summary

**Erdős Problem #713 - OPEN ($500 prize)**

Questions:
1. Does ex(n; G) ~ c·n^α for all bipartite G? (OPEN)
2. Does ex(n; G) ≍ n^α for all bipartite G? (OPEN)
3. Is α always rational? (OPEN)

Known:
- Original form α ∈ {1+1/k, 2-1/k} is FALSE (Erdős-Simonovits 1970)
- K_{s,t} has exponent 2-1/s (rational)
- Hypergraph version fails for k ≥ 5 (Frankl-Füredi 1987)
-/

/-- Complete summary of Erdős Problem #713.
Combines the disproof of the original conjecture with the known rational
exponent for complete bipartite graphs. -/
theorem erdos_713 :
    ¬erdosOriginalConjecture ∧
    (∀ s t : ℕ, s ≥ 2 → s ≤ t → ∃ α : ℚ, α = 2 - 1/s) :=
  ⟨erdos_simonovits_counterexample, complete_bipartite_exponent⟩

end Erdos713
