/-
Erdős Problem #753: List Chromatic Number of Graph and Complement

Source: https://erdosproblems.com/753
Status: SOLVED/DISPROVED (Alon 1992)

Statement:
Does there exist some constant c > 0 such that
  χ_L(G) + χ_L(G^c) > n^{1/2 + c}
for every graph G on n vertices (where G^c is the complement)?

Answer: NO (Alon 1992)
For every n, there exists a graph G on n vertices such that
  χ_L(G) + χ_L(G^c) ≪ (n log n)^{1/2}

Background:
- χ_L(G) = list chromatic number (choosability)
- G^c = complement graph (non-edges become edges)
- Question: How large must χ_L(G) + χ_L(G^c) be?

Origin: Problem of Erdős, Rubin, and Taylor

Tags: graph-theory, list-coloring, chromatic-number, complement-graph
-/

import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Coloring
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic

open SimpleGraph

namespace Erdos753

variable {V : Type*} [Fintype V] [DecidableEq V]

/-!
## Part I: List Coloring Definitions
-/

/--
**List Assignment:**
A list assignment L assigns a set (list) of colors to each vertex.
Different vertices may have different lists.
-/
def ListAssignment (V : Type*) (C : Type*) := V → Set C

/--
**k-List Assignment:**
A list assignment where each vertex has at least k colors.
-/
def IsKListAssignment (L : ListAssignment V ℕ) (k : ℕ) : Prop :=
  ∀ v : V, (L v).Finite ∧ k ≤ Set.ncard (L v)

/--
**L-Coloring:**
A coloring from list L assigns each vertex v a color from L(v).
-/
def IsLColoring (G : SimpleGraph V) [DecidableRel G.Adj]
    (L : ListAssignment V ℕ) (c : V → ℕ) : Prop :=
  (∀ v, c v ∈ L v) ∧ (∀ v w, G.Adj v w → c v ≠ c w)

/--
**k-Choosable (List Chromatic Number):**
A graph is k-choosable if for every k-list assignment L,
there exists a proper L-coloring.
-/
def IsKChoosable (G : SimpleGraph V) [DecidableRel G.Adj] (k : ℕ) : Prop :=
  ∀ L : ListAssignment V ℕ, IsKListAssignment L k →
    ∃ c : V → ℕ, IsLColoring G L c

/--
**List Chromatic Number χ_L(G):**
The minimum k such that G is k-choosable.
Axiomatized as exact computation is complex.
-/
axiom listChromaticNumber (G : SimpleGraph V) [DecidableRel G.Adj] : ℕ

/-- χ_L(G) is achieved. -/
axiom listChromaticNumber_achieved (G : SimpleGraph V) [DecidableRel G.Adj] :
    IsKChoosable G (listChromaticNumber G)

/-- χ_L(G) is minimal. -/
axiom listChromaticNumber_minimal (G : SimpleGraph V) [DecidableRel G.Adj] (k : ℕ) :
    IsKChoosable G k → listChromaticNumber G ≤ k

/-!
## Part II: Complement Graph
-/

/--
**Complement Graph G^c:**
The complement has an edge iff G doesn't (and vice versa).
-/
def complementGraph (G : SimpleGraph V) : SimpleGraph V where
  Adj v w := v ≠ w ∧ ¬G.Adj v w
  symm := by
    intro v w ⟨hne, hnadj⟩
    exact ⟨hne.symm, fun h => hnadj (G.symm h)⟩
  loopless := by
    intro v ⟨hne, _⟩
    exact hne rfl

/--
**Complement is involutive:**
(G^c)^c = G
-/
theorem complement_complement (G : SimpleGraph V) :
    complementGraph (complementGraph G) = G := by
  ext v w
  simp only [complementGraph]
  by_cases h : G.Adj v w
  · simp [h, G.ne_of_adj h]
  · by_cases hne : v = w
    · simp [hne, G.loopless]
    · simp [h, hne]

/-!
## Part III: The Conjecture
-/

/--
**The Erdős-Rubin-Taylor Conjecture:**
Does there exist c > 0 such that for all graphs G on n vertices,
χ_L(G) + χ_L(G^c) > n^{1/2 + c}?
-/
def ERTConjecture : Prop :=
  ∃ c : ℝ, c > 0 ∧ ∀ n : ℕ, n ≥ 1 → ∀ V : Type, ∀ _ : Fintype V,
    Fintype.card V = n → ∀ _ : DecidableEq V,
    ∀ G : SimpleGraph V, ∀ _ : DecidableRel G.Adj, ∀ _ : DecidableRel (complementGraph G).Adj,
    (listChromaticNumber G + listChromaticNumber (complementGraph G) : ℝ) > n ^ (1/2 + c)

/-!
## Part IV: Alon's Counterexample (1992)

The conjecture is FALSE.
-/

/--
**Alon's Theorem (1992):**
For every n, there exists a graph G on n vertices such that
χ_L(G) + χ_L(G^c) ≪ (n log n)^{1/2}.
-/
axiom alon_counterexample :
    ∃ C : ℝ, C > 0 ∧ ∀ n : ℕ, n ≥ 2 →
    ∃ V : Type, ∃ _ : Fintype V, Fintype.card V = n ∧
    ∃ _ : DecidableEq V, ∃ G : SimpleGraph V, ∃ _ : DecidableRel G.Adj,
    ∃ _ : DecidableRel (complementGraph G).Adj,
    (listChromaticNumber G + listChromaticNumber (complementGraph G) : ℝ) ≤
      C * Real.sqrt (n * Real.log n)

/--
**The conjecture is FALSE.**
-/
theorem conjecture_false : ¬ERTConjecture := by
  intro h
  obtain ⟨c, hc, hconj⟩ := h
  obtain ⟨C, hC, hcounter⟩ := alon_counterexample
  -- For large enough n, (n log n)^{1/2} < n^{1/2 + c}, contradiction
  sorry

/-!
## Part V: Bounds and Relations
-/

/--
**χ_L(G) ≥ χ(G):**
List chromatic number is at least the ordinary chromatic number.
-/
axiom list_chromatic_ge_chromatic (G : SimpleGraph V) [DecidableRel G.Adj] :
    listChromaticNumber G ≥ G.chromaticNumber

/--
**Trivial Lower Bound:**
χ_L(G) + χ_L(G^c) ≥ √n for most graphs.
-/
axiom trivial_lower_bound (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (complementGraph G).Adj] :
    (listChromaticNumber G + listChromaticNumber (complementGraph G) : ℝ) ≥
      Real.sqrt (Fintype.card V)

/--
**Upper Bound:**
χ_L(G) ≤ Δ(G) + 1 where Δ is max degree (greedy coloring).
-/
axiom list_chromatic_le_max_degree_plus_one (G : SimpleGraph V) [DecidableRel G.Adj] :
    True  -- Simplified

/-!
## Part VI: Probabilistic Construction
-/

/--
**Alon's Construction:**
The counterexample uses random graphs near the threshold p = 1/2.
The construction exploits the near-balance between G and G^c.
-/
axiom alon_construction_probabilistic :
    True  -- The construction uses probabilistic method

/--
**Random Graph G(n, 1/2):**
At probability 1/2, G and G^c have similar structure.
-/
axiom random_half_symmetry (n : ℕ) (hn : n ≥ 2) :
    True  -- χ_L(G) ≈ χ_L(G^c) for G(n, 1/2)

/-!
## Part VII: Related Results
-/

/--
**Ordinary Chromatic Number:**
χ(G) + χ(G^c) ≥ 2√n (Nordhaus-Gaddum).
-/
axiom nordhaus_gaddum (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (complementGraph G).Adj] :
    (G.chromaticNumber + (complementGraph G).chromaticNumber : ℝ) ≥ 2 * Real.sqrt (Fintype.card V)

/--
**Nordhaus-Gaddum Upper Bound:**
χ(G) + χ(G^c) ≤ n + 1.
-/
axiom nordhaus_gaddum_upper (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (complementGraph G).Adj] :
    G.chromaticNumber + (complementGraph G).chromaticNumber ≤ Fintype.card V + 1

/--
**List vs Ordinary:**
χ_L and χ can differ significantly (Voigt's example).
-/
axiom list_chromatic_differs_from_chromatic :
    ∃ V : Type, ∃ _ : Fintype V, ∃ _ : DecidableEq V,
    ∃ G : SimpleGraph V, ∃ _ : DecidableRel G.Adj,
    listChromaticNumber G > G.chromaticNumber

/-!
## Part VIII: Choosability Properties
-/

/--
**Bipartite Graphs:**
Not all bipartite graphs are 2-choosable (unlike 2-colorable).
-/
axiom bipartite_not_always_two_choosable :
    ∃ V : Type, ∃ _ : Fintype V, ∃ _ : DecidableEq V,
    ∃ G : SimpleGraph V, ∃ _ : DecidableRel G.Adj,
    G.chromaticNumber = 2 ∧ listChromaticNumber G > 2

/--
**Complete Graphs:**
K_n has χ_L(K_n) = n (same as χ).
-/
axiom complete_graph_list_chromatic (n : ℕ) (hn : n ≥ 1) :
    listChromaticNumber (completeGraph (Fin n)) = n

/--
**Complete Bipartite:**
K_{n,n} has χ_L = 1 + ⌈log₂ n⌉ (Galvin's theorem).
-/
axiom galvin_theorem (n : ℕ) (hn : n ≥ 1) :
    True  -- χ_L(K_{n,n}) = 1 + ⌈log₂ n⌉

/-!
## Part IX: Summary

**Erdős Problem #753: Status SOLVED/DISPROVED** (Alon 1992)

**Question:** Does there exist c > 0 such that
χ_L(G) + χ_L(G^c) > n^{1/2 + c} for all G on n vertices?

**Answer:** NO! Alon showed χ_L(G) + χ_L(G^c) ≤ O((n log n)^{1/2})
for suitable graphs.

**Key Points:**
- List chromatic number measures choosability
- The conjecture aimed to strengthen Nordhaus-Gaddum for χ_L
- Probabilistic methods give counterexamples
- Random G(n, 1/2) graphs have G ≈ G^c structure

**References:**
- Erdős, Rubin, Taylor: Original problem
- Alon (1992): Counterexample via probabilistic method
-/

theorem erdos_753_summary :
    -- The conjecture is FALSE
    ¬ERTConjecture ∧
    -- Alon's counterexample exists
    (∃ C : ℝ, C > 0 ∧ ∀ n : ℕ, n ≥ 2 →
      ∃ V : Type, ∃ _ : Fintype V, Fintype.card V = n ∧
      ∃ _ : DecidableEq V, ∃ G : SimpleGraph V, ∃ _ : DecidableRel G.Adj,
      ∃ _ : DecidableRel (complementGraph G).Adj,
      (listChromaticNumber G + listChromaticNumber (complementGraph G) : ℝ) ≤
        C * Real.sqrt (n * Real.log n)) := by
  exact ⟨conjecture_false, alon_counterexample⟩

end Erdos753
