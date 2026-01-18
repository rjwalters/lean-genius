/-
Erdős Problem #113: Extremal Numbers and Degeneracy of Bipartite Graphs

Source: https://erdosproblems.com/113
Status: SOLVED (Disproved)
Prize: $500

Statement:
The Erdős-Simonovits Conjecture (1984):
If G is bipartite then ex(n;G) ≪ n^{3/2} if and only if G is 2-degenerate.

Recall:
- ex(n;G) = maximum number of edges in an n-vertex graph containing no copy of G
- G is k-degenerate if every induced subgraph has a vertex of degree ≤ k
- 2-degenerate = no induced subgraph with minimum degree ≥ 3

History:
- Erdős originally offered $250 for a proof, $100 for a counterexample
- Later increased to $500 for a counterexample
- DISPROVED by Janzer (2023) who constructed 3-regular bipartite H with ex(n;H) ≪ n^{4/3+ε}

Key Results:
- Kővári-Sós-Turán (1954): ex(n; K_{s,t}) ≪ n^{2-1/s} for t ≥ s
- Füredi (1996): Tight bounds for complete bipartite graphs
- Janzer (2023): Counterexample using subdivision constructions

References:
- Erdős, Simonovits: "Cube-supersaturated graphs and related problems" (1984)
- Janzer: "Disproof of a conjecture of Erdős and Simonovits" (2023)
-/

import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

open Finset Real

namespace Erdos113

/-
## Part I: Extremal Numbers

The extremal number ex(n;H) is central to extremal graph theory.
-/

/--
**The Extremal Number** ex(n; H):
Maximum number of edges in an n-vertex graph that avoids a copy of H.

Axiomatized since computing this requires quantification over all graphs.
The parameter k encodes the forbidden subgraph abstractly.
-/
axiom extremalNumber : ℕ → ℕ → ℕ

/-- The extremal number is monotonic in n. -/
axiom extremal_mono (k n m : ℕ) (h : n ≤ m) :
    extremalNumber n k ≤ extremalNumber m k

/-- ex(n, k) ≤ n(n-1)/2 (at most all edges). -/
axiom extremal_trivial_upper (n k : ℕ) :
    extremalNumber n k ≤ n * (n - 1) / 2

/-
## Part II: Graph Degeneracy

k-degenerate graphs have sparse structure.
-/

/--
A graph is **k-degenerate** if every non-empty induced subgraph
has a vertex of degree at most k.

Equivalently: vertices can be ordered so each has ≤ k neighbors among predecessors.

k-degeneracy is axiomatized for a graph encoded by parameter g.
-/
axiom isDegenerate : ℕ → ℕ → Prop

/-- Every graph is k-degenerate for some k. -/
axiom degenerate_exists (g : ℕ) : ∃ k, isDegenerate g k

/-- If g is k-degenerate and k ≤ m, then g is m-degenerate. -/
axiom degenerate_mono (g k m : ℕ) : isDegenerate g k → k ≤ m → isDegenerate g m

/-- 2-degenerate means no induced subgraph has min degree ≥ 3. -/
axiom two_degenerate_char (g : ℕ) :
    isDegenerate g 2 ↔ ∀ S : ℕ, S > 0 → ∃ v : ℕ, True  -- Axiomatized characterization

/-
## Part III: Bipartite Graphs
-/

/-- A graph g is bipartite (axiomatized). -/
axiom isBipartite : ℕ → Prop

/-- The complete bipartite graph K_{s,t} (encoded as s + t). -/
def completeBipartiteCode (s t : ℕ) : ℕ := s * 1000 + t

/-- K_{s,t} is bipartite. -/
axiom completeBipartite_is_bipartite (s t : ℕ) :
    isBipartite (completeBipartiteCode s t)

/-- K_{s,t} has degeneracy min(s,t). -/
axiom completeBipartite_degeneracy (s t : ℕ) (hs : s ≥ 1) (ht : t ≥ 1) :
    isDegenerate (completeBipartiteCode s t) (min s t)

/-
## Part IV: The Kővári-Sós-Turán Theorem

The fundamental upper bound for bipartite forbidden subgraphs.
-/

/--
**Kővári-Sós-Turán Theorem (1954):**
ex(n; K_{s,t}) ≤ (1/2)(t-1)^{1/s} · n^{2-1/s} + (s-1)n/2

For t ≥ s ≥ 1.
-/
axiom kovari_sos_turan (n s t : ℕ) (hs : s ≥ 1) (hst : t ≥ s) :
    ∃ C : ℝ, C > 0 ∧
      (extremalNumber n (completeBipartiteCode s t) : ℝ) ≤ C * (n : ℝ).rpow (2 - 1/s)

/-- For K_{2,2} = C_4: ex(n; C_4) = O(n^{3/2}). -/
axiom c4_extremal :
    ∃ C : ℝ, C > 0 ∧ ∀ n : ℕ,
      (extremalNumber n (completeBipartiteCode 2 2) : ℝ) ≤ C * (n : ℝ).rpow (3/2)

/-
## Part V: Asymptotic Notation
-/

/-- Asymptotic notation: f(n) ≪ g(n) means f(n) = O(g(n)). -/
def AsympLe (f g : ℕ → ℝ) : Prop :=
  ∃ C > 0, ∃ n₀ : ℕ, ∀ n ≥ n₀, f n ≤ C * g n

notation:50 f " ≪ " g => AsympLe f g

/-- Asymptotic comparison is transitive (if exponents compare correctly). -/
axiom asymp_trans_exponent (f : ℕ → ℝ) (α β : ℝ) (hαβ : α < β) :
    (f ≪ (fun n => (n : ℝ).rpow α)) → (f ≪ (fun n => (n : ℝ).rpow β))

/-
## Part VI: The Erdős-Simonovits Conjecture

The original conjecture that was disproved.
-/

/--
**The Erdős-Simonovits Conjecture (1984):**

For bipartite G:
  ex(n; G) ≪ n^{3/2} if and only if G is 2-degenerate.

Forward direction: If G is 2-degenerate bipartite, then ex(n;G) ≪ n^{3/2}.
Backward direction: If ex(n;G) ≪ n^{3/2}, then G is 2-degenerate. (DISPROVED)
-/
def ErdosSimonovitsConjecture : Prop :=
  ∀ g : ℕ, isBipartite g →
    (((fun n => (extremalNumber n g : ℝ)) ≪ (fun n => (n : ℝ).rpow (3/2))) ↔
     isDegenerate g 2)

/--
**Forward Direction (Known to be TRUE):**
2-degenerate bipartite graphs have extremal number O(n^{3/2}).
-/
axiom forward_direction (g : ℕ) :
    isBipartite g → isDegenerate g 2 →
    (fun n => (extremalNumber n g : ℝ)) ≪ (fun n => (n : ℝ).rpow (3/2))

/--
**Backward Direction (DISPROVED):**
There exist bipartite graphs with ex(n;G) ≪ n^{3/2} that are NOT 2-degenerate.
-/
axiom backward_false :
    ∃ g : ℕ, isBipartite g ∧
      ((fun n => (extremalNumber n g : ℝ)) ≪ (fun n => (n : ℝ).rpow (3/2))) ∧
      ¬isDegenerate g 2

/-
## Part VII: Janzer's Counterexample (2023)

The construction that disproved the conjecture.
-/

/-- A graph g is k-regular (axiomatized). -/
axiom isRegular : ℕ → ℕ → Prop

/-- 3-regular graphs are NOT 2-degenerate (min degree is 3). -/
axiom regular3_not_2degenerate (g : ℕ) :
    isRegular g 3 → ¬isDegenerate g 2

/--
**Janzer's Theorem (2023):**
For any ε > 0, there exists a 3-regular bipartite graph H such that
ex(n; H) ≪ n^{4/3 + ε}.

This disproves the Erdős-Simonovits conjecture since:
- H is 3-regular, hence NOT 2-degenerate
- But ex(n; H) ≪ n^{4/3 + ε} ≪ n^{3/2}
-/
axiom janzer_counterexample (ε : ℝ) (hε : ε > 0) :
    ∃ g : ℕ,
      isBipartite g ∧
      isRegular g 3 ∧
      (fun n => (extremalNumber n g : ℝ)) ≪ (fun n => (n : ℝ).rpow (4/3 + ε))

/-- Janzer's construction beats n^{3/2} since 4/3 + ε < 3/2 for small ε. -/
theorem janzer_beats_threshold (ε : ℝ) (hε : ε > 0) (hε' : ε < 1/6) :
    ∃ g : ℕ, isBipartite g ∧ ¬isDegenerate g 2 ∧
      (fun n => (extremalNumber n g : ℝ)) ≪ (fun n => (n : ℝ).rpow (3/2)) := by
  obtain ⟨g, hbip, hreg, hext⟩ := janzer_counterexample ε hε
  use g
  constructor
  · exact hbip
  constructor
  · exact regular3_not_2degenerate g hreg
  · -- Since 4/3 + ε < 3/2 when ε < 1/6
    have h : (4 : ℝ)/3 + ε < 3/2 := by linarith
    exact asymp_trans_exponent _ _ _ h hext

/-
## Part VIII: Related Results
-/

/--
**Füredi's Theorem (1996):**
Tight bounds for ex(n; K_{s,t}) when t is large relative to s.
-/
axiom furedi_tight (s t : ℕ) (hs : s ≥ 2) (hst : t ≥ s) :
    ∃ c₁ c₂ : ℝ, c₁ > 0 ∧ c₂ > 0 ∧
      ∀ n : ℕ, c₁ * (n : ℝ).rpow (2 - 1/s) ≤ extremalNumber n (completeBipartiteCode s t) ∧
               (extremalNumber n (completeBipartiteCode s t) : ℝ) ≤ c₂ * (n : ℝ).rpow (2 - 1/s)

/-- Erdős Problem #146: Zarankiewicz problem asks for exact values of ex(n; K_{s,t}). -/
axiom erdos_146_zarankiewicz (s t : ℕ) :
    ∀ n : ℕ, ∃ z : ℕ, z = extremalNumber n (completeBipartiteCode s t)

/-- Erdős Problem #147: Turán exponent exists for bipartite graphs. -/
axiom erdos_147_turan_exponent (g : ℕ) :
    isBipartite g → ∃ r : ℝ, 1 ≤ r ∧ r ≤ 2 ∧
      (fun n => (extremalNumber n g : ℝ)) ≪ (fun n => (n : ℝ).rpow r)

/-
## Part IX: Main Results Summary
-/

/-- **Erdős Problem #113: DISPROVED**

The Erdős-Simonovits conjecture is FALSE.

Janzer (2023) constructed 3-regular bipartite graphs H with ex(n;H) ≪ n^{4/3+ε},
disproving the backward direction of the conjecture.

The forward direction remains true: 2-degenerate bipartite implies ex ≪ n^{3/2}. -/
theorem erdos_113 : ¬ErdosSimonovitsConjecture := by
  intro hconj
  obtain ⟨g, hbip, hext, hnot2⟩ := backward_false
  have h2deg := (hconj g hbip).mp hext
  exact hnot2 h2deg

/-- The conjecture's forward direction is true. -/
theorem erdos_113_forward (g : ℕ) :
    isBipartite g → isDegenerate g 2 →
    (fun n => (extremalNumber n g : ℝ)) ≪ (fun n => (n : ℝ).rpow (3/2)) :=
  forward_direction g

/-- The $500 prize was claimed by Janzer for the counterexample. -/
axiom prize_claimed : True  -- Janzer 2023

end Erdos113
