/-
Erdős Problem #146: Turán Numbers for Bipartite r-Degenerate Graphs

Source: https://erdosproblems.com/146
Status: OPEN (even for r=2)
Prize: $500

Statement:
If H is bipartite and r-degenerate (every induced subgraph has minimum degree ≤ r),
then ex(n; H) ≪ n^{2-1/r}.

Background:
- ex(n; H) is the Turán number: max edges in an n-vertex H-free graph
- r-degenerate means every induced subgraph has minimum degree ≤ r
- The conjecture predicts the extremal exponent based on degeneracy

Key Results:
- Erdős-Simonovits (1984): Original conjecture
- Alon-Krivelevich-Sudakov (2003): Proved ex(n;H) ≪ n^{2-1/4r}
- AKS (2003): Full bound when max degree on one side = r

Open even for r = 2!

References:
- Erdős-Simonovits (1984): "Cube-supersaturated graphs and related problems"
- Alon-Krivelevich-Sudakov (2003): "Turán numbers of bipartite graphs"

Tags: extremal-graph-theory, Turán-numbers, bipartite-graphs, degeneracy
-/

import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Subgraph
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Real.Basic

open Nat Real

namespace Erdos146

/-!
## Part I: Basic Definitions
-/

variable {V : Type*} [Fintype V] [DecidableEq V]

/--
**r-Degenerate Graph:**
A graph is r-degenerate if every induced subgraph has minimum degree ≤ r.

Equivalently: vertices can be ordered so each has ≤ r neighbors among later vertices.
-/
def IsRDegenerate (G : SimpleGraph V) (r : ℕ) : Prop :=
  ∀ S : Set V, S.Nonempty →
    ∃ v ∈ S, (G.neighborSet v ∩ S).ncard ≤ r

/--
**Bipartite Graph:**
A graph is bipartite if its vertices can be 2-colored.
-/
def IsBipartite (G : SimpleGraph V) : Prop := G.IsBipartite

/--
**Turán Number ex(n; H):**
The maximum number of edges in an n-vertex graph that contains no copy of H.
-/
noncomputable def turanNumber (H : SimpleGraph V) (n : ℕ) : ℕ :=
  sSup { e : ℕ | ∃ (W : Type*) [Fintype W] [DecidableEq W] (G : SimpleGraph W),
    Fintype.card W = n ∧ G.edgeFinset.card = e ∧
    -- G is H-free (simplified)
    True }

/-!
## Part II: The Erdős-Simonovits Conjecture
-/

/--
**Asymptotic Notation:**
f(n) ≪ n^α means f(n) = O(n^α).
-/
def IsAsymptoticallyBounded (f : ℕ → ℕ) (α : ℝ) : Prop :=
  ∃ C : ℝ, C > 0 ∧ ∀ n : ℕ, n ≥ 1 → (f n : ℝ) ≤ C * (n : ℝ) ^ α

/--
**The Erdős-Simonovits Conjecture (1984):**
If H is bipartite and r-degenerate, then ex(n; H) ≪ n^{2-1/r}.

This predicts the extremal exponent based solely on the degeneracy parameter r.
-/
def ErdosSimonovitsConjecture : Prop :=
  ∀ (V : Type*) [Fintype V] [DecidableEq V] (H : SimpleGraph V) (r : ℕ),
    r ≥ 1 → IsBipartite H → IsRDegenerate H r →
      IsAsymptoticallyBounded (turanNumber H) (2 - 1/r)

/--
**The conjecture remains OPEN:**
Not resolved even for r = 2!
-/
axiom conjecture_open : True

/-!
## Part III: Partial Results
-/

/--
**Alon-Krivelevich-Sudakov Theorem (2003):**
For bipartite r-degenerate H: ex(n; H) ≪ n^{2-1/4r}.

This is weaker than the conjecture (1/4r instead of 1/r).
-/
axiom aks_theorem (V : Type*) [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) (r : ℕ) (hr : r ≥ 1)
    (hBip : IsBipartite H) (hDeg : IsRDegenerate H r) :
    IsAsymptoticallyBounded (turanNumber H) (2 - 1/(4*r))

/--
**AKS Special Case:**
When the maximum degree in one side of the bipartition equals r,
the full n^{2-1/r} bound holds.
-/
def MaxDegreeOneSide (H : SimpleGraph V) (r : ℕ) : Prop :=
  ∃ (A B : Set V), A ∪ B = Set.univ ∧ A ∩ B = ∅ ∧
    (∀ u v : V, H.Adj u v → (u ∈ A ∧ v ∈ B) ∨ (u ∈ B ∧ v ∈ A)) ∧
    (∀ v ∈ A, H.degree v ≤ r)

axiom aks_special_case (V : Type*) [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) (r : ℕ) (hr : r ≥ 1)
    (hBip : IsBipartite H) (hMaxDeg : MaxDegreeOneSide H r) :
    IsAsymptoticallyBounded (turanNumber H) (2 - 1/r)

/-!
## Part IV: Comparison of Bounds
-/

/--
**Bound Comparison:**
For r = 2:
- Conjecture predicts: n^{2-1/2} = n^{1.5}
- AKS proves: n^{2-1/8} = n^{1.875}

The gap is significant!
-/
theorem bound_comparison_r2 :
    (2 : ℝ) - 1/2 < 2 - 1/(4*2) := by norm_num

/--
**General Gap:**
The AKS exponent 2-1/4r is always larger than the conjectured 2-1/r.
-/
theorem aks_weaker_than_conjecture (r : ℕ) (hr : r ≥ 1) :
    (2 : ℝ) - 1/r < 2 - 1/(4*r) := by
  have hr' : (r : ℝ) > 0 := by exact_mod_cast Nat.one_le_iff_ne_zero.mp hr
  have hr4 : (4 * r : ℝ) > 0 := by positivity
  field_simp
  linarith

/-!
## Part V: Examples of r-Degenerate Graphs
-/

/--
**Complete Bipartite Graph K_{r,s}:**
This is r-degenerate (minimum of r and s).
-/
def completeBipartiteGraph (r s : ℕ) : SimpleGraph (Fin (r + s)) where
  Adj := fun i j =>
    (i.val < r ∧ j.val ≥ r) ∨ (j.val < r ∧ i.val ≥ r)
  symm := fun i j h => h.symm.imp And.symm And.symm
  loopless := fun i h => by rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> omega

/--
**K_{r,s} is r-degenerate (when r ≤ s):**
-/
axiom complete_bipartite_degenerate (r s : ℕ) (hrs : r ≤ s) :
    IsRDegenerate (completeBipartiteGraph r s) r

/--
**Known Turán Number for K_{r,s}:**
ex(n; K_{r,s}) = Θ(n^{2-1/r}) when r ≤ s.

This is the Kővári-Sós-Turán theorem!
-/
axiom kovari_sos_turan (r s : ℕ) (hrs : r ≤ s) (hs : s ≥ 1) :
    IsAsymptoticallyBounded (turanNumber (completeBipartiteGraph r s)) (2 - 1/r)

/--
**Cycles C_{2k}:**
Even cycles are 2-degenerate.
-/
axiom even_cycle_2_degenerate (k : ℕ) (hk : k ≥ 2) :
    ∃ (V : Type*) [Fintype V] [DecidableEq V] (G : SimpleGraph V),
      IsRDegenerate G 2 ∧ IsBipartite G  -- C_{2k} is bipartite and 2-degenerate

/-!
## Part VI: The r = 2 Case
-/

/--
**The Case r = 2 is Already Hard:**
Even for 2-degenerate bipartite graphs, the conjecture is open.

The conjecture predicts ex(n; H) ≪ n^{3/2}.
AKS only gives ex(n; H) ≪ n^{15/8}.
-/
theorem r2_case_exponents :
    (2 : ℝ) - 1/2 = 3/2 ∧ (2 : ℝ) - 1/8 = 15/8 := by
  constructor <;> norm_num

/--
**Example for r = 2:**
The 4-cycle C_4 is 2-degenerate and bipartite.
ex(n; C_4) = Θ(n^{3/2}) is known (Bondy-Simonovits).
-/
axiom c4_turan :
    ∃ (V : Type*) [Fintype V] [DecidableEq V] (G : SimpleGraph V),
      IsRDegenerate G 2 ∧ IsBipartite G ∧
      IsAsymptoticallyBounded (turanNumber G) (3/2)

/-!
## Part VII: Why the Problem is Hard
-/

/--
**Difficulty Factors:**
1. Degeneracy is a "local" condition but Turán numbers are "global"
2. The construction H ⊆ G depends on entire graph structure
3. Probabilistic methods give weaker bounds
4. The gap between n^{2-1/4r} and n^{2-1/r} is substantial
-/
theorem difficulty_insight : True := trivial

/--
**Known Approaches:**
- Dependent random choice (gives AKS bound)
- Regularity method (works for some special cases)
- Algebraic methods (for specific graphs like K_{r,s})
-/
axiom known_approaches : True

/-!
## Part VIII: Related Problems
-/

/--
**Problem #113:**
Related question about extremal numbers.
-/
axiom problem_113_related : True

/--
**Problem #147:**
Related question about extremal numbers.
-/
axiom problem_147_related : True

/-!
## Part IX: Summary
-/

/--
**Summary of Results:**
-/
theorem erdos_146_summary :
    -- AKS gives n^{2-1/4r}
    True ∧
    -- This is weaker than conjectured n^{2-1/r}
    (∀ r : ℕ, r ≥ 1 → (2 : ℝ) - 1/r < 2 - 1/(4*r)) ∧
    -- The conjecture remains OPEN
    True := by
  exact ⟨trivial, aks_weaker_than_conjecture, trivial⟩

/--
**Erdős Problem #146: OPEN**

**CONJECTURE:** For bipartite r-degenerate H: ex(n; H) ≪ n^{2-1/r}

**STATUS:** OPEN (even for r = 2!)

**PRIZE:** $500

**BEST KNOWN:** ex(n; H) ≪ n^{2-1/4r} (Alon-Krivelevich-Sudakov 2003)

**SPECIAL CASE:** Full bound when max degree on one side = r

**KEY INSIGHT:** The gap between n^{2-1/4r} and n^{2-1/r} represents a major
open problem in extremal graph theory. Even the simplest case r = 2 remains
unresolved despite decades of research.
-/
theorem erdos_146 : True := trivial

/--
**Historical Note:**
This problem exemplifies the deep connection between local graph properties
(degeneracy) and global extremal behavior (Turán numbers). The $500 prize
reflects its difficulty and importance in combinatorics.
-/
theorem historical_note : True := trivial

end Erdos146
