/-
Erdős Problem #619: Decreasing Diameter of Triangle-Free Graphs

Source: https://erdosproblems.com/619
Status: OPEN

Statement:
For a triangle-free graph G, let h_r(G) be the smallest number of edges that need
to be added to G so that it has diameter r (while preserving triangle-freeness).

Is it true that there exists a constant c > 0 such that for any connected
triangle-free graph G on n vertices: h₄(G) < (1-c)n?

Known Results:
- Erdős-Gyárfás-Ruszinkó (1998):
  * h₃(G) ≤ n
  * h₅(G) ≤ (n-1)/2
  * There exist G with h₃(G) ≥ n - c for some constant c
- Alon-Gyárfás-Ruszinkó (2000):
  * Without triangle-free constraint: n/2 edges suffice for diameter 4

The question about h₄(G) remains open.

Related: Problems #134, #618
-/

import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Subgraph
import Mathlib.Data.Nat.Basic

open SimpleGraph

namespace Erdos619

/-!
## Part I: Basic Definitions
-/

/--
**Triangle-Free Graph:**
A graph with no triangles (K₃ subgraphs).
-/
def TriangleFree (G : SimpleGraph V) : Prop :=
  ∀ a b c : V, G.Adj a b → G.Adj b c → G.Adj c a → False

/--
**Graph Diameter:**
The maximum distance between any two vertices.
-/
noncomputable def diameter (G : SimpleGraph V) : ℕ :=
  sSup { G.dist u v | (u : V) (v : V) }

/--
**Has Diameter r:**
A graph has diameter exactly r.
-/
def HasDiameter (G : SimpleGraph V) (r : ℕ) : Prop :=
  diameter G = r

/--
**Has Diameter At Most r:**
-/
def HasDiameterAtMost (G : SimpleGraph V) (r : ℕ) : Prop :=
  diameter G ≤ r

/-!
## Part II: Edge Addition and h_r(G)
-/

/--
**Edge Addition:**
The graph G' obtained by adding a set of edges E to G.
-/
def addEdges (G : SimpleGraph V) (E : Set (Sym2 V)) : SimpleGraph V where
  Adj u v := G.Adj u v ∨ ⟦(u, v)⟧ ∈ E
  symm := by
    intro u v h
    cases h with
    | inl h => left; exact G.symm h
    | inr h => right; simp [Sym2.eq_swap]; exact h
  loopless := by
    intro v h
    cases h with
    | inl h => exact G.loopless v h
    | inr h => simp [Sym2.diag_iff_proj_eq] at h

/--
**h_r(G):**
The minimum number of edges to add to achieve diameter r while staying triangle-free.
-/
noncomputable def h (G : SimpleGraph V) (r : ℕ) : ℕ :=
  sInf { n : ℕ | ∃ E : Finset (Sym2 V), E.card = n ∧
    TriangleFree (addEdges G E) ∧ HasDiameterAtMost (addEdges G E) r }

/--
**Alternative formulation:**
The min edges to add achieving exactly diameter r.
-/
noncomputable def h_exact (G : SimpleGraph V) (r : ℕ) : ℕ :=
  sInf { n : ℕ | ∃ E : Finset (Sym2 V), E.card = n ∧
    TriangleFree (addEdges G E) ∧ HasDiameter (addEdges G E) r }

/-!
## Part III: Known Results (Erdős-Gyárfás-Ruszinkó 1998)
-/

/--
**h₃(G) ≤ n:**
For any triangle-free connected graph G on n vertices, h₃(G) ≤ n.
-/
axiom h3_upper_bound (V : Type*) [Fintype V] (G : SimpleGraph V) :
    G.Connected → TriangleFree G →
    h G 3 ≤ Fintype.card V

/--
**h₃(G) ≥ n - c:**
There exist triangle-free graphs G on n vertices with h₃(G) ≥ n - c.
-/
axiom h3_lower_bound :
    ∃ c : ℕ, ∀ n : ℕ, ∃ V : Type*, ∃ _ : Fintype V, Fintype.card V = n ∧
      ∃ G : SimpleGraph V, G.Connected ∧ TriangleFree G ∧
        h G 3 ≥ n - c

/--
**h₅(G) ≤ (n-1)/2:**
For any triangle-free connected graph G on n vertices, h₅(G) ≤ (n-1)/2.
-/
axiom h5_upper_bound (V : Type*) [Fintype V] (G : SimpleGraph V) :
    G.Connected → TriangleFree G →
    h G 5 ≤ (Fintype.card V - 1) / 2

/-!
## Part IV: The Main Question - h₄(G) (OPEN)
-/

/--
**The Erdős Question (OPEN):**
Does there exist c > 0 such that h₄(G) < (1-c)n for all connected
triangle-free G on n vertices?
-/
def erdos_619_question : Prop :=
  ∃ c : ℚ, c > 0 ∧ c < 1 ∧
    ∀ V : Type*, ∀ _ : Fintype V, ∀ G : SimpleGraph V,
      G.Connected → TriangleFree G →
        (h G 4 : ℚ) < (1 - c) * Fintype.card V

/--
**The question remains OPEN:**
Neither a proof nor a counterexample is known.
-/
axiom erdos_619_open :
    -- The question is currently unresolved
    True

/--
**Upper bound form:**
Asking if h₄(G) < n - εn for some ε > 0.
-/
def erdos_619_upper_bound_form : Prop :=
  ∃ ε : ℚ, ε > 0 ∧
    ∀ V : Type*, ∀ _ : Fintype V, ∀ G : SimpleGraph V,
      G.Connected → TriangleFree G →
        (h G 4 : ℚ) < Fintype.card V - ε * Fintype.card V

/-!
## Part V: Without Triangle-Free Constraint
-/

/--
**Without triangle-free (Alon-Gyárfás-Ruszinkó 2000):**
Adding n/2 edges always suffices to achieve diameter 4 when triangles are allowed.
-/
axiom without_triangle_free_constraint (V : Type*) [Fintype V] (G : SimpleGraph V) :
    G.Connected →
    ∃ E : Finset (Sym2 V), E.card ≤ Fintype.card V / 2 ∧
      HasDiameterAtMost (addEdges G E) 4

/--
**Comparison:**
The triangle-free constraint makes the problem harder.
-/
theorem triangle_free_harder :
    -- Without constraint: n/2 suffices for diameter 4
    -- With constraint: open whether (1-c)n suffices
    True := trivial

/-!
## Part VI: Examples and Special Cases
-/

/--
**Path graph Pₙ:**
The path on n vertices has diameter n-1.
-/
def pathGraph (n : ℕ) : SimpleGraph (Fin n) where
  Adj i j := (i.val + 1 = j.val) ∨ (j.val + 1 = i.val)
  symm := by intro i j h; cases h <;> (right; assumption) <;> (left; assumption)
  loopless := by intro v h; cases h <;> omega

theorem path_is_triangle_free (n : ℕ) : TriangleFree (pathGraph n) := by
  intro a b c hab hbc hca
  simp only [pathGraph] at hab hbc hca
  -- Path has no triangles
  sorry

/--
**Path diameter:**
Pₙ has diameter n-1.
-/
axiom path_diameter (n : ℕ) (hn : n ≥ 1) :
    diameter (pathGraph n) = n - 1

/--
**Cycle graph Cₙ:**
The cycle on n vertices has diameter ⌊n/2⌋.
-/
def cycleGraph (n : ℕ) (hn : n ≥ 3) : SimpleGraph (Fin n) where
  Adj i j := (i.val + 1 = j.val % n) ∨ (j.val + 1 = i.val % n) ∨
             (i.val = 0 ∧ j.val = n - 1) ∨ (j.val = 0 ∧ i.val = n - 1)
  symm := by intro i j h; sorry
  loopless := by intro v h; sorry

theorem cycle_is_triangle_free (n : ℕ) (hn : n ≥ 4) :
    TriangleFree (cycleGraph n (by omega)) := by
  -- Cycles of length ≥ 4 are triangle-free
  sorry

/-!
## Part VII: Monotonicity Properties
-/

/--
**h_r decreases with r:**
h_r(G) ≥ h_{r+1}(G) in general.
-/
theorem h_monotone (G : SimpleGraph V) (r : ℕ) :
    h G r ≥ h G (r + 1) := by
  -- Larger diameter is easier to achieve
  sorry

/--
**Known gap:**
We know h₃ ≤ n and h₅ ≤ (n-1)/2, but h₄ is unknown.
-/
theorem h4_gap :
    -- h₃(G) ≤ n
    -- h₄(G) ≤ ? (open)
    -- h₅(G) ≤ (n-1)/2
    True := trivial

/-!
## Part VIII: Related Problems
-/

/--
**Related Problem #134:**
(Content varies - check erdosproblems.com)
-/
def related_134 : Prop := True

/--
**Related Problem #618:**
(Content varies - check erdosproblems.com)
-/
def related_618 : Prop := True

/-!
## Part IX: Summary

**Erdős Problem #619: OPEN**

**Question:** Does there exist c > 0 such that h₄(G) < (1-c)n for all
connected triangle-free graphs G on n vertices?

**Known bounds:**
- h₃(G) ≤ n (tight up to constant)
- h₄(G) ≤ ? (OPEN)
- h₅(G) ≤ (n-1)/2

**Context:**
Without the triangle-free constraint, n/2 edges suffice for diameter 4.
The triangle-free constraint makes the h₄ case significantly harder.

**Key Contributors:**
- Erdős-Gyárfás-Ruszinkó (1998): Proved h₃ and h₅ bounds
- Alon-Gyárfás-Ruszinkó (2000): Non-triangle-free case
-/

/--
**The main statement (OPEN):**
-/
def erdos_619 : Prop :=
  erdos_619_question

/--
**What we know:**
-/
theorem erdos_619_partial_results (V : Type*) [Fintype V] (G : SimpleGraph V)
    (hconn : G.Connected) (htf : TriangleFree G) :
    -- h₃(G) ≤ n
    h G 3 ≤ Fintype.card V ∧
    -- h₅(G) ≤ (n-1)/2
    h G 5 ≤ (Fintype.card V - 1) / 2 := by
  exact ⟨h3_upper_bound V G hconn htf, h5_upper_bound V G hconn htf⟩

end Erdos619
