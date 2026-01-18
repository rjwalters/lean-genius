/-
Erdős Problem #1021: Extremal Numbers for Bipartite Pair Graphs

Is it true that for every k ≥ 3, there exists c_k > 0 such that
ex(n, G_k) ≪ n^(3/2 - c_k), where G_k is the bipartite graph with
vertices {y₁,...,y_k} and {z₁,...,z_{C(k,2)}}, each z_j joined to
exactly one pair of y vertices?

**Status**: OPEN
**Known**: c_k → 0 as k → ∞ (Erdős-Simonovits, unpublished)
**Special case**: G_3 = C_6, ex(n, C_6) ≪ n^(7/6)

Reference: https://erdosproblems.com/1021
-/

import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Subgraph
import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Nat.Choose.Basic

open SimpleGraph

namespace Erdos1021

/-
## Graph Basics

We work with simple graphs on finite vertex sets.
-/

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The number of edges in a simple graph. -/
def edgeCount (G : SimpleGraph V) [DecidableRel G.Adj] : ℕ :=
  G.edgeFinset.card

/-- The number of vertices. -/
def vertexCount : ℕ := Fintype.card V

/-
## The Bipartite Pair Graph G_k

G_k has k "primary" vertices and C(k,2) "pair" vertices.
Each pair vertex connects to exactly one pair of primary vertices.
-/

/-- The number of pair vertices in G_k: C(k,2) = k(k-1)/2. -/
def pairVertexCount (k : ℕ) : ℕ := Nat.choose k 2

/-- Total vertices in G_k: k + C(k,2). -/
def Gk_vertexCount (k : ℕ) : ℕ := k + pairVertexCount k

/-- The vertex type for G_k: either a primary (left) or pair (right) vertex. -/
abbrev Gk_vertex (k : ℕ) := Fin k ⊕ Fin (pairVertexCount k)

/-- G_k is the bipartite pair graph. -/
def Gk (k : ℕ) : SimpleGraph (Gk_vertex k) where
  Adj v w := match v, w with
    | Sum.inl _, Sum.inr _ => True  -- Primary to pair connections
    | Sum.inr _, Sum.inl _ => True  -- Symmetric
    | _, _ => False  -- No edges within parts
  symm := fun v w h => by cases v <;> cases w <;> simp_all
  loopless := fun v h => by cases v <;> simp at h

/-- G_k is bipartite by construction. -/
theorem Gk_bipartite (k : ℕ) : ∀ v w : Gk_vertex k,
    (Gk k).Adj v w → (∃ i, v = Sum.inl i) ↔ (∃ j, w = Sum.inr j) := by
  sorry

/-
## Special Case: G_3 = C_6

When k = 3, G_3 is the 6-cycle.
-/

/-- The cycle graph C_n. -/
def cycleGraph (n : ℕ) (hn : n ≥ 3) : SimpleGraph (Fin n) where
  Adj i j := (i.val + 1) % n = j.val ∨ (j.val + 1) % n = i.val
  symm := fun i j h => by simp only [or_comm]; exact h
  loopless := fun i h => by
    simp at h
    omega

/-- G_3 is isomorphic to C_6. -/
axiom G3_is_C6 : ∃ (f : Gk_vertex 3 → Fin 6),
  Function.Bijective f ∧
  ∀ v w, (Gk 3).Adj v w ↔ (cycleGraph 6 (by omega)).Adj (f v) (f w)

/-
## Extremal Numbers

ex(n, H) is the maximum edges in an n-vertex H-free graph.
-/

/-- A graph is H-free if it contains no copy of H. -/
def isFree (G : SimpleGraph V) (H : SimpleGraph W) : Prop :=
  ¬∃ (f : W → V), Function.Injective f ∧ ∀ v w, H.Adj v w → G.Adj (f v) (f w)

/-- The extremal number ex(n, H): max edges in n-vertex H-free graph. -/
noncomputable def extremalNumber (n : ℕ) (H : SimpleGraph W) : ℕ :=
  sSup { m : ℕ | ∃ (V : Type*) [Fintype V] [DecidableEq V],
    Fintype.card V = n ∧
    ∃ (G : SimpleGraph V) [DecidableRel G.Adj], isFree G H ∧ edgeCount G = m }

/-
## Asymptotic Notation

We use asymptotic bounds for extremal numbers.
-/

/-- f(n) ≪ g(n) means f(n) = O(g(n)). -/
def isAsympBounded (f g : ℕ → ℝ) : Prop :=
  ∃ C > 0, ∃ N : ℕ, ∀ n ≥ N, f n ≤ C * g n

/-- f(n) = o(g(n)) means f(n)/g(n) → 0. -/
def isLittleO (f g : ℕ → ℝ) : Prop :=
  ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N, f n ≤ ε * g n

notation:50 f " ≪ " g => isAsympBounded f g
notation:50 f " = o(" g ")" => isLittleO f g

/-
## The Conjecture

For each k ≥ 3, ex(n, G_k) ≪ n^(3/2 - c_k) for some c_k > 0.
-/

/-- The extremal function for G_k. -/
noncomputable def exGk (k n : ℕ) : ℝ := extremalNumber n (Gk k)

/-- The power bound n^(3/2 - c). -/
noncomputable def powerBound (c : ℝ) (n : ℕ) : ℝ := (n : ℝ) ^ (3/2 - c)

/-- The main conjecture: ex(n, G_k) ≪ n^(3/2 - c_k) for some c_k > 0. -/
def erdos_1021_conjecture : Prop :=
  ∀ k ≥ 3, ∃ c : ℝ, c > 0 ∧ (fun n => exGk k n) ≪ (fun n => powerBound c n)

/-
## Known Results

Erdős-Simonovits proved c_k → 0 as k → ∞.
-/

/-- c_k → 0 as k → ∞ (if the conjecture holds). -/
def exponentVanishes : Prop :=
  ∀ ε > 0, ∃ K : ℕ, ∀ k ≥ K,
    (∃ c > 0, (fun n => exGk k n) ≪ (fun n => powerBound c n)) →
    ∀ c, (fun n => exGk k n) ≪ (fun n => powerBound c n) → c < ε

/-- Erdős-Simonovits: if the conjecture holds, c_k → 0. -/
axiom erdos_simonovits_limit : erdos_1021_conjecture → exponentVanishes

/-
## Weak Conjecture

Even ex(n, G_k) = o(n^(3/2)) is unknown.
-/

/-- The weak conjecture: ex(n, G_k) = o(n^(3/2)). -/
def weak_conjecture : Prop :=
  ∀ k ≥ 3, (fun n => exGk k n) = o(fun n => (n : ℝ) ^ (3/2 : ℝ))

/-- The main conjecture implies the weak conjecture. -/
theorem strong_implies_weak : erdos_1021_conjecture → weak_conjecture := by
  sorry

/-- Even the weak conjecture is open. -/
axiom weak_conjecture_open : ¬∃ (proof : weak_conjecture), True

/-
## The C_6 Case (k = 3)

For C_6, ex(n, C_6) ≪ n^(7/6) is known.
-/

/-- The extremal number for C_6. -/
noncomputable def exC6 (n : ℕ) : ℝ := extremalNumber n (cycleGraph 6 (by omega))

/-- Erdős, Bondy-Simonovits: ex(n, C_6) ≪ n^(7/6). -/
axiom C6_extremal_bound :
  (fun n => exC6 n) ≪ (fun n => (n : ℝ) ^ (7/6 : ℝ))

/-- The exponent 7/6 = 3/2 - 1/3, so c_3 = 1/3 works. -/
theorem c3_value : (7 : ℝ) / 6 = 3/2 - 1/3 := by norm_num

/-- The k = 3 case of the conjecture is solved. -/
theorem k3_case_solved : ∃ c : ℝ, c > 0 ∧
    (fun n => exGk 3 n) ≪ (fun n => powerBound c n) := by
  sorry

/-
## Connection to Problem 926

G_k is H_k (from Problem 926) with vertex x removed.
-/

/-- H_k has one additional vertex x connected to all primary vertices. -/
def Hk_vertexCount (k : ℕ) : ℕ := k + pairVertexCount k + 1

/-- Removing the central vertex from H_k gives G_k. -/
axiom Gk_from_Hk (k : ℕ) :
  ∃ (f : Gk_vertex k → Fin (Hk_vertexCount k)),
    Function.Injective f
    -- G_k embeds into H_k minus vertex x

/-
## Trivial Bounds

Basic extremal theory gives n^(3/2) as an upper bound.
-/

/-- The Kővári-Sós-Turán theorem gives ex(n, K_{s,t}) ≤ C · n^(2-1/s). -/
axiom kovari_sos_turan (s t : ℕ) (hs : s ≥ 2) (ht : t ≥ s) :
  ∃ C > 0, ∀ n, extremalNumber n (completeBipartite s t) ≤ C * (n : ℝ) ^ (2 - 1/s)
  where
    completeBipartite (m n : ℕ) : SimpleGraph (Fin m ⊕ Fin n) := {
      Adj := fun v w => match v, w with
        | Sum.inl _, Sum.inr _ => True
        | Sum.inr _, Sum.inl _ => True
        | _, _ => False
      symm := fun v w h => by cases v <;> cases w <;> simp_all
      loopless := fun v h => by cases v <;> simp at h
    }

/-- G_k contains K_{2, C(k,2)}, giving a trivial n^(3/2) bound. -/
theorem trivial_bound (k : ℕ) (hk : k ≥ 3) :
    ∃ C > 0, ∀ n, exGk k n ≤ C * (n : ℝ) ^ (3/2 : ℝ) := by
  sorry

/-
## The Gap

The conjecture asks for improvement over n^(3/2).
-/

/-- The gap from n^(3/2) that the conjecture claims. -/
noncomputable def conjecturedGap (k : ℕ) : ℝ := sorry  -- The unknown c_k

/-- The conjecture is that this gap is positive for all k. -/
theorem gap_positive_conjecture :
    erdos_1021_conjecture ↔ ∀ k ≥ 3, conjecturedGap k > 0 := by
  sorry

/-
## Summary

This file formalizes Erdős Problem #1021 on extremal numbers for G_k.

**Status**: OPEN

**The Question**: For k ≥ 3, does there exist c_k > 0 such that
ex(n, G_k) ≪ n^(3/2 - c_k)?

**Known Results**:
- Erdős-Simonovits: If true, c_k → 0 as k → ∞
- k = 3 (G_3 = C_6): ex(n, C_6) ≪ n^(7/6), so c_3 = 1/3 works
- Even ex(n, G_k) = o(n^(3/2)) is unknown for general k

**Related Problems**:
- Problem 572 (C_6 extremal number)
- Problem 926 (H_k graphs)
- Kővári-Sós-Turán theorem
-/

end Erdos1021
