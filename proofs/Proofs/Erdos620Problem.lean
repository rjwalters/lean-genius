/-
  Erdős Problem #620: The Erdős-Rogers Problem

  Source: https://erdosproblems.com/620
  Status: OPEN (bounds known, exact answer unknown)

  Statement:
  If G is a K₄-free graph on n vertices, how large a triangle-free
  induced subgraph must G contain?

  Let f(n) = minimum over all K₄-free graphs G on n vertices of
            maximum triangle-free induced subgraph size.

  Known Bounds:
  - Lower: f(n) ≫ n^{1/2} · (log n)^{1/2} / log log n  (Shearer)
  - Upper: f(n) ≪ n^{1/2} · log n  (Mubayi-Verstraete 2024)

  Historical Progress:
  - Bollobás-Hind (1991): n^{1/2} ≪ f(n) ≪ n^{7/10+o(1)}
  - Krivelevich (1994): Upper improved to n^{2/3}(log n)^{1/3}
  - Wolfovitz (2013): Upper improved to n^{1/2}(log n)^{120}
  - Mubayi-Verstraete (2024): Upper improved to n^{1/2} log n

  References:
  [ErRo62] Erdős-Rogers, original problem
  [BoHi91] Bollobás-Hind, first bounds
  [MuVe24] Mubayi-Verstraete, current best upper bound

  Tags: graph-theory, ramsey-theory, induced-subgraphs, extremal-graph-theory
-/

import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Combinatorics.SimpleGraph.Subgraph
import Mathlib.Data.Finset.Card
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

namespace Erdos620

open SimpleGraph Finset

variable {V : Type*} [Fintype V] [DecidableEq V]

/-! ## Part I: Cliques and Forbidden Subgraphs -/

/-- A triangle (K₃) in a graph. -/
def HasTriangle (G : SimpleGraph V) : Prop :=
  ∃ a b c : V, a ≠ b ∧ b ≠ c ∧ a ≠ c ∧ G.Adj a b ∧ G.Adj b c ∧ G.Adj a c

/-- A graph is triangle-free if it contains no K₃. -/
def TriangleFree (G : SimpleGraph V) : Prop := ¬HasTriangle G

/-- A K₄ (complete graph on 4 vertices) in a graph. -/
def HasK4 (G : SimpleGraph V) : Prop :=
  ∃ a b c d : V, a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d ∧ c ≠ d ∧
    G.Adj a b ∧ G.Adj a c ∧ G.Adj a d ∧ G.Adj b c ∧ G.Adj b d ∧ G.Adj c d

/-- A graph is K₄-free if it contains no complete graph on 4 vertices. -/
def K4Free (G : SimpleGraph V) : Prop := ¬HasK4 G

/-- Triangle-free graphs are K₄-free. -/
theorem triangleFree_implies_K4Free (G : SimpleGraph V) (h : TriangleFree G) :
    K4Free G := by
  intro ⟨a, b, c, d, hne, hab, hac, had, hbc, hbd, hcd⟩
  apply h
  exact ⟨a, b, c, hne.1, hne.2.2.1, hne.2.1, hab, hbc, hac⟩

/-! ## Part II: Induced Subgraphs -/

/-- The induced subgraph on a subset of vertices. -/
def inducedSubgraph (G : SimpleGraph V) (S : Finset V) : SimpleGraph S where
  Adj := fun x y => G.Adj x.val y.val
  symm := fun x y h => G.symm h
  loopless := fun x => G.loopless x.val

/-- The size of a vertex set. -/
def vertexCount (S : Finset V) : ℕ := S.card

/-- An induced subgraph is triangle-free. -/
def InducedTriangleFree (G : SimpleGraph V) (S : Finset V) : Prop :=
  TriangleFree (inducedSubgraph G S)

/-- The maximum triangle-free induced subgraph size in G. -/
noncomputable def maxTriangleFreeInduced (G : SimpleGraph V) : ℕ :=
  sSup {k : ℕ | ∃ S : Finset V, S.card = k ∧ InducedTriangleFree G S}

/-! ## Part III: The Erdős-Rogers Function -/

/-- **The Erdős-Rogers Function f(n)**

    f(n) = minimum over all K₄-free graphs G on n vertices of
           the maximum triangle-free induced subgraph size.
-/
noncomputable def erdosRogers (n : ℕ) : ℕ :=
  sInf {k : ℕ | ∀ (G : SimpleGraph (Fin n)), K4Free G → maxTriangleFreeInduced G ≥ k}

/-- Alternative characterization: f(n) is the largest k such that
    every K₄-free graph on n vertices has a triangle-free induced subgraph
    on at least k vertices. -/
def ErdosRogersProperty (n k : ℕ) : Prop :=
  ∀ (G : SimpleGraph (Fin n)), K4Free G →
    ∃ S : Finset (Fin n), S.card ≥ k ∧ InducedTriangleFree G S

/-! ## Part IV: Main Problem Statement -/

/-- **Erdős Problem #620**

    Determine f(n), the minimum triangle-free induced subgraph size
    guaranteed in any K₄-free graph on n vertices.
-/
def Erdos620Statement : Prop :=
  ∃ (f : ℕ → ℕ), ∀ n : ℕ,
    (∀ (G : SimpleGraph (Fin n)), K4Free G → maxTriangleFreeInduced G ≥ f n) ∧
    (∃ (G : SimpleGraph (Fin n)), K4Free G ∧ maxTriangleFreeInduced G = f n)

/-! ## Part V: Known Bounds -/

/-- **Trivial Lower Bound**

    Every K₄-free graph on n vertices has an independent set of size Ω(√n).
    Independent sets are triangle-free, so f(n) ≥ c√n for some c > 0.
-/
axiom trivial_lower_bound :
    ∃ c : ℝ, c > 0 ∧ ∀ n ≥ 1, (erdosRogers n : ℝ) ≥ c * Real.sqrt n

/-- **Shearer's Lower Bound**

    f(n) ≫ n^{1/2} · (log n)^{1/2} / log log n
-/
axiom shearer_lower_bound :
    ∃ c : ℝ, c > 0 ∧ ∀ n ≥ 16,
      (erdosRogers n : ℝ) ≥ c * Real.sqrt n * Real.sqrt (Real.log n) / Real.log (Real.log n)

/-- **Bollobás-Hind Upper Bound (1991)**

    f(n) ≪ n^{7/10 + o(1)}
-/
axiom bollobas_hind_upper :
    ∀ ε > 0, ∃ C : ℝ, C > 0 ∧ ∀ n ≥ 1,
      (erdosRogers n : ℝ) ≤ C * (n : ℝ) ^ ((7:ℝ)/10 + ε)

/-- **Krivelevich Upper Bound (1994)**

    f(n) ≪ n^{2/3} · (log n)^{1/3}
-/
axiom krivelevich_upper :
    ∃ C : ℝ, C > 0 ∧ ∀ n ≥ 2,
      (erdosRogers n : ℝ) ≤ C * (n : ℝ) ^ ((2:ℝ)/3) * (Real.log n) ^ ((1:ℝ)/3)

/-- **Wolfovitz Upper Bound (2013)**

    f(n) ≪ n^{1/2} · (log n)^{120}
-/
axiom wolfovitz_upper :
    ∃ C : ℝ, C > 0 ∧ ∀ n ≥ 2,
      (erdosRogers n : ℝ) ≤ C * Real.sqrt n * (Real.log n) ^ (120 : ℝ)

/-- **Mubayi-Verstraete Upper Bound (2024)**

    f(n) ≪ n^{1/2} · log n

    This is the current best upper bound.
-/
axiom mubayi_verstraete_upper :
    ∃ C : ℝ, C > 0 ∧ ∀ n ≥ 2,
      (erdosRogers n : ℝ) ≤ C * Real.sqrt n * Real.log n

/-! ## Part VI: Current State of Knowledge -/

/-- The gap between lower and upper bounds. -/
theorem current_bounds :
    (∃ c : ℝ, c > 0 ∧ ∀ n ≥ 16,
      (erdosRogers n : ℝ) ≥ c * Real.sqrt n * Real.sqrt (Real.log n) / Real.log (Real.log n)) ∧
    (∃ C : ℝ, C > 0 ∧ ∀ n ≥ 2,
      (erdosRogers n : ℝ) ≤ C * Real.sqrt n * Real.log n) := by
  exact ⟨shearer_lower_bound, mubayi_verstraete_upper⟩

/-- The gap is roughly (log n)^{1/2} / log log n  vs  log n,
    a factor of roughly (log n)^{1/2} · log log n. -/
theorem gap_analysis (n : ℕ) (hn : n ≥ 16) :
    ∃ (c C : ℝ), c > 0 ∧ C > 0 ∧
      c * Real.sqrt n * Real.sqrt (Real.log n) / Real.log (Real.log n) ≤ erdosRogers n ∧
      (erdosRogers n : ℝ) ≤ C * Real.sqrt n * Real.log n := by
  obtain ⟨c, hc, hlower⟩ := shearer_lower_bound
  obtain ⟨C, hC, hupper⟩ := mubayi_verstraete_upper
  exact ⟨c, C, hc, hC, hlower n hn, hupper n (by omega)⟩

/-! ## Part VII: Special Cases -/

/-- For very sparse K₄-free graphs (few edges), we can find large independent sets. -/
theorem sparse_case (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hK4 : K4Free G) (hsparse : G.edgeFinset.card ≤ n) :
    ∃ S : Finset (Fin n), S.card ≥ n / 3 ∧ InducedTriangleFree G S := by
  sorry

/-- The Turán graph T(n,3) is K₄-free and has minimum triangle-free induced subgraph. -/
def turanGraph3 (n : ℕ) : SimpleGraph (Fin n) where
  Adj i j := i.val % 3 ≠ j.val % 3
  symm := by intro i j h; exact Ne.symm h
  loopless := by intro i h; exact h rfl

theorem turan_is_K4Free (n : ℕ) : K4Free (turanGraph3 n) := by
  sorry

/-! ## Part VIII: Ramsey Connection -/

/-- The Ramsey number R(3,k) is the minimum n such that every graph on n vertices
    contains either a triangle or an independent set of size k. -/
noncomputable def ramsey3k (k : ℕ) : ℕ :=
  sInf {n : ℕ | ∀ (G : SimpleGraph (Fin n)),
    HasTriangle G ∨ (∃ S : Finset (Fin n), S.card ≥ k ∧
      ∀ i j, i ∈ S → j ∈ S → i ≠ j → ¬G.Adj i j)}

/-- R(3,k) ≈ k² / log k (Kim 1995, refined by others). -/
axiom ramsey_3k_bound (k : ℕ) (hk : k ≥ 3) :
    ∃ c C : ℝ, c > 0 ∧ C > 0 ∧
      c * k^2 / Real.log k ≤ ramsey3k k ∧
      (ramsey3k k : ℝ) ≤ C * k^2 / Real.log k

/-- Connection: f(n) relates to finding independent sets in triangle-free subgraphs. -/
theorem erdos_rogers_ramsey_connection (n k : ℕ) (hn : n ≥ ramsey3k k) :
    erdosRogers n ≥ k ∨ ∀ (G : SimpleGraph (Fin n)), K4Free G → HasTriangle G := by
  sorry

/-! ## Part IX: Probabilistic Bounds -/

/-- Random K₄-free graphs give upper bounds on f(n).

    The probabilistic construction shows extremal K₄-free graphs exist
    with small maximum triangle-free induced subgraphs.
-/
axiom probabilistic_upper_bound :
    ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N,
      ∃ (G : SimpleGraph (Fin n)), K4Free G ∧
        (maxTriangleFreeInduced G : ℝ) ≤ (1 + ε) * Real.sqrt n * Real.log n

/-- Dependent random choice gives lower bounds. -/
axiom dependent_random_choice_lower :
    ∃ c : ℝ, c > 0 ∧ ∀ n ≥ 4,
      ∀ (G : SimpleGraph (Fin n)), K4Free G →
        (maxTriangleFreeInduced G : ℝ) ≥ c * Real.sqrt n

/-! ## Part X: Generalizations -/

/-- The generalized Erdős-Rogers function f_{s,t}(n):
    minimum K_t-free induced subgraph size in K_s-free graphs on n vertices. -/
noncomputable def generalizedErdosRogers (s t n : ℕ) : ℕ :=
  sInf {k : ℕ | ∀ (G : SimpleGraph (Fin n)),
    G.CliqueFree s → ∃ H : Finset (Fin n), H.card ≥ k ∧
      (inducedSubgraph G H).CliqueFree t}

/-- The original problem is f_{4,3}(n). -/
theorem original_is_f43 (n : ℕ) :
    erdosRogers n = generalizedErdosRogers 4 3 n := by
  sorry

/-- Known: f_{s,2}(n) ≈ n^{1/(s-1)} (independent sets in K_s-free graphs). -/
axiom ramsey_independent_set (s : ℕ) (hs : s ≥ 3) :
    ∃ c C : ℝ, c > 0 ∧ C > 0 ∧ ∀ n ≥ 1,
      c * (n : ℝ) ^ (1 / (s - 1 : ℝ)) ≤ generalizedErdosRogers s 2 n ∧
      (generalizedErdosRogers s 2 n : ℝ) ≤ C * (n : ℝ) ^ (1 / (s - 1 : ℝ)) * Real.log n

/-! ## Part XI: Open Status -/

/-- The exact value of f(n) remains unknown.

    The gap between √n · √(log n) / log log n and √n · log n
    represents our uncertainty about the true growth rate.
-/
def erdos_620_open : Prop :=
  ¬∃ (α : ℝ), α > 0 ∧
    (∀ ε > 0, ∃ c C : ℝ, c > 0 ∧ C > 0 ∧ ∀ n ≥ 2,
      c * (n : ℝ) ^ α ≤ erdosRogers n ∧
      (erdosRogers n : ℝ) ≤ C * (n : ℝ) ^ α)

theorem erdos_620_unsolved : erdos_620_open := by
  sorry -- The problem remains open

end Erdos620

/-!
## Summary

This file formalizes Erdős Problem #620, the Erdős-Rogers problem.

**The Problem**: In any K₄-free graph on n vertices, how large a
triangle-free induced subgraph must exist?

**Status**: OPEN - bounds known but exact answer unknown.

**Current Bounds**:
- Lower: f(n) ≫ √n · √(log n) / log log n  (Shearer)
- Upper: f(n) ≪ √n · log n  (Mubayi-Verstraete 2024)

**What We Formalize**:
1. Triangles, K₄, and forbidden subgraphs
2. Induced subgraphs and the triangle-free property
3. The Erdős-Rogers function f(n)
4. All historical upper bounds (Bollobás-Hind, Krivelevich, Wolfovitz, Mubayi-Verstraete)
5. Lower bounds via Ramsey theory
6. Connection to Ramsey numbers R(3,k)
7. Probabilistic methods for bounds
8. Generalization f_{s,t}(n)

**Key Insight**: The gap of roughly (log n)^{1/2} · log log n between
upper and lower bounds represents fundamental uncertainty about the
structure of extremal K₄-free graphs.

**Open Questions**:
- Is the truth closer to √n · log n or √n · √(log n)?
- What is the structure of extremal graphs?
- Can probabilistic constructions be derandomized?
-/
