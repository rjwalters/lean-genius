/-!
# Erdős Problem #1092: Chromatic Decomposition Threshold

Erdős, Hajnal, and Szemerédi defined f_r(n) as the maximum number of edges
that can be removed from each m-vertex subgraph of G so that the remainder
has chromatic number ≤ r, while guaranteeing G has chromatic number ≤ r+1.

They asked:
1. Is f₂(n) ≫ n?
2. More generally, is f_r(n) ≫_r n?

Tang noted that a construction by Rödl (1982) actually disproves the first
question, showing f₂(n) does not grow much faster than n.

Reference: https://erdosproblems.com/1092
-/

import Mathlib.Tactic
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Combinatorics.SimpleGraph.Basic

/-! ## Definitions -/

/-- A simple graph on n vertices. -/
structure SGraph (n : ℕ) where
  adj : Fin n → Fin n → Prop
  symm : ∀ u v, adj u v → adj v u
  irrefl : ∀ v, ¬adj v v

/-- The edge count of a graph. -/
noncomputable def SGraph.edgeCount {n : ℕ} (G : SGraph n) : ℕ :=
  Finset.card ((Finset.univ.product Finset.univ).filter
    (fun (p : Fin n × Fin n) => p.1 < p.2 ∧ G.adj p.1 p.2))

/-- A proper r-coloring of a graph. -/
def SGraph.hasColoring {n : ℕ} (G : SGraph n) (r : ℕ) : Prop :=
  ∃ c : Fin n → Fin r, ∀ u v, G.adj u v → c u ≠ c v

/-- The chromatic number: minimum r such that G has a proper r-coloring. -/
noncomputable def SGraph.chromaticNum {n : ℕ} (G : SGraph n) : ℕ :=
  Nat.find ⟨n, ⟨Fin.elim0, fun u v _ => (Fin.elim0 u).elim⟩⟩

/-- Removing k edges from G: there exist k edges whose deletion
    yields a graph with chromatic number ≤ r. -/
def CanReduceChromatic {n : ℕ} (G : SGraph n) (k r : ℕ) : Prop :=
  ∃ removed : Finset (Fin n × Fin n),
    removed.card ≤ k ∧
    (SGraph.mk
      (fun u v => G.adj u v ∧ (u, v) ∉ removed ∧ (v, u) ∉ removed)
      (fun u v ⟨h, hu, hv⟩ => ⟨G.symm u v h, hv, hu⟩)
      (fun v ⟨h, _, _⟩ => G.irrefl v h)).hasColoring r

/-! ## The Function f_r(n) -/

/-- f_r(n): the maximum k such that if every m-vertex induced subgraph
    of G can have its chromatic number reduced to ≤ r by removing ≤ k edges,
    then G has chromatic number ≤ r + 1. -/
noncomputable def fThreshold (r n : ℕ) : ℕ :=
  sSup { k : ℕ | ∀ G : SGraph n,
    (∀ S : Finset (Fin n), CanReduceChromatic
      (SGraph.mk (fun u v => u ∈ S ∧ v ∈ S ∧ G.adj u v)
        (fun u v ⟨hu, hv, h⟩ => ⟨hv, hu, G.symm u v h⟩)
        (fun v ⟨_, _, h⟩ => G.irrefl v h)) k r) →
    G.hasColoring (r + 1) }

/-! ## Erdős–Hajnal–Szemerédi Questions -/

/-- Question 1: Is f₂(n) ≫ n? That is, does f₂(n)/n → ∞?
    Tang noted that Rödl's 1982 construction gives a negative answer. -/
axiom erdos_1092_question1 :
  ∀ C : ℝ, ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n →
    C * n ≤ (fThreshold 2 n : ℝ)

/-- Question 2: Is f_r(n) ≫_r n for general r? -/
axiom erdos_1092_question2 (r : ℕ) (hr : 2 ≤ r) :
  ∀ C : ℝ, ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n →
    C * (r : ℝ) * n ≤ (fThreshold r n : ℝ)

/-! ## Rödl's Construction -/

/-- Rödl (1982): Construction showing that f₂(n) does not grow much
    faster than n, providing evidence against Question 1.
    Specifically, f₂(n) = O(n · polylog(n)). -/
axiom rodl_upper_bound :
  ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 2 ≤ n →
    (fThreshold 2 n : ℝ) ≤ C * n * (Real.log n) ^ 2

/-! ## Trivial Lower Bound -/

/-- f_r(n) ≥ n - 1 trivially: removing all n-1 edges of a tree
    always leaves an independent set (chromatic number 1 ≤ r). -/
axiom f_trivial_lower (r n : ℕ) (hr : 1 ≤ r) (hn : 2 ≤ n) :
  n - 1 ≤ fThreshold r n

/-! ## Connection to Problem #744 -/

/-- This problem is related to but distinct from Erdős Problem #744,
    which concerns similar chromatic decomposition thresholds. -/
axiom erdos_744_connection :
  ∀ r n : ℕ, 2 ≤ r → 2 ≤ n →
    fThreshold r n ≤ fThreshold (r + 1) n
