/-!
# Erdős Problem #568: Ramsey Size Linearity from Tree and Clique Bounds

A graph G is Ramsey size linear if R̂(G, H) ≪ m for every graph H
with m edges and no isolated vertices, where R̂ denotes the size Ramsey number.

Question: If R(G, Tₙ) ≪ n for all trees Tₙ on n vertices and
R(G, Kₙ) ≪ n² for all complete graphs Kₙ, must G be Ramsey size linear?

Known:
- R̂(G, H) ≤ R(G, H) · |V(H)| gives crude bounds
- EFRS (1993) posed this question
- Connected to problems #567 (Q₃, K₃,₃, H₅ size linearity)

Status: OPEN.

Reference: https://erdosproblems.com/568
-/

import Mathlib.Tactic
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Real.Basic

/-! ## Definitions -/

/-- A simple graph on n vertices. -/
structure SGraph (n : ℕ) where
  adj : Fin n → Fin n → Prop
  symm : ∀ i j, adj i j → adj j i
  irrefl : ∀ i, ¬adj i i

/-- The number of edges in a graph. -/
noncomputable def numEdges {n : ℕ} (G : SGraph n) : ℕ :=
  Finset.card (Finset.filter (fun p : Fin n × Fin n => p.1 < p.2 ∧ G.adj p.1 p.2)
    (Finset.univ.product Finset.univ))

/-- G has no isolated vertices (every vertex has at least one neighbor). -/
def NoIsolated {n : ℕ} (G : SGraph n) : Prop :=
  ∀ v : Fin n, ∃ w : Fin n, G.adj v w

/-- The Ramsey number R(G, H): smallest N such that every red-blue coloring
    of K_N contains a red copy of G or a blue copy of H.
    Axiomatized. -/
axiom ramseyNumber (nG nH : ℕ) (G : SGraph nG) (H : SGraph nH) : ℕ

/-- The size Ramsey number R̂(G, H): smallest m such that there exists
    a graph F with m edges where every red-blue coloring of E(F)
    contains a red copy of G or a blue copy of H.
    Axiomatized. -/
axiom sizeRamseyNumber (nG nH : ℕ) (G : SGraph nG) (H : SGraph nH) : ℕ

/-- A tree on n vertices (connected acyclic graph). -/
def IsTree {n : ℕ} (T : SGraph n) : Prop :=
  numEdges T = n - 1 ∧ n ≥ 1  -- simplified characterization

/-- A graph is a complete graph if all distinct vertices are adjacent. -/
def IsComplete {n : ℕ} (G : SGraph n) : Prop :=
  ∀ i j : Fin n, i ≠ j → G.adj i j

/-! ## Tree and Clique Ramsey Conditions -/

/-- G has linear Ramsey number against all trees: R(G, Tₙ) ≤ C·n. -/
def LinearTreeRamsey {nG : ℕ} (G : SGraph nG) : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ (nH : ℕ) (T : SGraph nH), IsTree T →
    (ramseyNumber nG nH G T : ℝ) ≤ C * nH

/-- G has quadratic Ramsey number against all complete graphs: R(G, Kₙ) ≤ C·n². -/
def QuadraticCliqueRamsey {nG : ℕ} (G : SGraph nG) : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ (nH : ℕ) (K : SGraph nH), IsComplete K →
    (ramseyNumber nG nH G K : ℝ) ≤ C * nH ^ 2

/-! ## Size Linearity -/

/-- G is Ramsey size linear: R̂(G, H) ≤ C·m for all H with m edges,
    no isolated vertices. -/
def IsRamseySizeLinear {nG : ℕ} (G : SGraph nG) : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ (nH : ℕ) (H : SGraph nH),
    NoIsolated H → (sizeRamseyNumber nG nH G H : ℝ) ≤ C * numEdges H

/-! ## The Conjecture -/

/-- Erdős Problem #568 (EFRS 1993): If G has R(G, Tₙ) ≪ n for all trees
    and R(G, Kₙ) ≪ n² for all complete graphs, then G is Ramsey size linear. -/
axiom erdos_568_conjecture {nG : ℕ} (G : SGraph nG)
    (hTree : LinearTreeRamsey G)
    (hClique : QuadraticCliqueRamsey G) :
  IsRamseySizeLinear G
