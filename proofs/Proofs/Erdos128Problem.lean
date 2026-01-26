/-!
# Erdős Problem #128: Triangle-Free Graphs with Dense Subgraphs

Erdős Problem #128 asks: if every induced subgraph of G on ≥ ⌊n/2⌋ vertices
has more than n²/50 edges, must G contain a triangle?

The constant 1/50 is conjectured to be best possible, as shown by blow-ups
of C₅ or the Petersen graph (which are triangle-free with edge density 1/5
in large subgraphs, and 1/5 > 1/50).

Known partial results:
- EFRS: holds with 50 replaced by 16
- Krivelevich: holds with n/2 → 3n/5 (and 50 → 25)
- Norin–Yepremyan: holds for graphs with ≥ (1/5 - c)n² edges
- Razborov: holds with 1/50 replaced by 27/1024

Reward: $250. Reference: https://erdosproblems.com/128
-/

import Mathlib.Tactic
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Combinatorics.SimpleGraph.Basic

/-! ## Definitions -/

/-- A simple graph on n vertices. -/
structure Graph (n : ℕ) where
  adj : Fin n → Fin n → Prop
  symm : ∀ u v, adj u v → adj v u
  irrefl : ∀ v, ¬adj v v

/-- The number of edges in a graph. -/
noncomputable def Graph.edgeCount {n : ℕ} (G : Graph n) : ℕ :=
  Finset.card ((Finset.univ.product Finset.univ).filter
    (fun (p : Fin n × Fin n) => p.1 < p.2 ∧ G.adj p.1 p.2))

/-- The induced subgraph on a subset S of vertices. -/
def Graph.induce {n : ℕ} (G : Graph n) (S : Finset (Fin n)) : Graph n where
  adj u v := u ∈ S ∧ v ∈ S ∧ G.adj u v
  symm u v h := ⟨h.2.1, h.1, G.symm u v h.2.2⟩
  irrefl v h := G.irrefl v h.2.2

/-- G contains a triangle: three mutually adjacent vertices. -/
def Graph.hasTriangle {n : ℕ} (G : Graph n) : Prop :=
  ∃ u v w : Fin n, u ≠ v ∧ v ≠ w ∧ u ≠ w ∧
    G.adj u v ∧ G.adj v w ∧ G.adj u w

/-- G is triangle-free. -/
def Graph.triangleFree {n : ℕ} (G : Graph n) : Prop :=
  ¬G.hasTriangle

/-- Every induced subgraph on ≥ ⌊n/2⌋ vertices has more than n²/50 edges. -/
def Graph.denseSubgraphs {n : ℕ} (G : Graph n) : Prop :=
  ∀ S : Finset (Fin n), n / 2 ≤ S.card →
    n ^ 2 / 50 < (G.induce S).edgeCount

/-! ## Extremal Examples -/

/-- The blow-up of C₅ (Möbius–Kantor type): partition n vertices into 5 parts
    of size ~n/5, connect parts i and i+1 (mod 5). This is triangle-free
    with edge density approaching 2/5 · (1/5)² · n² in large subgraphs. -/
axiom c5_blowup_triangle_free (n : ℕ) (hn : 10 ≤ n) :
  ∃ G : Graph n, G.triangleFree ∧
    ∀ S : Finset (Fin n), n / 2 ≤ S.card →
      (G.induce S).edgeCount ≤ n ^ 2 / 50 + n

/-! ## Partial Results -/

/-- EFRS (Erdős–Faudree–Rousseau–Schelp): the result holds with
    50 replaced by 16. If every subgraph on ≥ n/2 vertices has > n²/16 edges,
    then G contains a triangle. -/
axiom efrs_theorem (n : ℕ) (G : Graph n) :
  (∀ S : Finset (Fin n), n / 2 ≤ S.card →
    n ^ 2 / 16 < (G.induce S).edgeCount) →
  G.hasTriangle

/-- Krivelevich: the result holds with n/2 replaced by 3n/5 and 50 by 25.
    If every subgraph on ≥ 3n/5 vertices has > n²/25 edges, then triangle. -/
axiom krivelevich_theorem (n : ℕ) (G : Graph n) :
  (∀ S : Finset (Fin n), 3 * n / 5 ≤ S.card →
    n ^ 2 / 25 < (G.induce S).edgeCount) →
  G.hasTriangle

/-- Razborov: holds with 1/50 replaced by 27/1024 ≈ 0.0264.
    Uses flag algebra methods. -/
axiom razborov_theorem (n : ℕ) (G : Graph n) :
  (∀ S : Finset (Fin n), n / 2 ≤ S.card →
    27 * n ^ 2 / 1024 < (G.induce S).edgeCount) →
  G.hasTriangle

/-- Norin–Yepremyan: holds for graphs with at least (1/5 - c)n² edges
    for some small constant c > 0. -/
axiom norin_yepremyan_theorem :
  ∃ c : ℝ, 0 < c ∧ ∀ n : ℕ, ∀ G : Graph n,
    (1 / 5 - c) * (n : ℝ) ^ 2 ≤ (G.edgeCount : ℝ) →
    G.denseSubgraphs → G.hasTriangle

/-! ## Main Conjecture -/

/-- Erdős Problem #128: If every induced subgraph on ≥ ⌊n/2⌋ vertices
    has more than n²/50 edges, then G contains a triangle. ($250 prize) -/
axiom erdos_128_conjecture (n : ℕ) (G : Graph n) :
  G.denseSubgraphs → G.hasTriangle
