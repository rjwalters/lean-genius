/-!
# Erdős Problem #1068 — Countable Infinitely-Connected Subgraphs

Does every graph with chromatic number ℵ₁ contain a countable subgraph
which is infinitely vertex-connected?

A graph is infinitely (vertex) connected if any two vertices are
connected by infinitely many pairwise internally-disjoint paths.

Known:
- Soukup (2015): constructed a graph with uncountable chromatic number
  where every uncountable set is only finitely vertex-connected
- Simplified construction by Bowler–Pikhurko (2024)

Status: OPEN
Reference: https://erdosproblems.com/1068
Source: [Va99, 7.90], [ErHa66]
-/

import Mathlib.Data.Nat.Basic
import Mathlib.Data.Set.Basic
import Mathlib.Order.Cardinal.Basic
import Mathlib.Tactic

/-! ## Definitions -/

/-- A graph (abstractly: adjacency on vertex type V). -/
structure InfGraph (V : Type*) where
  adj : V → V → Prop
  symm : ∀ u v, adj u v → adj v u
  irrefl : ∀ v, ¬adj v v

/-- A path from u to v in a graph. -/
structure GraphPath {V : Type*} (G : InfGraph V) (u v : V) where
  vertices : List V
  starts_at : vertices.head? = some u
  ends_at : vertices.getLast? = some v

/-- Two paths are internally disjoint if they share no internal vertices. -/
def AreInternallyDisjoint {V : Type*} {G : InfGraph V} {u v : V}
  (p q : GraphPath G u v) : Prop :=
  ∀ w : V, w ≠ u → w ≠ v → ¬(w ∈ p.vertices ∧ w ∈ q.vertices)

/-- A graph is infinitely vertex-connected: any two vertices are
    connected by infinitely many pairwise internally-disjoint paths. -/
def IsInfConnected {V : Type*} (G : InfGraph V) : Prop :=
  ∀ u v : V, u ≠ v →
    ∃ P : Set (GraphPath G u v), P.Infinite ∧
      P.Pairwise (fun p q => AreInternallyDisjoint p q)

/-- The chromatic number of a graph is at least κ. -/
def ChromaticAtLeast {V : Type*} (G : InfGraph V) (κ : Cardinal) : Prop :=
  ∀ (k : Cardinal), k < κ →
    ¬∃ (c : V → Ordinal), (∀ u v, G.adj u v → c u ≠ c v) ∧
      Cardinal.mk (Set.range c) ≤ k

/-! ## Main Question -/

/-- **Erdős Problem #1068**: Does every graph with chromatic number ℵ₁
    contain a countable infinitely-connected subgraph? -/
axiom erdos_1068_countable_inf_connected :
  ∀ (V : Type) (G : InfGraph V),
    ChromaticAtLeast G Cardinal.aleph0.succ →
    ∃ (S : Set V), S.Countable ∧
      IsInfConnected ⟨fun u v => G.adj u v ∧ u ∈ S ∧ v ∈ S,
        fun u v h => ⟨G.symm u v h.1, h.2.2, h.2.1⟩,
        fun v h => G.irrefl v h.1⟩

/-! ## Known Results -/

/-- **Soukup (2015)**: There exists a graph with uncountable chromatic
    number where every uncountable vertex set is only finitely
    vertex-connected. This shows the question is subtle — it
    specifically asks about countable subgraphs. -/
axiom soukup_counterexample :
  ∃ (V : Type) (G : InfGraph V),
    ChromaticAtLeast G Cardinal.aleph0.succ ∧
    ∃ S : Set V, ¬S.Countable ∧ ¬IsInfConnected
      ⟨fun u v => G.adj u v ∧ u ∈ S ∧ v ∈ S,
        fun u v h => ⟨G.symm u v h.1, h.2.2, h.2.1⟩,
        fun v h => G.irrefl v h.1⟩

/-- **Bowler–Pikhurko (2024)**: Simplified Soukup's construction
    and described the problem as a version of the Erdős–Hajnal problem. -/
axiom bowler_pikhurko_simplified : True

/-! ## Observations -/

/-- **Erdős–Hajnal connection (Problem #1067)**: The question is a
    variant of the Erdős–Hajnal problem about chromatic number and
    graph structure. The original asks about uncountable chromatic
    number forcing certain substructures. -/
axiom erdos_hajnal_connection : True

/-- **Infinite connectivity strength**: Infinite vertex-connectivity
    is a strong requirement — it implies the graph has no finite
    vertex cut separating any two vertices. -/
axiom inf_connectivity_strength : True

/-- **Set-theoretic aspects**: The answer may depend on set-theoretic
    axioms beyond ZFC, as is common for problems involving
    uncountable chromatic numbers. -/
axiom set_theory_aspects : True
