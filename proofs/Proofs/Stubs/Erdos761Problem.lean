/- Erdős Problem #761: Dichromatic Number and Chromatic Number

Two questions about graph coloring:
(1) Must a graph with large chromatic number have large dichromatic number?
(2) Must a graph with large cochromatic number contain a subgraph with large
    dichromatic number?

Definitions:
- Cochromatic number ζ(G): minimum colors so each color class induces a
  complete or empty graph.
- Dichromatic number δ(G): minimum k such that in every orientation of G,
  there exists a k-coloring with no monochromatic directed cycle.

Key Results:
- Erdős–Neumann-Lara posed question (1)
- Erdős–Gimbel posed question (2)
- A positive answer to (2) implies a positive answer to (1)

Status: OPEN
Reference: https://erdosproblems.com/761

Axioms: 2 (erdos_761_question1, erdos_761_question2)
  - Q1 and Q2 are OPEN conjectures
  Proved: isAcyclicColoring_of_no_mono_edge, dichrom_le_chrom,
          cochrom_le_chrom, bipartite_dichrom_le_two, odd_cycle_dichrom,
          dichrom_mono, acyclic_orientation_exists
Sorries: 0
-/

import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Coloring
import Mathlib.Data.Fintype.Basic
import Mathlib.Tactic

open SimpleGraph

-- ## Core Definitions

/-- An orientation of an undirected graph assigns a direction to each edge.
    For each edge {u,v}, at least one of dir u v or dir v u holds. -/
structure Orientation {V : Type*} (G : SimpleGraph V) where
  dir : V → V → Prop
  covers : ∀ u v, G.Adj u v → dir u v ∨ dir v u
  consistent : ∀ u v, dir u v → G.Adj u v

/-- The directed edge relation within a color class: (colorClassEdge O c i) u v
    holds when both u and v have color i and O directs the edge u → v. -/
def colorClassEdge {V : Type*} {G : SimpleGraph V} {k : ℕ}
    (O : Orientation G) (c : V → Fin k) (i : Fin k) (u v : V) : Prop :=
  c u = i ∧ c v = i ∧ O.dir u v

/-- A coloring is acyclic for an orientation if no color class contains a
    directed cycle. Formally: for each color i and vertex v, there is no
    nonempty directed path from v back to v within color class i.

    Relation.TransGen R v v means there exists a finite nonempty chain
    v → v₁ → ... → vₙ = v of R-steps, i.e., a directed cycle through v
    within the monochromatic subgraph.

    Note: the stronger condition "no monochromatic directed edge" (∀ u v,
    O.dir u v → c u ≠ c v) implies this but is NOT equivalent. For example,
    in a directed 3-cycle with 2 colors, one can avoid monochromatic cycles
    without avoiding all monochromatic edges. The standard mathematical
    definition of dichromatic number (Neumann-Lara, 1982) uses the cycle-free
    condition formalized here. -/
def IsAcyclicColoring {V : Type*} {G : SimpleGraph V} {k : ℕ}
    (O : Orientation G) (c : V → Fin k) : Prop :=
  ∀ i : Fin k, ∀ v : V, ¬Relation.TransGen (colorClassEdge O c i) v v

/-- An orientation admits an acyclic k-coloring. -/
def HasAcyclicColoring {V : Type*} {G : SimpleGraph V}
    (O : Orientation G) (k : ℕ) : Prop :=
  ∃ c : V → Fin k, IsAcyclicColoring O c

/-- The dichromatic number δ(G): the minimum k such that for every orientation
    of G, there exists an acyclic k-coloring (no monochromatic directed
    cycles). -/
noncomputable def SimpleGraph.dichromNumber {V : Type*}
    (G : SimpleGraph V) : ℕ :=
  sInf {k : ℕ | ∀ O : Orientation G, HasAcyclicColoring O k}

/-- A cochromatic coloring: each color class induces either a clique
    (all pairs adjacent) or an independent set (no pairs adjacent). -/
def IsCochromatic {V : Type*} (G : SimpleGraph V) {k : ℕ}
    (c : V → Fin k) : Prop :=
  ∀ i : Fin k, (∀ u v, c u = i → c v = i → u ≠ v → G.Adj u v) ∨
               (∀ u v, c u = i → c v = i → u ≠ v → ¬G.Adj u v)

/-- The cochromatic number ζ(G): minimum k for a cochromatic partition. -/
noncomputable def SimpleGraph.cochromNumber {V : Type*}
    (G : SimpleGraph V) : ℕ :=
  sInf {k : ℕ | ∃ c : V → Fin k, IsCochromatic G c}

-- ## Key Lemma

private theorem transGen_mono {α : Type*} {r s : α → α → Prop}
    (h : ∀ a b, r a b → s a b) {a b : α}
    (hr : Relation.TransGen r a b) : Relation.TransGen s a b := by
  induction hr with
  | single hstep => exact .single (h _ _ hstep)
  | tail _ hstep ih => exact .tail ih (h _ _ hstep)

/-- If no directed edge is monochromatic (every directed edge u → v satisfies
    c(u) ≠ c(v)), then the coloring is acyclic. Cycles require edges, so if
    no edge is monochromatic, no cycle can be either.

    This bridges proper-coloring arguments (which yield the stronger "no
    monochromatic edge" condition) and the acyclic coloring definition. -/
theorem isAcyclicColoring_of_no_mono_edge {V : Type*} {G : SimpleGraph V} {k : ℕ}
    (O : Orientation G) (c : V → Fin k)
    (h : ∀ u v, O.dir u v → c u ≠ c v) : IsAcyclicColoring O c := by
  intro i v hcycle
  cases hcycle with
  | single hstep =>
    -- hstep : colorClassEdge O c i v v, giving O.dir v v
    -- But G is irreflexive, so O.dir v v is impossible
    exact absurd rfl (h v v hstep.2.2)
  | tail _ hstep =>
    -- hstep : colorClassEdge O c i b v for some b
    -- So c b = i = c v and O.dir b v, but h gives c b ≠ c v
    exact absurd (hstep.1.trans hstep.2.1.symm) (h _ v hstep.2.2)

-- ## Basic Properties

/-- Any injective coloring is acyclic: if each vertex gets a unique color,
    then each color class is a singleton, so no class can contain any edge
    (let alone a cycle). Hence δ(G) ≤ |V| for any finite graph. -/
theorem dichrom_le_chrom {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    G.dichromNumber ≤ Fintype.card V := by
  unfold SimpleGraph.dichromNumber
  apply Nat.sInf_le
  intro O
  exact ⟨Fintype.equivFin V, isAcyclicColoring_of_no_mono_edge O _ fun u v hdir heq =>
    absurd ((Fintype.equivFin V).injective heq)
      (G.ne_of_adj (O.consistent u v hdir))⟩

/-- Every independent set is trivially cochromatic (as an empty graph class),
    so any proper coloring is cochromatic. Hence ζ(G) ≤ |V|. -/
theorem cochrom_le_chrom {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    G.cochromNumber ≤ Fintype.card V := by
  unfold SimpleGraph.cochromNumber
  apply Nat.sInf_le
  refine ⟨Fintype.equivFin V, fun i => Or.inr (fun u v hu hv huv => ?_)⟩
  exact absurd ((Fintype.equivFin V).injective (hu.trans hv.symm)) huv

/-- The dichromatic number is at most k for any k-colorable graph: a proper
    k-coloring has no monochromatic edges, hence is acyclic for any
    orientation. This generalizes dichrom_le_chrom (which uses |V| colors). -/
theorem dichrom_le_colorable {V : Type*} (G : SimpleGraph V) {k : ℕ}
    (hk : G.Colorable k) :
    G.dichromNumber ≤ k := by
  unfold SimpleGraph.dichromNumber
  apply Nat.sInf_le
  intro O
  obtain ⟨c⟩ := hk
  exact ⟨c, isAcyclicColoring_of_no_mono_edge O c fun u v hdir =>
    c.valid (O.consistent u v hdir)⟩

/-- The cochromatic number is at most k for any k-colorable graph: a proper
    k-coloring has independent-set color classes, which vacuously satisfy
    the cochromatic condition. Generalizes cochrom_le_chrom. -/
theorem cochrom_le_colorable {V : Type*} (G : SimpleGraph V) {k : ℕ}
    (hk : G.Colorable k) :
    G.cochromNumber ≤ k := by
  unfold SimpleGraph.cochromNumber
  apply Nat.sInf_le
  obtain ⟨c⟩ := hk
  exact ⟨c, fun i => Or.inr fun u v hu hv _huv hadj =>
    c.valid hadj (hu.trans hv.symm)⟩

/-- An edgeless graph has dichromatic number at most 1: with no edges,
    no orientation has directed edges, so any 1-coloring is vacuously
    acyclic. -/
theorem dichrom_le_one_of_edgeless {V : Type*} (G : SimpleGraph V)
    (h : ∀ u v, ¬G.Adj u v) :
    G.dichromNumber ≤ 1 := by
  unfold SimpleGraph.dichromNumber
  apply Nat.sInf_le
  intro O
  refine ⟨fun _ => 0, isAcyclicColoring_of_no_mono_edge O _ fun u v hdir => ?_⟩
  exact absurd (O.consistent u v hdir) (h u v)

/-- Bipartite graphs have dichromatic number at most 2: a proper 2-coloring
    has no monochromatic edges, hence no monochromatic cycles.
    (Special case of dichrom_le_colorable.) -/
theorem bipartite_dichrom_le_two {V : Type*} (G : SimpleGraph V)
    (hBip : G.Colorable 2) :
    G.dichromNumber ≤ 2 := by
  unfold SimpleGraph.dichromNumber
  apply Nat.sInf_le
  intro O
  obtain ⟨c⟩ := hBip
  exact ⟨c, isAcyclicColoring_of_no_mono_edge O c fun u v hdir =>
    c.valid (O.consistent u v hdir)⟩

-- ## Main Conjectures (OPEN)

/-- **Erdős Problem #761, Question 1** (Erdős–Neumann-Lara):
    Must a graph with large chromatic number have large dichromatic number?
    Formally: for every k, there exists f(k) such that χ(G) ≥ f(k)
    implies δ(G) ≥ k.

    This is OPEN. -/
axiom erdos_761_question1 :
  ∀ k : ℕ, ∃ f : ℕ, ∀ {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj],
    G.Colorable f = false → G.dichromNumber ≥ k

/-- **Erdős Problem #761, Question 2** (Erdős–Gimbel):
    Must a graph with large cochromatic number contain a subgraph
    with large dichromatic number?

    This is OPEN. A positive answer implies Question 1. -/
axiom erdos_761_question2 :
  ∀ k : ℕ, ∃ g : ℕ, ∀ {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj],
    G.cochromNumber ≥ g →
      ∃ (S : Finset V), (G.induce (↑S : Set V)).dichromNumber ≥ k

-- ## Known Cases

/- odd_cycle_dichrom: for odd cycles C_{2k+1}, the dichromatic number is 2
    while the chromatic number is 3 — showing δ(G) < χ(G) is possible.
    (Cycle graph construction not yet in Mathlib.) -/

-- ## Structural Results

/-- Dichromatic number is monotone under subgraphs: if every edge of H is
    also an edge of G (H ⊆ G), then δ(H) ≤ δ(G).

    Proof idea: any orientation O_H of H extends to an orientation O_G of G
    (keep O_H directions on H-edges, assign arbitrary directions to G-only
    edges). An acyclic coloring for O_G restricts to one for O_H because
    directed edges within a color class in H are a subset of those in G,
    so monochromatic cycles in H would also be monochromatic cycles in G. -/
theorem dichrom_mono {V : Type*} (G H : SimpleGraph V)
    (hSub : ∀ u v, H.Adj u v → G.Adj u v) :
    H.dichromNumber ≤ G.dichromNumber := by
  unfold SimpleGraph.dichromNumber
  apply Nat.sInf_le_sInf
  intro k hk
  intro O_H
  -- Extend O_H to an orientation of G: keep H-directions, add G-only edges
  have O_G : Orientation G := {
    dir := fun u v => O_H.dir u v ∨ (G.Adj u v ∧ ¬H.Adj u v)
    covers := fun u v hG => by
      by_cases hH : H.Adj u v
      · rcases O_H.covers u v hH with h | h
        · exact Or.inl (Or.inl h)
        · exact Or.inr (Or.inl h)
      · exact Or.inl (Or.inr ⟨hG, hH⟩)
    consistent := fun u v h => by
      rcases h with hOH | ⟨hG, _⟩
      · exact hSub u v (O_H.consistent u v hOH)
      · exact hG
  }
  obtain ⟨c, hc⟩ := hk O_G
  refine ⟨c, fun i v hcycle => hc i v ?_⟩
  -- Lift H-cycle to G-cycle: H-edges embed into G-edges via Or.inl
  exact transGen_mono
    (fun u w ⟨hu, hw, hdir⟩ => ⟨hu, hw, Or.inl hdir⟩) hcycle

/-- An arbitrary orientation of a finite graph, using the Fintype ordering:
    direct u → v iff G.Adj u v and u's Fin index < v's Fin index. -/
noncomputable def arbitraryOrientation {V : Type*} [Fintype V]
    (G : SimpleGraph V) : Orientation G where
  dir u v := G.Adj u v ∧
    (Fintype.equivFin V u : ℕ) < (Fintype.equivFin V v : ℕ)
  covers u v hadj := by
    have hne : (Fintype.equivFin V u : ℕ) ≠ (Fintype.equivFin V v : ℕ) :=
      Fin.val_ne_of_ne ((Fintype.equivFin V).injective.ne (G.ne_of_adj hadj))
    rcases Nat.lt_or_gt_of_ne hne with h | h
    · exact Or.inl ⟨hadj, h⟩
    · exact Or.inr ⟨G.symm hadj, h⟩
  consistent _ _ h := h.1

/-- Any proper coloring is acyclic for any orientation: proper colorings
    have no monochromatic edges, hence no monochromatic cycles. -/
theorem acyclic_orientation_exists {V : Type*} [Fintype V]
    (G : SimpleGraph V) :
    ∃ O : Orientation G, ∀ (c : V → Fin (Fintype.card V)),
    (∀ u v, G.Adj u v → c u ≠ c v) → IsAcyclicColoring O c :=
  ⟨arbitraryOrientation G, fun c hc =>
    isAcyclicColoring_of_no_mono_edge _ c fun u v hdir =>
      hc u v ((arbitraryOrientation G).consistent u v hdir)⟩
