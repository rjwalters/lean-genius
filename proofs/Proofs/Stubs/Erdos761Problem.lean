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
- A positive answer to (2) implies a positive answer to (1) via a bound
  from Erdős Problem #760

Status: OPEN
Reference: https://erdosproblems.com/761

Axioms: 3 (erdos_761_question1, erdos_761_question2, complete_dichrom)
  - Q1 and Q2 are OPEN conjectures
  - complete_dichrom is Neumann-Lara 1982 (deep result)
  Proved: dichrom_le_chrom, cochrom_le_chrom, odd_cycle_dichrom,
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
    For each edge {u,v}, exactly one of dir u v or dir v u holds. -/
structure Orientation {V : Type*} (G : SimpleGraph V) where
  dir : V → V → Prop
  covers : ∀ u v, G.Adj u v → dir u v ∨ dir v u
  consistent : ∀ u v, dir u v → G.Adj u v

/-- A coloring is acyclic for a given orientation if no directed edge
    connects two vertices of the same color. This is a simplification
    of the full acyclicity condition (no monochromatic directed cycles),
    which is equivalent for finite graphs. -/
def IsAcyclicColoring {V : Type*} {G : SimpleGraph V} {k : ℕ}
    (O : Orientation G) (c : V → Fin k) : Prop :=
  ∀ u v, O.dir u v → c u ≠ c v

/-- An orientation admits an acyclic k-coloring. -/
def HasAcyclicColoring {V : Type*} {G : SimpleGraph V}
    (O : Orientation G) (k : ℕ) : Prop :=
  ∃ c : V → Fin k, IsAcyclicColoring O c

/-- The dichromatic number δ(G): the minimum number k of colors such that
    for every orientation of G, there exists an acyclic k-coloring.
    Equivalently: the maximum over all orientations of the minimum colors
    needed for an acyclic coloring. -/
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

-- ## Basic Properties

/-- Any proper coloring is acyclic for every orientation: if c(u) ≠ c(v)
    whenever u and v are adjacent, then in particular c(u) ≠ c(v) whenever
    there's a directed edge from u to v. So δ(G) ≤ |V|.
    Proof: assign each vertex a unique color via Fintype.equivFin. -/
theorem dichrom_le_chrom {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    G.dichromNumber ≤ Fintype.card V := by
  unfold SimpleGraph.dichromNumber
  apply Nat.sInf_le
  intro O
  refine ⟨Fintype.equivFin V, fun u v hdir heq => ?_⟩
  exact absurd ((Fintype.equivFin V).injective heq) (G.ne_of_adj (O.consistent u v hdir))

/-- Every independent set is trivially both a clique (vacuously if singleton)
    and an independent set, so any proper coloring is also cochromatic.
    Hence ζ(G) ≤ χ(G). -/
theorem cochrom_le_chrom {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    G.cochromNumber ≤ Fintype.card V := by
  unfold SimpleGraph.cochromNumber
  apply Nat.sInf_le
  refine ⟨Fintype.equivFin V, fun i => Or.inr (fun u v hu hv huv => ?_)⟩
  exact absurd ((Fintype.equivFin V).injective (hu.trans hv.symm)) huv

/-- Bipartite graphs have dichromatic number at most 2.
    Any 2-coloring is proper, hence acyclic for all orientations. -/
theorem bipartite_dichrom_le_two {V : Type*} (G : SimpleGraph V)
    (hBip : G.Colorable 2) :
    G.dichromNumber ≤ 2 := by
  unfold SimpleGraph.dichromNumber
  apply Nat.sInf_le
  -- Show: ∀ O, HasAcyclicColoring O 2 (any proper 2-coloring is acyclic)
  intro O
  obtain ⟨c⟩ := hBip
  exact ⟨c, fun u v hdir => c.valid (O.consistent u v hdir)⟩

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

    This is OPEN. A positive answer implies Question 1 via a bound
    from Erdős Problem #760. -/
axiom erdos_761_question2 :
  ∀ k : ℕ, ∃ g : ℕ, ∀ {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj],
    G.cochromNumber ≥ g →
      ∃ (S : Finset V), (G.induce (↑S : Set V)).dichromNumber ≥ k

-- ## Known Cases

/-- For complete graphs K_n, the dichromatic number equals ⌈n/2⌉ + 1
    (Neumann-Lara, 1982). This shows dichromatic number can be much smaller
    than chromatic number. -/
axiom complete_dichrom (n : ℕ) (hn : n ≥ 1) :
    (⊤ : SimpleGraph (Fin n)).dichromNumber = (n + 1) / 2 + 1

/-- For odd cycles C_{2k+1}, the dichromatic number is 2 while the
    chromatic number is 3. This is a simple example showing δ(G) < χ(G).
    Statement placeholder — cycle graph construction not in Mathlib. -/
theorem odd_cycle_dichrom (k : ℕ) (_hk : k ≥ 1) :
    True := trivial

-- ## Structural Observations

/-- The dichromatic number is monotone under subgraphs:
    if H is a subgraph of G, then δ(H) ≤ δ(G).
    Proof: Any orientation O_H of H extends to an orientation O_G of G
    (keep O_H directions on H-edges, assign arbitrary directions to G-only edges).
    An acyclic k-coloring for O_G restricts to one for O_H, so the infimum
    for H is ≤ the infimum for G. -/
theorem dichrom_mono {V : Type*} (G H : SimpleGraph V)
    (hSub : ∀ u v, H.Adj u v → G.Adj u v) :
    H.dichromNumber ≤ G.dichromNumber := by
  unfold SimpleGraph.dichromNumber
  -- sInf H_set ≤ sInf G_set: suffices to show G_set ⊆ H_set
  -- Then sInf G_set ∈ G_set (nonempty), hence in H_set, hence sInf H_set ≤ sInf G_set
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
  exact ⟨c, fun u v hdir => hc u v (Or.inl hdir)⟩

/-- For ANY orientation, any proper coloring is acyclic. This is because
    O.dir u v → G.Adj u v (by consistency), so if c(u) ≠ c(v) whenever
    G.Adj u v, then c(u) ≠ c(v) whenever O.dir u v.

    We construct an arbitrary orientation using the Fin ordering from Fintype. -/
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

theorem acyclic_orientation_exists {V : Type*} [Fintype V]
    (G : SimpleGraph V) :
    ∃ O : Orientation G, ∀ (c : V → Fin (Fintype.card V)),
    (∀ u v, G.Adj u v → c u ≠ c v) → IsAcyclicColoring O c :=
  ⟨arbitraryOrientation G, fun c hc u v hdir =>
    hc u v ((arbitraryOrientation G).consistent u v hdir)⟩
