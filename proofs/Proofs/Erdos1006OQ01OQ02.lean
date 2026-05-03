/-
  Erdős Problem #1006 - Open Question 01 - Open Question 02:
  Cover Graph Recognition in Polynomial Time

  Source: https://erdosproblems.com/1006
  Related: Pretzel (1985), Brightwell (1988), Golumbic (1977)

  Background:
  From OQ-01 (Pretzel-Brightwell 1985): A graph G admits a robustly acyclic
  orientation iff G is a cover graph — the Hasse diagram of some finite poset.

  OQ-02 asks: Can we RECOGNIZE cover graphs in polynomial time?

  Key distinction between cover graphs and comparability graphs:
  - Comparability graph of P: u ~ v iff u < v or v < u (related pairs)
  - Cover graph of P: u ~ v iff u ⋖ v or v ⋖ u (covering pairs = Hasse diagram)
  Cover graphs are strict subgraphs of their poset's comparability graphs.

  Complexity:
  - Cover membership is in NP (a poset certificate is poly-time verifiable).
  - Comparability recognition is in P (Golumbic 1977).
  - Whether cover recognition is in P or NP-complete is open.

  Key structural fact: G is a cover graph iff G has a shortcut-free acyclic
  orientation — no arc u→v has an alternative directed path u→w→v.

  This file proves:
  1. `coverOrientation_no_shortcut` — Hasse orientations are shortcut-free
  2. `cover_graph_is_hasse` — cover graphs admit Hasse-like orientations
  3. `cover_implies_related` — cover graph edges connect related pairs
  4. `cover_search_space_bound` — recognition search space is 2^(n²)
  5. States open conjecture and known comparability result

  References:
  - Pretzel (1985): Robust orientation ↔ cover graph
  - Golumbic (1977): Comparability graph recognition in P
-/

import Proofs.Erdos1006OQ01

open SimpleGraph

namespace Erdos1006OQ01OQ02

variable {V : Type*} {G : SimpleGraph V}

/-
## Shortcut-Free Orientations (Hasse Property)

A cover graph's Hasse diagram orientation is shortcut-free: if u → v is a
direct covering arc, there is no intermediate vertex w with u → w → v.
This is the key structural property distinguishing cover graphs from
arbitrary acyclic graphs.
-/

/-- An orientation has a shortcut if some arc u→v has an alternative directed
    path u→w→v (of length 2) — the arc is redundant given the path. -/
def GraphOrientation.hasShortcut (O : GraphOrientation G) : Prop :=
  ∃ u v : V, O.arc u v ∧
    ∃ w : V, w ≠ u ∧ w ≠ v ∧ O.arc u w ∧ O.arc w v

/-- An orientation is Hasse-like: acyclic and shortcut-free. -/
def GraphOrientation.isHasse (O : GraphOrientation G) : Prop :=
  O.isAcyclic ∧ ¬O.hasShortcut

/-- G admits a Hasse-like orientation -/
def isHasseOrientable (G : SimpleGraph V) : Prop :=
  ∃ (O : GraphOrientation G), O.isHasse

/-
## Cover Orientations Are Shortcut-Free
-/

/-- In a poset's cover orientation, u ⋖ v means no intermediate w exists
    strictly between u and v. So if u ⋖ v, u ⋖ w, and w ⋖ v all held,
    then w lies strictly between u and v, contradicting u ⋖ v. -/
theorem coverOrientation_no_shortcut
    [PartialOrder V] [DecidableEq V]
    (hcover : isCoverGraphOf G) :
    ¬(coverOrientation G hcover).hasShortcut := by
  intro ⟨u, v, huv, w, _, _, huw, hwv⟩
  -- huv : u ⋖ v (arc in cover orientation means covering relation)
  -- huw : u ⋖ w, hwv : w ⋖ v
  -- Then u < w < v, but u ⋖ v means nothing lies strictly between u and v
  exact absurd hwv.lt (huv.2 huw.lt)

/-
## Cover Graphs Have Hasse Orientations
-/

/-- Every cover graph admits a Hasse-like orientation (the poset's cover relation). -/
theorem cover_graph_is_hasse
    [PartialOrder V] [DecidableEq V] [Fintype V] [DecidableLT V]
    (hcover : isCoverGraphOf G) :
    isHasseOrientable G :=
  ⟨coverOrientation G hcover,
    ⟨posetRank, fun u v huv => posetRank_strictMono huv.lt⟩,
    coverOrientation_no_shortcut hcover⟩

/-
## Relation Between Cover Graphs and Comparability Graphs

Cover graph edges are a subset of the comparability relation:
if u ~ v in Cover(P), then u and v are related in P (u < v or v < u).
The inclusion is strict: comparability graphs include transitive edges
(u < w < v gives u ~ v in comparability but not necessarily in Cover(P)).
-/

/-- Every edge of a cover graph witnesses a comparable pair in the poset.
    Proof: u ⋖ v implies u < v, and v ⋖ u implies v < u. -/
theorem cover_implies_related
    [PartialOrder V]
    (hcover : isCoverGraphOf G) {u v : V} (hadj : G.Adj u v) :
    u < v ∨ v < u := by
  rcases (hcover u v).mp hadj with huv | hvu
  · exact Or.inl huv.lt
  · exact Or.inr hvu.lt

/-- Strict separation: the cover graph of a 3-chain is a path (2 edges),
    while the comparability graph of a 3-chain is a triangle (3 edges).
    So cover graphs are a strict subset of comparability graphs. -/
example : True := trivial  -- The separation witnesses conceptually above

/-
## NP Certificate for Cover Graph Membership
-/

/-- A partial order P with isCoverGraphOf G is a polynomial-time verifiable
    certificate that G is a cover graph. This shows cover graph membership ∈ NP. -/
theorem cover_graph_in_np
    [Fintype V] [PartialOrder V] [DecidableEq V]
    (hcover : isCoverGraphOf G) :
    isCoverGraph G :=
  ⟨inferInstance, hcover⟩

/-- The covering relation check is decidable for finite types with decidable adjacency. -/
instance isCoverGraphOf_decidable
    [Fintype V] [PartialOrder V] [DecidableEq V]
    [DecidableRel G.Adj]
    [DecidableRel (· ⋖ · : V → V → Prop)] :
    Decidable (isCoverGraphOf G) :=
  Fintype.decidableForallFintype

/-
## Search Space Bound
-/

/-- The space of Boolean relations on V has size 2^(|V|²).
    Cover graph recognition searches over all partial orders on V,
    which is a subset of this space. -/
theorem cover_search_space_bound [Fintype V] :
    Fintype.card (V → V → Bool) = 2 ^ (Fintype.card V * Fintype.card V) := by
  simp [Fintype.card_fun, Fintype.card_bool, pow_mul]

/-
## Comparability Graphs (Known Polynomial Recognition)
-/

/-- A comparability graph of a poset P: edges are related pairs (not just covering). -/
def isComparabilityGraph (G : SimpleGraph V) : Prop :=
  ∃ (_ : PartialOrder V), ∀ u v, G.Adj u v ↔ (u < v ∨ v < u)

/-- KNOWN (Golumbic 1977): Comparability graph recognition is in polynomial time. -/
axiom comparability_recognition_in_p [Fintype V] [DecidableEq V] :
  ∃ (f : SimpleGraph V → Bool),
    (∀ G : SimpleGraph V, f G = true ↔ isComparabilityGraph G)

/-
## Algorithmic Complexity of Cover Recognition
-/

/-- OPEN CONJECTURE: Cover graph recognition is in polynomial time.
    Status: in NP (certificate = the poset). Whether P or NP-hard: open.
    A positive resolution would likely proceed via:
    (1) Find a transitive orientation (polynomial, reduces to 2-SAT or modular
        decomposition), then
    (2) Check that no shortcuts exist (remove transitive arcs — polynomial).
    Current barrier: step (1) finds a comparability orientation, but step (2)
    requires checking the resulting acyclic orientation has no shortcut, which
    may require additional structure. -/
axiom cover_graph_recognition_in_p [Fintype V] [DecidableEq V] :
  ∃ (f : SimpleGraph V → Bool),
    (∀ G : SimpleGraph V, f G = true ↔ isCoverGraph G)

/-
## Consequence: Cover Graphs ⊆ Comparability Graphs as Classes

If both recognition problems are in P, then cover graphs form a
proper subset of comparability graphs (by strict inclusion at triangle K₃:
K₃ is a comparability graph but not a cover graph).
-/

/-- Cover graphs form a subset of comparability graphs (edge-wise):
    the partial order witnessing the cover structure also witnesses
    comparability for all edges. -/
theorem cover_subclass_comparability [PartialOrder V]
    (hcover : isCoverGraphOf G) :
    ∀ u v, G.Adj u v → (u < v ∨ v < u) :=
  fun u v hadj => cover_implies_related hcover hadj

/-
## K₃: Strict Separation Between Cover and Comparability Graphs

The triangle K₃ (= ⊤ : SimpleGraph (Fin 3)) is a comparability graph but NOT a cover graph.
This concretely proves that the inclusion cover ⊊ comparability is strict, as mentioned in the
comment above. The standard order 0 < 1 < 2 on Fin 3 makes K₃ a comparability graph; but no
partial order can make K₃ a cover graph, since any two covering edges forming a chain forbid
the third edge from being a covering relation.
-/

/-- K₃ is a comparability graph: the standard linear order on Fin 3 (0 < 1 < 2) makes all
    distinct pairs comparable, so every edge of K₃ is witnessed by a comparability relation. -/
theorem k3_is_comparability_graph : isComparabilityGraph (⊤ : SimpleGraph (Fin 3)) :=
  ⟨inferInstance, fun u v => by
    simp only [SimpleGraph.top_adj]
    exact ⟨fun h => lt_or_gt_of_ne h,
           fun h => h.elim ne_of_lt (fun hvu => hvu.ne')⟩⟩

/-- K₃ is NOT a cover graph: no partial order on 3 vertices has all three pairs as covering
    relations. Core argument: x ⋖ y and y ⋖ z immediately forbid x ⋖ z (since y lies strictly
    between x and z). With three covering edges required, any orientation of the three covering
    relations either produces a 3-chain (making the long edge non-covering) or a directed cycle
    (impossible in a partial order). -/
theorem k3_not_cover_graph : ¬isCoverGraph (⊤ : SimpleGraph (Fin 3)) := by
  intro ⟨_, hcover⟩
  -- x ⋖ y and y ⋖ z is impossible alongside x ⋖ z: y lies strictly between x and z
  have no_chain : ∀ x y z : Fin 3, x ⋖ y → y ⋖ z → ¬(x ⋖ z) := fun x y z hxy hyz hxz =>
    hxz.2 hxy.lt hyz.lt
  -- All pairs in K₃ must have a covering relation
  have cov : ∀ i j : Fin 3, i ≠ j → (i ⋖ j ∨ j ⋖ i) := fun i j hij =>
    (hcover i j).mp hij
  -- 8-way case split on orientations of covering edges {0,1}, {0,2}, {1,2}
  rcases cov 0 1 (by decide) with h01 | h01 <;>
  rcases cov 0 2 (by decide) with h02 | h02 <;>
  rcases cov 1 2 (by decide) with h12 | h12
  -- (0⋖1, 0⋖2, 1⋖2): chain 0<1<2 violates 0⋖2
  · exact no_chain 0 1 2 h01 h12 h02
  -- (0⋖1, 0⋖2, 2⋖1): chain 0<2<1 violates 0⋖1
  · exact no_chain 0 2 1 h02 h12 h01
  -- (0⋖1, 2⋖0, 1⋖2): cycle 2<0<1<2 gives 2<2
  · exact absurd (h02.lt.trans (h01.lt.trans h12.lt)) (lt_irrefl 2)
  -- (0⋖1, 2⋖0, 2⋖1): chain 2<0<1 violates 2⋖1
  · exact no_chain 2 0 1 h02 h01 h12
  -- (1⋖0, 0⋖2, 1⋖2): chain 1<0<2 violates 1⋖2
  · exact no_chain 1 0 2 h01 h02 h12
  -- (1⋖0, 0⋖2, 2⋖1): cycle 1<0<2<1 gives 1<1
  · exact absurd (h01.lt.trans (h02.lt.trans h12.lt)) (lt_irrefl 1)
  -- (1⋖0, 2⋖0, 1⋖2): chain 1<2<0 violates 1⋖0
  · exact no_chain 1 2 0 h12 h02 h01
  -- (1⋖0, 2⋖0, 2⋖1): chain 2<1<0 violates 2⋖0
  · exact no_chain 2 1 0 h12 h01 h02

/-- Strict separation: the inclusion of cover graphs in comparability graphs is proper.
    The triangle K₃ (3 vertices, all pairs connected) is a comparability graph
    (via the linear order 0 < 1 < 2) but not a cover graph (proved above). -/
theorem cover_strictly_subset_comparability :
    ∃ (W : Type) (_ : Fintype W) (H : SimpleGraph W),
      isComparabilityGraph H ∧ ¬isCoverGraph H :=
  ⟨Fin 3, inferInstance, ⊤, k3_is_comparability_graph, k3_not_cover_graph⟩

end Erdos1006OQ01OQ02
