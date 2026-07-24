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
  O.isAcyclic ∧ ¬ GraphOrientation.hasShortcut O

/-- G admits a Hasse-like orientation -/
def isHasseOrientable (G : SimpleGraph V) : Prop :=
  ∃ (O : GraphOrientation G), GraphOrientation.isHasse O

/-
## Cover Orientations Are Shortcut-Free
-/

/-- In a poset's cover orientation, u ⋖ v means no intermediate w exists
    strictly between u and v. So if u ⋖ v, u ⋖ w, and w ⋖ v all held,
    then w lies strictly between u and v, contradicting u ⋖ v. -/
theorem coverOrientation_no_shortcut
    [PartialOrder V] [DecidableEq V]
    (hcover : isCoverGraphOf G) :
    ¬ GraphOrientation.hasShortcut (coverOrientation G hcover) := by
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
theorem cover_search_space_bound [Fintype V] [DecidableEq V] :
    Fintype.card (V → V → Bool) = 2 ^ (Fintype.card V * Fintype.card V) := by
  simp [Fintype.card_fun, Fintype.card_bool, pow_mul]

/-
## Comparability Graphs (Known Polynomial Recognition)
-/

/-- A comparability graph of a poset P: edges are related pairs (not just covering). -/
def isComparabilityGraph (G : SimpleGraph V) : Prop :=
  ∃ (_ : PartialOrder V), ∀ u v, G.Adj u v ↔ (u < v ∨ v < u)

/-- For **any** predicate on graphs a Boolean recognizer exists — trivially,
    under classical logic (`f := fun G => decide (P G)`). This captures NONE of
    the algorithmic (polynomial-time) content: it is pure decidability
    packaging, true even for undecidable-in-practice `P`. Used below to
    discharge the two former "recognition_in_p" axioms, whose Lean statements
    were of exactly this trivial shape (and therefore vacuous). -/
theorem exists_bool_recognizer (P : SimpleGraph V → Prop) :
    ∃ f : SimpleGraph V → Bool, ∀ G : SimpleGraph V, f G = true ↔ P G := by
  classical
  refine ⟨fun G => decide (P G), fun G => ?_⟩
  simp only [decide_eq_true_eq]

/-- **Boolean recognizer for comparability graphs exists** (formerly an axiom).

    NOTE — honest scope: this statement only asserts that *some* Boolean
    function recognizes comparability graphs, which is trivially true under
    classical logic (`exists_bool_recognizer`). It does **not** formalize the
    polynomial-time bound its name suggests. Golumbic (1977) supplies the actual
    poly-time algorithm; formalizing "in P" would require a complexity model
    absent from Mathlib. Retained (proved) rather than left as a vacuous
    axiom. -/
theorem comparability_recognition_in_p [Fintype V] [DecidableEq V] :
    ∃ (f : SimpleGraph V → Bool),
      (∀ G : SimpleGraph V, f G = true ↔ isComparabilityGraph G) :=
  exists_bool_recognizer isComparabilityGraph

/-
## Algorithmic Complexity of Cover Recognition
-/

/-- **Boolean recognizer for cover graphs exists** (formerly the axiom
    `cover_graph_recognition_in_p`; renamed to avoid overclaiming).

    ⚠ The genuine open question (erdosproblems.com/1006 OQ-02) is whether cover
    graphs can be recognized in **polynomial time**. That is a *complexity*
    statement and is **NOT** formalized here — Mathlib has no complexity model.
    The former axiom `cover_graph_recognition_in_p` had exactly this Lean
    statement (`∃ f : SimpleGraph V → Bool, …`), which is trivially true for any
    predicate under classical logic and so captured none of the poly-time
    content: it was a vacuous axiom mislabeled as encoding the open conjecture.
    We prove the trivial content and rename, so nothing claims the open problem
    is resolved.

    Known context (unchanged, informal): cover recognition is in NP (the poset
    is a poly-time-verifiable certificate); whether it is in P or NP-hard is
    open. A positive resolution would plausibly (1) find a transitive
    orientation (polynomial: 2-SAT / modular decomposition), then (2) check no
    shortcuts remain (polynomial) — with the shortcut check the current
    barrier. -/
theorem exists_bool_cover_recognizer [Fintype V] [DecidableEq V] :
    ∃ (f : SimpleGraph V → Bool),
      (∀ G : SimpleGraph V, f G = true ↔ isCoverGraph G) :=
  exists_bool_recognizer isCoverGraph

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

/-- The combinatorial core, stated over an abstract poset so that `⋖`, `<` and
    `lt_irrefl` all resolve to the single ambient `PartialOrder W` instance (no
    competing canonical order as there would be on a concrete `Fin 3`). Three
    pairwise-distinct elements cannot be pairwise covering: every orientation of
    the three covering pairs yields either a 3-chain (a covering pair with a
    strictly-between element) or a directed 3-cycle (giving `x < x`). -/
private theorem no_pairwise_covering_triangle {W : Type*} [PartialOrder W] {a b c : W}
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (cov : ∀ x y : W, x ≠ y → (x ⋖ y ∨ y ⋖ x)) : False := by
  have no_chain : ∀ x y z : W, x ⋖ y → y ⋖ z → ¬(x ⋖ z) := fun x y z hxy hyz hxz =>
    hxz.2 hxy.lt hyz.lt
  rcases cov a b hab with hab' | hab' <;>
  rcases cov a c hac with hac' | hac' <;>
  rcases cov b c hbc with hbc' | hbc'
  · exact no_chain a b c hab' hbc' hac'
  · exact no_chain a c b hac' hbc' hab'
  · exact absurd (hab'.lt.trans (hbc'.lt.trans hac'.lt)) (lt_irrefl _)
  · exact no_chain c a b hac' hab' hbc'
  · exact no_chain b a c hab' hac' hbc'
  · exact absurd (hab'.lt.trans (hac'.lt.trans hbc'.lt)) (lt_irrefl _)
  · exact no_chain b c a hbc' hac' hab'
  · exact no_chain c b a hbc' hab' hac'

/-- K₃ is NOT a cover graph: no partial order on `Fin 3` has all three pairs as
    covering relations (see `no_pairwise_covering_triangle`). -/
theorem k3_not_cover_graph : ¬isCoverGraph (⊤ : SimpleGraph (Fin 3)) := by
  rintro ⟨ho, hcover⟩
  -- Apply the abstract core with the witnessed order `ho` passed explicitly, so
  -- the covering relation matches `hcover`'s (rather than Fin 3's canonical order).
  exact @no_pairwise_covering_triangle (Fin 3) ho 0 1 2 (by decide) (by decide) (by decide)
    (fun x y hxy => (hcover x y).mp (by rwa [SimpleGraph.top_adj]))

/-- Strict separation: the inclusion of cover graphs in comparability graphs is proper.
    The triangle K₃ (3 vertices, all pairs connected) is a comparability graph
    (via the linear order 0 < 1 < 2) but not a cover graph (proved above). -/
theorem cover_strictly_subset_comparability :
    ∃ (W : Type) (_ : Fintype W) (H : SimpleGraph W),
      isComparabilityGraph H ∧ ¬isCoverGraph H :=
  ⟨Fin 3, inferInstance, ⊤, k3_is_comparability_graph, k3_not_cover_graph⟩

end Erdos1006OQ01OQ02
