import Proofs.CycleDoubleCoverPort.GeneralGraph
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Finite
import Mathlib.Data.Fintype.Pigeonhole
import Mathlib.SetTheory.Cardinal.Finite

/-
# Cycle Double Cover port, step 4 (part 1): Nash-Williams--Tutte tree packing

Fourth slice of the port of the openai/cdc-lean development of the Cycle Double
Cover theorem (Szekeres 1973 / Seymour 1979, resolved 2026) into this gallery.
It corresponds to the *first part* of upstream `CDCLean/NashWilliams.lean`
(3,657 lines — by far the largest file in the development); see #37507 for the
porting order and #43625 / #43626 for steps 1 and 2.

## Provenance and licensing

`openai/cdc-lean` carries **no license file**, so default copyright applies and
no proof text may be vendored. This file is an *independent re-derivation*: the
upstream source was consulted only for the mathematical content — the shapes of
the definitions and the statements of the results — and every proof script here
was written from scratch against this repository's Mathlib pin. Several proofs
below deliberately take a different route from upstream (see "Deviations").

## What this part contains

The whole vocabulary of Kaiser's elementary proof of the Nash-Williams--Tutte
tree-packing theorem, together with the lemma layers that are independent of
the long local-exchange argument:

* the *support graph* of a set of edge objects and reachability/connectivity in
  it (`supportGraph`, `ReachableIn`, `Connects`, `IsSpanningTree`,
  `HasTreePacking`);
* partitions: crossing edges, the contracted quotient multigraph, the
  Nash-Williams--Tutte partition inequality (`SatisfiesTreePackingCondition`);
* edge colourings, colour classes, prefix trees and the residual class;
* Kaiser's refinement process (`refineSetoid`, `badColors`,
  `firstDisconnectedColor`, `refineOnce`, `kaiserPartition`), its monotonicity,
  its termination (`exists_stable_kaiserPartition`) and the notion of the
  *level* of an edge (`HasFiniteLevel`);
* the colour-swap exchange operator (`swapColor`) and the exact description of
  the three affected colour classes;
* elementary support-graph facts (adjacency, edge finset, monotonicity, walk
  transport lemmas);
* the counting layer for setoid classes (`sum_card_setoid_classes`) and the
  packing-to-colouring translation (`coloringOfPacking`).

## Deviations from upstream (all statement-preserving)

* Upstream selects the least disconnected colour with a bare `dite` on
  `NeedsRefinement` plus an inline `Finset.min'`. Here the "bad colour" finset
  is named (`badColors`) and the selector is characterised once and for all by
  `firstDisconnectedColor_eq_some_iff`, from which the three upstream facts
  (`_spec`, `_internal_of_lt`, `_eq_some_of_spec`) are immediate.
* Upstream's `refineOnce` matches on an `Option`; here it is `Option.elim`,
  which gives the two clean rewrite lemmas `refineOnce_of_none` /
  `refineOnce_of_some`.
* Termination of the refinement process is proved by pigeonholing the *graph of
  the relation* as a `Finset (V × V)` (`setoidGraph`) rather than by routing
  through `Finpartition.ofSetoid`; consequently upstream's auxiliary
  `finpartitionOfSetoid`, `finpartitionOfSetoid_rel_iff` and
  `rel_iff_of_finpartition_eq` have no counterpart here (they are used upstream
  only inside `exists_stable_kaiserPartition`).
* Upstream's `isAcyclic_of_le` is already available in this repository's
  Mathlib pin as `SimpleGraph.IsAcyclic.anti`, so it is re-exported rather than
  re-proved.

## What is deferred to later parts

The long local-exchange argument and everything that depends on it. Concretely,
the following upstream declarations are **not** in this file and remain to be
ported: `inside_induce_connected`, `quotientGraph_connected_of_connects`,
`connects_of_internal_of_quotient_connects`,
`insideEdges_subset_erase_of_crossing`, `cyclicEdge_of_quotient_cyclic_of_internal`,
`reachableIn_erase_of_cyclic`, `componentSetoid_erase_eq_of_cyclic`,
`component_card_lt_of_not_cyclic`, `card_add_components_le_of_no_cyclic`,
`exists_cyclic_of_disconnected_of_card_ge`, `connects_erase_of_cyclic`,
`exists_isSpanningTree_subset_of_connects`, `supportGraph_isTree_of_spanningTree`,
`symEdge_injOn_of_spanningTree`, `reachableIn_inside_of_walk_of_no_crossing`,
`exists_crossing_tree_edge_of_not_internal_reachable`,
`rel_of_reachableIn_inside`, `path_edge_ends_rel_start_of_no_crossing`,
`connects_exchange_of_path_edge`, `isSpanningTree_exchange_of_path_edge`,
`reachableIn_inside_exchange_of_path_edge_of_new_support`,
`reachableIn_inside_exchange_of_path_edge`, `reachableIn_exchange_of_path_edge`,
`cyclicEdge_of_mem_path_of_cyclic_edge`,
`reachableIn_inside_erase_of_min_superfluous`, `reachableIn_of_adj_reachable`,
`refineSetoid_residual_erase_eq_of_min_superfluous`,
`refineSetoid_union_singleton_eq_of_internal_reachable`,
`refineSetoid_exchange_eq_of_path_internal`, `prefixTrees_swap_of_path_edge`,
`reachableIn_union_singleton_iff_of_reachable`,
`reachableIn_erase_union_singleton_iff_of_cyclic_of_reachable`,
`connectedComponent_card_eq_of_reachable_iff`,
`residualComponents_eq_of_reachable_iff`,
`connectedComponent_card_lt_of_union_singleton_of_not_reachable`,
`residualClass_swap_of_residual_of_tree`,
`residualComponents_swap_eq_of_cyclic_of_reachable`,
`cyclicEdge_swap_of_cyclic_of_reachable`,
`residualComponents_swap_lt_of_cyclic_of_not_reachable`,
`not_reachable_residual_of_level_zero`, `reachable_residual_of_positive_level`,
`exists_internal_tree_subset`, `crossingClass_card_eq_of_spanningTree_of_internal`,
`quotient_card_sub_one_le_crossingClass_card`,
`quotient_card_sub_one_le_crossingEdges_card`,
`satisfiesTreePackingCondition_of_hasTreePacking`,
`hasSuperfluousEdge_of_condition_of_disconnected`,
`exists_lower_level_tree_edge_of_superfluous`,
`exists_lower_level_tree_edge_on_path_of_superfluous`, `finiteLevelValue`,
`finiteLevelValue_spec`, `finiteLevelValue_eq_of_level`,
`exists_firstDisconnectedColor_of_finiteLevel`,
`finiteLevel_of_partitions_eq_upto`,
`exists_min_level_tree_edge_on_path_of_superfluous`,
`exists_min_level_tree_edge_on_path_anchored_of_superfluous`,
`kaiserPartition_eq_upto_of_min_exchange`, `HasSuperfluousLevel`,
`minSuperfluousLevel`, `minSuperfluousLevel_spec`, `minSuperfluousLevel_le`,
`HasKaiserImprovementStep`, `hasKaiserImprovementStep_of_condition`,
`exists_connected_residual_of_kaiser_step`, `hasTreePacking_of_kaiser_steps`,
`hasTreePacking_of_condition` and the headline `nashWilliamsTutte`.

Nothing in this file is `sorry`-free by accident: there are no `sorry`s, no
`native_decide`, and no `axiom` declarations. This file does **not** discharge
`CycleDoubleCover.cycleDoubleCover_of_bridgeless`; that is the final step of the
port.
-/

namespace CycleDoubleCover

namespace FiniteGraph

open scoped BigOperators

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
  (G : FiniteGraph V E)

/-! ## The support graph of a set of edge objects -/

/-- The simple graph underlying a set `S` of edge objects: two distinct vertices
are adjacent when some member of `S` joins them. Parallel edge objects induce
the same adjacency, which is all that reachability can see. -/
def supportGraph (S : Finset E) : SimpleGraph V :=
  SimpleGraph.fromRel fun u v => ∃ e ∈ S, G.endAt e 0 = u ∧ G.endAt e 1 = v

/-- Reachability using only the edge objects of `S`. -/
def ReachableIn (S : Finset E) (u v : V) : Prop :=
  (G.supportGraph S).Reachable u v

/-- `S` joins up all of `V`. -/
def Connects (S : Finset E) : Prop :=
  (G.supportGraph S).Connected

/-- A spanning tree, in the cardinality form Kaiser's exchange argument needs: a
connected set of exactly `|V| - 1` edge objects. For a finite multigraph this is
equivalent to connected-and-acyclic. -/
def IsSpanningTree (S : Finset E) : Prop :=
  G.Connects S ∧ S.card + 1 = Fintype.card V

/-- A packing of `k` pairwise edge-disjoint spanning trees. -/
def HasTreePacking (k : ℕ) : Prop :=
  ∃ T : Fin k → Finset E,
    (∀ i, G.IsSpanningTree (T i)) ∧ ∀ i j, i ≠ j → Disjoint (T i) (T j)

/-! ## Partitions, crossing edges and contraction -/

open Classical in
/-- All edge objects whose two ends lie in different classes of `P`. -/
noncomputable def crossingEdges (P : Setoid V) : Finset E :=
  Finset.univ.filter fun e => ¬ P (G.endAt e 0) (G.endAt e 1)

open Classical in
/-- The members of `S` whose two ends lie in different classes of `P`. -/
noncomputable def crossingClass (S : Finset E) (P : Setoid V) : Finset E :=
  S.filter fun e => ¬ P (G.endAt e 0) (G.endAt e 1)

omit [DecidableEq V] [DecidableEq E] in
@[simp]
theorem mem_crossingEdges {P : Setoid V} {e : E} :
    e ∈ G.crossingEdges P ↔ ¬ P (G.endAt e 0) (G.endAt e 1) := by
  classical
  simp [crossingEdges]

omit [DecidableEq V] [DecidableEq E] in
@[simp]
theorem mem_crossingClass {S : Finset E} {P : Setoid V} {e : E} :
    e ∈ G.crossingClass S P ↔ e ∈ S ∧ ¬ P (G.endAt e 0) (G.endAt e 1) := by
  classical
  simp [crossingClass]

omit [DecidableEq V] [DecidableEq E] in
theorem crossingClass_subset_crossingEdges (S : Finset E) (P : Setoid V) :
    G.crossingClass S P ⊆ G.crossingEdges P := by
  intro e he
  exact G.mem_crossingEdges.mpr (G.mem_crossingClass.mp he).2

noncomputable instance instFintypeQuotientSetoid (P : Setoid V) : Fintype (Quotient P) :=
  Fintype.ofFinite _

/-- Contract the classes of `P` and throw away the edges that became loops. The
edge type is a subtype of genuine edge objects, so parallel edges stay
distinct. -/
noncomputable def quotientGraph (S : Finset E) (P : Setoid V) :
    FiniteGraph (Quotient P) {e : E // e ∈ G.crossingClass S P} where
  endAt e i := Quotient.mk P (G.endAt e.1 i)
  loopless e := by
    intro h
    exact (G.mem_crossingClass.mp e.2).2 (Quotient.exact h)

/-- The Nash-Williams--Tutte partition inequality for `k` trees. -/
def SatisfiesTreePackingCondition (k : ℕ) : Prop :=
  ∀ P : Setoid V, k * (Nat.card (Quotient P) - 1) ≤ (G.crossingEdges P).card

omit [DecidableEq V] [DecidableEq E] in
theorem satisfiesTreePackingCondition_mono {a b : ℕ} (hab : a ≤ b)
    (h : G.SatisfiesTreePackingCondition b) : G.SatisfiesTreePackingCondition a := by
  intro P
  exact le_trans (Nat.mul_le_mul_right _ hab) (h P)

/-- The partition of `V` into connected components of `S`. -/
def componentSetoid (S : Finset E) : Setoid V :=
  (G.supportGraph S).reachableSetoid

/-! ## Edges internal to a class, and one refinement step -/

open Classical in
/-- The members of `S` with both ends in the `P`-class of `u`. -/
noncomputable def insideEdges (S : Finset E) (P : Setoid V) (u : V) : Finset E :=
  S.filter fun e => P (G.endAt e 0) u ∧ P (G.endAt e 1) u

omit [DecidableEq V] [DecidableEq E] in
@[simp]
theorem mem_insideEdges {S : Finset E} {P : Setoid V} {u : V} {e : E} :
    e ∈ G.insideEdges S P u ↔ e ∈ S ∧ P (G.endAt e 0) u ∧ P (G.endAt e 1) u := by
  classical
  simp [insideEdges]

omit [DecidableEq V] [DecidableEq E] in
theorem insideEdges_eq_of_rel {S : Finset E} {P : Setoid V} {u v : V} (huv : P u v) :
    G.insideEdges S P u = G.insideEdges S P v := by
  ext e
  simp only [mem_insideEdges]
  exact and_congr_right fun _ =>
    and_congr (⟨fun h => P.trans' h huv, fun h => P.trans' h (P.symm' huv)⟩)
      (⟨fun h => P.trans' h huv, fun h => P.trans' h (P.symm' huv)⟩)

omit [DecidableEq V] [DecidableEq E] in
theorem insideEdges_subset (S : Finset E) (P : Setoid V) (u : V) :
    G.insideEdges S P u ⊆ S := fun _ he => (G.mem_insideEdges.mp he).1

omit [DecidableEq V] in
theorem insideEdges_erase (S : Finset E) (P : Setoid V) (u : V) (e : E) :
    G.insideEdges (S.erase e) P u = (G.insideEdges S P u).erase e := by
  ext f
  simp only [mem_insideEdges, Finset.mem_erase]
  tauto

omit [DecidableEq V] [DecidableEq E] in
theorem insideEdges_top (S : Finset E) (u : V) : G.insideEdges S ⊤ u = S := by
  have htop : ∀ x y : V, (⊤ : Setoid V) x y := fun _ _ => trivial
  ext e
  simp [mem_insideEdges, htop]

/-- Kaiser's single refinement step: split every class of `P` into the connected
components of `S` inside it. -/
noncomputable def refineSetoid (P : Setoid V) (S : Finset E) : Setoid V where
  r u v := P u v ∧ G.ReachableIn (G.insideEdges S P u) u v
  iseqv :=
    { refl := fun u => ⟨P.refl' u, SimpleGraph.Reachable.refl u⟩
      symm := by
        rintro u v ⟨h1, h2⟩
        refine ⟨P.symm' h1, ?_⟩
        rw [← G.insideEdges_eq_of_rel (S := S) h1]
        exact h2.symm
      trans := by
        rintro u v w ⟨h1, h2⟩ ⟨h3, h4⟩
        refine ⟨P.trans' h1 h3, ?_⟩
        rw [G.insideEdges_eq_of_rel (S := S) h1] at h2 ⊢
        exact h2.trans h4 }

omit [DecidableEq V] [DecidableEq E] in
theorem refineSetoid_le (P : Setoid V) (S : Finset E) {u v : V}
    (h : G.refineSetoid P S u v) : P u v := h.1

/-! ## Edge colourings -/

/-- The edges carrying colour `i`. Using a total colouring rather than a tuple of
sets makes disjointness and coverage definitional. -/
def colorClass {k : ℕ} (χ : E → Fin k) (i : Fin k) : Finset E :=
  Finset.univ.filter fun e => χ e = i

omit [DecidableEq E] in
@[simp]
theorem mem_colorClass {k : ℕ} {χ : E → Fin k} {i : Fin k} {e : E} :
    e ∈ colorClass χ i ↔ χ e = i := by simp [colorClass]

omit [DecidableEq E] in
theorem colorClass_disjoint {k : ℕ} (χ : E → Fin k) {i j : Fin k} (hij : i ≠ j) :
    Disjoint (colorClass χ i) (colorClass χ j) := by
  refine Finset.disjoint_left.2 fun e hei hej => hij ?_
  rw [← mem_colorClass.mp hei, mem_colorClass.mp hej]

omit [DecidableEq V] [DecidableEq E] in
theorem crossingClass_colorClass_disjoint {k : ℕ} (χ : E → Fin k) (P : Setoid V)
    {i j : Fin k} (hij : i ≠ j) :
    Disjoint (G.crossingClass (colorClass χ i) P) (G.crossingClass (colorClass χ j) P) := by
  refine Finset.disjoint_left.2 fun e hei hej => ?_
  exact Finset.disjoint_left.mp (colorClass_disjoint χ hij)
    (G.mem_crossingClass.mp hei).1 (G.mem_crossingClass.mp hej).1

omit [DecidableEq E] in
theorem mem_some_colorClass {k : ℕ} (χ : E → Fin k) (e : E) :
    ∃ i : Fin k, e ∈ colorClass χ i := ⟨χ e, mem_colorClass.mpr rfl⟩

omit [DecidableEq V] in
theorem crossingEdges_eq_biUnion_crossingClass {k : ℕ} [NeZero k] (χ : E → Fin k)
    (P : Setoid V) :
    G.crossingEdges P =
      Finset.univ.biUnion fun i : Fin k => G.crossingClass (colorClass χ i) P := by
  ext e
  simp only [mem_crossingEdges, Finset.mem_biUnion, Finset.mem_univ, true_and,
    mem_crossingClass, mem_colorClass]
  exact ⟨fun h => ⟨χ e, rfl, h⟩, fun ⟨_, _, h⟩ => h⟩

omit [DecidableEq V] in
theorem crossingEdges_card_eq_sum_crossingClass {k : ℕ} [NeZero k] (χ : E → Fin k)
    (P : Setoid V) :
    (G.crossingEdges P).card =
      ∑ i : Fin k, (G.crossingClass (colorClass χ i) P).card := by
  rw [G.crossingEdges_eq_biUnion_crossingClass χ P]
  exact Finset.card_biUnion fun i _ j _ hij => G.crossingClass_colorClass_disjoint χ P hij

/-- In the inductive step colours `0, …, k-1` already carry spanning trees. -/
def PrefixTrees {k : ℕ} (χ : E → Fin (k + 1)) : Prop :=
  ∀ i : Fin k, G.IsSpanningTree (colorClass χ i.castSucc)

/-- The last colour: the residual subgraph left over by a prefix of trees. -/
def residualClass {k : ℕ} (χ : E → Fin (k + 1)) : Finset E :=
  colorClass χ (Fin.last k)

/-- The number of connected components of the residual subgraph. -/
noncomputable def residualComponents {k : ℕ} (χ : E → Fin (k + 1)) : ℕ :=
  Nat.card (G.supportGraph (residualClass χ)).ConnectedComponent

/-! ## Kaiser's refinement process -/

/-- A colour is *internally connected* for `P` when it joins up each class of `P`
from the inside. This is the stopping condition of the refinement process. -/
def InternallyConnected (S : Finset E) (P : Setoid V) : Prop :=
  ∀ u v : V, P u v → G.ReachableIn (G.insideEdges S P u) u v

def NeedsRefinement {k : ℕ} (χ : E → Fin k) (P : Setoid V) : Prop :=
  ∃ i : Fin k, ¬ G.InternallyConnected (colorClass χ i) P

open Classical in
/-- The colours that fail to be internally connected for `P`. -/
noncomputable def badColors {k : ℕ} (χ : E → Fin k) (P : Setoid V) : Finset (Fin k) :=
  Finset.univ.filter fun i => ¬ G.InternallyConnected (colorClass χ i) P

omit [DecidableEq V] [DecidableEq E] in
@[simp]
theorem mem_badColors {k : ℕ} {χ : E → Fin k} {P : Setoid V} {i : Fin k} :
    i ∈ G.badColors χ P ↔ ¬ G.InternallyConnected (colorClass χ i) P := by
  classical
  simp [badColors]

omit [DecidableEq V] [DecidableEq E] in
theorem badColors_nonempty_iff {k : ℕ} (χ : E → Fin k) (P : Setoid V) :
    (G.badColors χ P).Nonempty ↔ G.NeedsRefinement χ P :=
  ⟨fun ⟨i, hi⟩ => ⟨i, G.mem_badColors.mp hi⟩, fun ⟨i, hi⟩ => ⟨i, G.mem_badColors.mpr hi⟩⟩

/-- The least colour that disconnects some class of `P`, if there is one. -/
noncomputable def firstDisconnectedColor {k : ℕ} (χ : E → Fin k) (P : Setoid V) :
    Option (Fin k) :=
  if h : (G.badColors χ P).Nonempty then some ((G.badColors χ P).min' h) else none

omit [DecidableEq V] [DecidableEq E] in
/-- Complete characterisation of the selector: it returns exactly the minimum of
the bad-colour set. Everything else about `firstDisconnectedColor` follows. -/
theorem firstDisconnectedColor_eq_some_iff {k : ℕ} {χ : E → Fin k} {P : Setoid V}
    {i : Fin k} :
    G.firstDisconnectedColor χ P = some i ↔
      i ∈ G.badColors χ P ∧ ∀ j ∈ G.badColors χ P, i ≤ j := by
  unfold firstDisconnectedColor
  by_cases h : (G.badColors χ P).Nonempty
  · rw [dif_pos h]
    constructor
    · intro hi
      have hmin : (G.badColors χ P).min' h = i := Option.some_injective _ hi
      subst hmin
      exact ⟨Finset.min'_mem _ h, fun j hj => Finset.min'_le _ j hj⟩
    · rintro ⟨hi, hle⟩
      have hmin : (G.badColors χ P).min' h = i :=
        le_antisymm (Finset.min'_le _ i hi) (hle _ (Finset.min'_mem _ h))
      rw [hmin]
  · rw [dif_neg h]
    refine ⟨fun hi => by simp at hi, ?_⟩
    rintro ⟨hi, -⟩
    exact absurd ⟨i, hi⟩ h

omit [DecidableEq V] [DecidableEq E] in
theorem firstDisconnectedColor_eq_none_iff {k : ℕ} (χ : E → Fin k) (P : Setoid V) :
    G.firstDisconnectedColor χ P = none ↔ ¬ G.NeedsRefinement χ P := by
  rw [← G.badColors_nonempty_iff]
  unfold firstDisconnectedColor
  by_cases h : (G.badColors χ P).Nonempty
  · rw [dif_pos h]; simp [h]
  · rw [dif_neg h]; simp [h]

omit [DecidableEq V] [DecidableEq E] in
theorem firstDisconnectedColor_spec {k : ℕ} {χ : E → Fin k} {P : Setoid V} {i : Fin k}
    (h : G.firstDisconnectedColor χ P = some i) :
    ¬ G.InternallyConnected (colorClass χ i) P :=
  G.mem_badColors.mp (G.firstDisconnectedColor_eq_some_iff.mp h).1

omit [DecidableEq V] [DecidableEq E] in
theorem firstDisconnectedColor_internal_of_lt {k : ℕ} {χ : E → Fin k} {P : Setoid V}
    {c d : Fin k} (hc : G.firstDisconnectedColor χ P = some c) (hdc : d < c) :
    G.InternallyConnected (colorClass χ d) P := by
  by_contra hbad
  exact absurd ((G.firstDisconnectedColor_eq_some_iff.mp hc).2 d (G.mem_badColors.mpr hbad))
    (not_le.mpr hdc)

omit [DecidableEq V] [DecidableEq E] in
theorem firstDisconnectedColor_eq_some_of_spec {k : ℕ} {χ : E → Fin k} {P : Setoid V}
    {c : Fin k} (hbad : ¬ G.InternallyConnected (colorClass χ c) P)
    (hbefore : ∀ d : Fin k, d < c → G.InternallyConnected (colorClass χ d) P) :
    G.firstDisconnectedColor χ P = some c := by
  refine G.firstDisconnectedColor_eq_some_iff.mpr ⟨G.mem_badColors.mpr hbad, fun j hj => ?_⟩
  by_contra hlt
  exact (G.mem_badColors.mp hj) (hbefore j (not_le.mp hlt))

omit [DecidableEq V] [DecidableEq E] in
theorem internallyConnected_iff_of_refineSetoid_eq {S T : Finset E} {P : Setoid V}
    (hEq : G.refineSetoid P S = G.refineSetoid P T) :
    G.InternallyConnected S P ↔ G.InternallyConnected T P := by
  constructor
  · intro h u v huv
    have hrel : G.refineSetoid P S u v := ⟨huv, h u v huv⟩
    rw [hEq] at hrel
    exact hrel.2
  · intro h u v huv
    have hrel : G.refineSetoid P T u v := ⟨huv, h u v huv⟩
    rw [← hEq] at hrel
    exact hrel.2

/-- One deterministic step of the process: refine by the least bad colour, or stop. -/
noncomputable def refineOnce {k : ℕ} (χ : E → Fin k) (P : Setoid V) : Setoid V :=
  (G.firstDisconnectedColor χ P).elim P fun i => G.refineSetoid P (colorClass χ i)

omit [DecidableEq V] [DecidableEq E] in
theorem refineOnce_of_none {k : ℕ} {χ : E → Fin k} {P : Setoid V}
    (hcol : G.firstDisconnectedColor χ P = none) : G.refineOnce χ P = P := by
  simp [refineOnce, hcol]

omit [DecidableEq V] [DecidableEq E] in
theorem refineOnce_of_some {k : ℕ} {χ : E → Fin k} {P : Setoid V} {i : Fin k}
    (hcol : G.firstDisconnectedColor χ P = some i) :
    G.refineOnce χ P = G.refineSetoid P (colorClass χ i) := by
  simp [refineOnce, hcol]

/-- Kaiser's nested sequence of partitions, starting from the one-class partition. -/
noncomputable def kaiserPartition {k : ℕ} (χ : E → Fin k) (n : ℕ) : Setoid V :=
  Nat.rec (motive := fun _ => Setoid V) ⊤ (fun _ P => G.refineOnce χ P) n

omit [DecidableEq V] [DecidableEq E] in
@[simp]
theorem kaiserPartition_zero {k : ℕ} (χ : E → Fin k) :
    G.kaiserPartition χ 0 = ⊤ := rfl

omit [DecidableEq V] [DecidableEq E] in
theorem kaiserPartition_succ {k : ℕ} (χ : E → Fin k) (n : ℕ) :
    G.kaiserPartition χ (n + 1) = G.refineOnce χ (G.kaiserPartition χ n) := rfl

omit [DecidableEq V] [DecidableEq E] in
theorem kaiserPartition_succ_refines {k : ℕ} (χ : E → Fin k) (n : ℕ) {u v : V}
    (h : G.kaiserPartition χ (n + 1) u v) : G.kaiserPartition χ n u v := by
  rw [kaiserPartition_succ] at h
  cases hcol : G.firstDisconnectedColor χ (G.kaiserPartition χ n) with
  | none => rwa [G.refineOnce_of_none hcol] at h
  | some i =>
      rw [G.refineOnce_of_some hcol] at h
      exact h.1

theorem kaiserPartition_refines_of_le {k : ℕ} (χ : E → Fin k) {m n : ℕ} (hmn : m ≤ n)
    {u v : V} (h : G.kaiserPartition χ n u v) : G.kaiserPartition χ m u v := by
  induction n, hmn using Nat.le_induction with
  | base => exact h
  | succ n hmn ih => exact ih (G.kaiserPartition_succ_refines χ n h)

open Classical in
/-- The graph of a setoid as a finite set of pairs. Used only to pigeonhole the
refinement process into stabilising. -/
noncomputable def setoidGraph (P : Setoid V) : Finset (V × V) :=
  Finset.univ.filter fun p => P p.1 p.2

omit [DecidableEq V] in
@[simp]
theorem mem_setoidGraph {P : Setoid V} {u v : V} :
    (u, v) ∈ setoidGraph (V := V) P ↔ P u v := by
  classical
  simp [setoidGraph]

omit [DecidableEq V] in
theorem setoid_eq_of_setoidGraph_eq {P Q : Setoid V}
    (h : setoidGraph (V := V) P = setoidGraph (V := V) Q) (u v : V) : P u v ↔ Q u v := by
  rw [← mem_setoidGraph (P := P) (u := u) (v := v), h, mem_setoidGraph]

/-- The refinement process stabilises: this is the finite termination fact behind
Kaiser's notation `P∞`. Proved by pigeonholing the graphs of the partitions,
which live in the finite type `Finset (V × V)`. -/
theorem exists_stable_kaiserPartition {k : ℕ} (χ : E → Fin k) :
    ∃ n : ℕ, G.firstDisconnectedColor χ (G.kaiserPartition χ n) = none := by
  classical
  obtain ⟨m, n, hmn, hEq⟩ :=
    Finite.exists_ne_map_eq_of_infinite fun t : ℕ => setoidGraph (V := V) (G.kaiserPartition χ t)
  -- Work with the smaller of the two indices.
  set a := min m n with ha
  set b := max m n with hb
  have hab : a < b := by
    rcases lt_or_gt_of_ne hmn with h | h
    · simp [ha, hb, min_eq_left h.le, max_eq_right h.le, h]
    · simp [ha, hb, min_eq_right h.le, max_eq_left h.le, h]
  have hgraph : setoidGraph (V := V) (G.kaiserPartition χ a)
      = setoidGraph (V := V) (G.kaiserPartition χ b) := by
    rcases lt_or_gt_of_ne hmn with h | h
    · simpa [ha, hb, min_eq_left h.le, max_eq_right h.le] using hEq
    · simpa [ha, hb, min_eq_right h.le, max_eq_left h.le] using hEq.symm
  -- Hence stage `a` and stage `a + 1` have the same relation.
  have hstep : ∀ u v : V, G.kaiserPartition χ a u v → G.kaiserPartition χ (a + 1) u v := by
    intro u v huv
    have hb' : G.kaiserPartition χ b u v :=
      (setoid_eq_of_setoidGraph_eq hgraph u v).mp huv
    exact G.kaiserPartition_refines_of_le χ (Nat.succ_le_of_lt hab) hb'
  refine ⟨a, ?_⟩
  cases hcol : G.firstDisconnectedColor χ (G.kaiserPartition χ a) with
  | none => rfl
  | some i =>
      exfalso
      have hbad := G.firstDisconnectedColor_spec hcol
      rw [InternallyConnected] at hbad
      push Not at hbad
      obtain ⟨u, v, huv, hnreach⟩ := hbad
      have hnext := hstep u v huv
      rw [kaiserPartition_succ, G.refineOnce_of_some hcol] at hnext
      exact hnreach hnext.2

omit [DecidableEq V] [DecidableEq E] in
theorem internallyConnected_of_stable {k : ℕ} {χ : E → Fin k} {n : ℕ}
    (hstable : G.firstDisconnectedColor χ (G.kaiserPartition χ n) = none) (i : Fin k) :
    G.InternallyConnected (colorClass χ i) (G.kaiserPartition χ n) := by
  by_contra hnot
  exact (G.firstDisconnectedColor_eq_none_iff χ _).mp hstable ⟨i, hnot⟩

omit [DecidableEq V] [DecidableEq E] in
theorem kaiserPartition_stable_after {k : ℕ} {χ : E → Fin k} {n : ℕ}
    (hstable : G.firstDisconnectedColor χ (G.kaiserPartition χ n) = none) :
    ∀ t : ℕ, G.kaiserPartition χ (n + t) = G.kaiserPartition χ n := by
  intro t
  induction t with
  | zero => rfl
  | succ t ih =>
      rw [← Nat.add_assoc, kaiserPartition_succ, ih, G.refineOnce_of_none hstable]

/-! ## Levels -/

/-- The two ends of `e` survive together up to stage `m` and are separated at
stage `m + 1`. -/
def HasFiniteLevel {k : ℕ} (χ : E → Fin k) (e : E) (m : ℕ) : Prop :=
  G.kaiserPartition χ m (G.endAt e 0) (G.endAt e 1) ∧
    ¬ G.kaiserPartition χ (m + 1) (G.endAt e 0) (G.endAt e 1)

theorem finiteLevel_unique {k : ℕ} {χ : E → Fin k} {e : E} {m n : ℕ}
    (hm : G.HasFiniteLevel χ e m) (hn : G.HasFiniteLevel χ e n) : m = n := by
  by_contra hne
  rcases lt_or_gt_of_ne hne with h | h
  · exact hm.2 (G.kaiserPartition_refines_of_le χ (Nat.succ_le_of_lt h) hn.1)
  · exact hn.2 (G.kaiserPartition_refines_of_le χ (Nat.succ_le_of_lt h) hm.1)

omit [DecidableEq V] [DecidableEq E] in
theorem exists_finiteLevel_of_not_rel {k : ℕ} {χ : E → Fin k} {e : E} {n : ℕ}
    (hnot : ¬ G.kaiserPartition χ n (G.endAt e 0) (G.endAt e 1)) :
    ∃ m : ℕ, G.HasFiniteLevel χ e m := by
  classical
  have hex : ∃ t : ℕ, ¬ G.kaiserPartition χ t (G.endAt e 0) (G.endAt e 1) := ⟨n, hnot⟩
  have hspec := Nat.find_spec hex
  have hpos : Nat.find hex ≠ 0 := by
    intro h0
    refine (h0 ▸ hspec) ?_
    rw [kaiserPartition_zero]
    trivial
  obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero hpos
  have hm' : Nat.find hex = m + 1 := by omega
  rw [hm'] at hspec
  refine ⟨m, ?_, hspec⟩
  by_contra hbad
  exact Nat.find_min hex (by omega) hbad

/-! ## Cyclic and superfluous edges -/

/-- `e` lies on a cycle of `S`: deleting it still leaves a route between its ends.
This is the edge-object form of "lies on a circuit". -/
def IsCyclicEdge (S : Finset E) (e : E) : Prop :=
  e ∈ S ∧ G.ReachableIn (S.erase e) (G.endAt e 0) (G.endAt e 1)

def IsSuperfluousAt {k : ℕ} (χ : E → Fin (k + 1)) (e : E) (m : ℕ) : Prop :=
  G.IsCyclicEdge (residualClass χ) e ∧ G.HasFiniteLevel χ e m

def HasSuperfluousEdge {k : ℕ} (χ : E → Fin (k + 1)) : Prop :=
  ∃ e m, G.IsSuperfluousAt χ e m

/-! ## Support-graph basics -/

omit [DecidableEq V] [DecidableEq E] in
theorem supportGraph_adj_iff (S : Finset E) (u v : V) :
    (G.supportGraph S).Adj u v ↔
      u ≠ v ∧ ∃ e ∈ S,
        (G.endAt e 0 = u ∧ G.endAt e 1 = v) ∨ (G.endAt e 0 = v ∧ G.endAt e 1 = u) := by
  simp only [supportGraph, SimpleGraph.fromRel_adj]
  constructor
  · rintro ⟨hne, ⟨e, he, h0, h1⟩ | ⟨e, he, h0, h1⟩⟩
    · exact ⟨hne, e, he, Or.inl ⟨h0, h1⟩⟩
    · exact ⟨hne, e, he, Or.inr ⟨h0, h1⟩⟩
  · rintro ⟨hne, e, he, ⟨h0, h1⟩ | ⟨h0, h1⟩⟩
    · exact ⟨hne, Or.inl ⟨e, he, h0, h1⟩⟩
    · exact ⟨hne, Or.inr ⟨e, he, h0, h1⟩⟩

/-- The unordered pair of ends of a genuine multiedge. -/
def symEdge (e : E) : Sym2 V := s(G.endAt e 0, G.endAt e 1)

omit [DecidableEq V] [DecidableEq E] in
theorem supportGraph_mono {S T : Finset E} (hST : S ⊆ T) :
    G.supportGraph S ≤ G.supportGraph T := by
  intro u v huv
  rw [G.supportGraph_adj_iff] at huv ⊢
  obtain ⟨hne, e, he, hends⟩ := huv
  exact ⟨hne, e, hST he, hends⟩

omit [DecidableEq E] in
theorem edgeFinset_supportGraph (S : Finset E) [Fintype (G.supportGraph S).edgeSet] :
    (G.supportGraph S).edgeFinset = S.image G.symEdge := by
  ext z
  induction z using Sym2.inductionOn with
  | _ u v =>
    rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet, G.supportGraph_adj_iff]
    simp only [Finset.mem_image, symEdge]
    constructor
    · rintro ⟨-, e, he, ⟨h0, h1⟩ | ⟨h0, h1⟩⟩
      · exact ⟨e, he, Sym2.eq_iff.mpr (Or.inl ⟨h0, h1⟩)⟩
      · exact ⟨e, he, Sym2.eq_iff.mpr (Or.inr ⟨h0, h1⟩)⟩
    · rintro ⟨e, he, hz⟩
      rcases Sym2.eq_iff.mp hz with ⟨h0, h1⟩ | ⟨h0, h1⟩
      · refine ⟨?_, e, he, Or.inl ⟨h0, h1⟩⟩
        rintro rfl
        exact G.loopless e (h0.trans h1.symm)
      · refine ⟨?_, e, he, Or.inr ⟨h0, h1⟩⟩
        rintro rfl
        exact G.loopless e (h0.trans h1.symm)

omit [DecidableEq E] in
theorem exists_edge_of_mem_supportGraph_edgeSet (S : Finset E) {z : Sym2 V}
    (hz : z ∈ (G.supportGraph S).edgeSet) : ∃ e ∈ S, G.symEdge e = z := by
  classical
  have hz' : z ∈ (G.supportGraph S).edgeFinset := by
    simpa only [SimpleGraph.mem_edgeFinset] using hz
  rw [G.edgeFinset_supportGraph S] at hz'
  exact Finset.mem_image.mp hz'

omit [DecidableEq V] [DecidableEq E] in
theorem reachableIn_mono {S T : Finset E} (hST : S ⊆ T) {u v : V}
    (h : G.ReachableIn S u v) : G.ReachableIn T u v :=
  h.mono (G.supportGraph_mono hST)

omit [DecidableEq V] [DecidableEq E] in
theorem connects_mono {S T : Finset E} (hST : S ⊆ T) (h : G.Connects S) : G.Connects T :=
  h.mono (G.supportGraph_mono hST)

omit [DecidableEq V] [DecidableEq E] in
theorem internallyConnected_top_iff_connects [Nonempty V] (S : Finset E) :
    G.InternallyConnected S ⊤ ↔ G.Connects S := by
  constructor
  · intro h
    refine ⟨fun u v => ?_⟩
    have huv := h u v trivial
    rw [ReachableIn, G.insideEdges_top S u] at huv
    exact huv
  · intro h u v _
    rw [ReachableIn, G.insideEdges_top S u]
    exact h.preconnected u v

omit [DecidableEq V] [DecidableEq E] in
/-- The first refinement step of a prefix-of-trees colouring splits exactly along
the components of the residual class. -/
theorem first_partition_is_residual_components [Nonempty V] {k : ℕ}
    (χ : E → Fin (k + 1)) (hprefix : G.PrefixTrees χ) (hdisc : ¬ G.Connects (residualClass χ)) :
    G.kaiserPartition χ 1 = G.refineSetoid ⊤ (residualClass χ) := by
  have hlast : ¬ G.InternallyConnected (colorClass χ (Fin.last k)) ⊤ := by
    rw [G.internallyConnected_top_iff_connects]
    exact hdisc
  have hbefore : ∀ d : Fin (k + 1), d < Fin.last k →
      G.InternallyConnected (colorClass χ d) ⊤ := by
    intro d hd
    rcases Fin.eq_castSucc_or_eq_last d with ⟨j, rfl⟩ | rfl
    · exact (G.internallyConnected_top_iff_connects _).mpr (hprefix j).1
    · exact absurd hd (lt_irrefl _)
  have hcol : G.firstDisconnectedColor χ (⊤ : Setoid V) = some (Fin.last k) :=
    G.firstDisconnectedColor_eq_some_of_spec hlast hbefore
  have h1 : G.kaiserPartition χ 1 = G.refineOnce χ (⊤ : Setoid V) := by
    rw [kaiserPartition_succ, kaiserPartition_zero]
  rw [h1, G.refineOnce_of_some hcol]
  rfl

/-! ## The colour-swap exchange -/

/-- Swap the colours of two edge objects: Kaiser's exchange `T_c + e - e'`,
`T_k - e + e'`. -/
noncomputable def swapColor {k : ℕ} (χ : E → Fin k) (e e' : E) : E → Fin k :=
  Function.update (Function.update χ e (χ e')) e' (χ e)

omit [Fintype E] in
theorem swapColor_apply_left {k : ℕ} (χ : E → Fin k) {e e' : E} (h : e ≠ e') :
    swapColor χ e e' e = χ e' := by
  classical
  simp [swapColor, h]

omit [Fintype E] in
theorem swapColor_apply_right {k : ℕ} (χ : E → Fin k) (e e' : E) :
    swapColor χ e e' e' = χ e := by
  classical
  simp [swapColor]

omit [Fintype E] in
theorem swapColor_apply_of_ne {k : ℕ} (χ : E → Fin k) {e e' x : E} (hxe : x ≠ e)
    (hxe' : x ≠ e') : swapColor χ e e' x = χ x := by
  classical
  simp [swapColor, hxe, hxe']

theorem colorClass_swap_left {k : ℕ} (χ : E → Fin k) {e e' : E} (hee' : e ≠ e')
    (hcol : χ e ≠ χ e') :
    colorClass (swapColor χ e e') (χ e) = (colorClass χ (χ e)).erase e ∪ {e'} := by
  ext x
  rcases eq_or_ne x e with rfl | hxe
  · simp [mem_colorClass, swapColor_apply_left χ hee', hcol.symm, hee']
  · rcases eq_or_ne x e' with rfl | hxe'
    · simp [mem_colorClass, swapColor_apply_right, hcol.symm]
    · simp [mem_colorClass, swapColor_apply_of_ne χ hxe hxe', hxe, hxe']

theorem colorClass_swap_right {k : ℕ} (χ : E → Fin k) {e e' : E} (hee' : e ≠ e')
    (hcol : χ e ≠ χ e') :
    colorClass (swapColor χ e e') (χ e') = (colorClass χ (χ e')).erase e' ∪ {e} := by
  ext x
  rcases eq_or_ne x e with rfl | hxe
  · simp [mem_colorClass, swapColor_apply_left χ hee', hee', hcol]
  · rcases eq_or_ne x e' with rfl | hxe'
    · simp [mem_colorClass, swapColor_apply_right, hcol, hxe]
    · simp [mem_colorClass, swapColor_apply_of_ne χ hxe hxe', hxe, hxe']

theorem colorClass_swap_other {k : ℕ} (χ : E → Fin k) {e e' : E} {i : Fin k} (hee' : e ≠ e')
    (hi : i ≠ χ e) (hi' : i ≠ χ e') :
    colorClass (swapColor χ e e') i = colorClass χ i := by
  ext x
  rcases eq_or_ne x e with rfl | hxe
  · simp only [mem_colorClass, swapColor_apply_left χ hee']
    exact ⟨fun h => absurd h.symm hi', fun h => absurd h.symm hi⟩
  · rcases eq_or_ne x e' with rfl | hxe'
    · simp only [mem_colorClass, swapColor_apply_right]
      exact ⟨fun h => absurd h.symm hi, fun h => absurd h.symm hi'⟩
    · simp [mem_colorClass, swapColor_apply_of_ne χ hxe hxe']

/-! ## Walk transport lemmas -/

omit [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] in
/-- A relation that turns edges into routes turns routes into routes. -/
theorem reachable_of_adj_reachable {H K : SimpleGraph V}
    (hstep : ∀ {u v : V}, H.Adj u v → K.Reachable u v) {u v : V} (h : H.Reachable u v) :
    K.Reachable u v := by
  obtain ⟨p⟩ := h
  induction p with
  | nil => exact SimpleGraph.Reachable.refl _
  | cons hadj _ ih => exact (hstep hadj).trans ih

omit [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] in
/-- A vertex map that sends edges to routes sends routes to routes. Unlike a graph
homomorphism this permits an edge to collapse to a point, which is exactly what
contraction of an internal edge does. -/
theorem reachable_map_of_adj_reachable {W : Type*} {H : SimpleGraph V} {K : SimpleGraph W}
    (f : V → W) (hstep : ∀ {u v : V}, H.Adj u v → K.Reachable (f u) (f v)) {u v : V}
    (h : H.Reachable u v) : K.Reachable (f u) (f v) := by
  obtain ⟨p⟩ := h
  induction p with
  | nil => exact SimpleGraph.Reachable.refl _
  | cons hadj _ ih => exact (hstep hadj).trans ih

omit [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] in
/-- If every edge of the ambient graph has both ends in `s`, a walk starting in `s`
stays in `s`. -/
theorem walk_support_subset_of_adj {H : SimpleGraph V} {s : Set V} {u v : V} (p : H.Walk u v)
    (hu : u ∈ s) (hedge : ∀ {x y : V}, H.Adj x y → x ∈ s ∧ y ∈ s) : ∀ x ∈ p.support, x ∈ s := by
  induction p with
  | nil =>
      intro x hx
      rw [SimpleGraph.Walk.support_nil, List.mem_singleton] at hx
      exact hx ▸ hu
  | cons hadj p ih =>
      intro x hx
      rw [SimpleGraph.Walk.support_cons, List.mem_cons] at hx
      rcases hx with rfl | hx
      · exact (hedge hadj).1
      · exact ih (hedge hadj).2 x hx

omit [Fintype V] [DecidableEq V] in
/-- Acyclicity is inherited by subgraphs. This repository's Mathlib pin already
provides the fact as `SimpleGraph.IsAcyclic.anti`; it is re-exported here under
the name the rest of the port uses. -/
theorem isAcyclic_of_le {H K : SimpleGraph V} (hHK : H ≤ K) (hK : K.IsAcyclic) :
    H.IsAcyclic := hK.anti hHK

/-! ## Elementary cardinality facts -/

omit [DecidableEq V] in
theorem isCyclicEdge_mono {S T : Finset E} (hST : S ⊆ T) {e : E} (he : G.IsCyclicEdge S e) :
    G.IsCyclicEdge T e := by
  refine ⟨hST he.1, G.reachableIn_mono ?_ he.2⟩
  intro f hf
  obtain ⟨hne, hfS⟩ := Finset.mem_erase.mp hf
  exact Finset.mem_erase.mpr ⟨hne, hST hfS⟩

omit [DecidableEq V] [DecidableEq E] in
theorem component_card_le_vertex_card (S : Finset E) :
    Nat.card (G.supportGraph S).ConnectedComponent ≤ Fintype.card V := by
  have hsurj : Function.Surjective (G.supportGraph S).connectedComponentMk := by
    intro C
    induction C using SimpleGraph.ConnectedComponent.ind with
    | _ v => exact ⟨v, rfl⟩
  have hle := Nat.card_le_card_of_surjective _ hsurj
  simpa [Nat.card_eq_fintype_card] using hle

omit [Fintype E] in
theorem card_exchange {S : Finset E} {e e' : E} (he' : e' ∈ S) (he : e ∉ S) :
    ((S.erase e') ∪ {e}).card = S.card := by
  have hnot : e ∉ S.erase e' := fun h => he (Finset.mem_of_mem_erase h)
  have hpos : 0 < S.card := Finset.card_pos.mpr ⟨e', he'⟩
  rw [Finset.union_singleton, Finset.card_insert_of_notMem hnot,
    Finset.card_erase_of_mem he']
  omega

omit [DecidableEq V] in
theorem isSpanningTree_of_exchange {T : Finset E} {e e' : E} (hT : G.IsSpanningTree T)
    (he' : e' ∈ T) (he : e ∉ T) (hconn : G.Connects ((T.erase e') ∪ {e})) :
    G.IsSpanningTree ((T.erase e') ∪ {e}) := by
  refine ⟨hconn, ?_⟩
  rw [card_exchange he' he]
  exact hT.2

/-! ## Counting the classes of a setoid -/

/-- A class described by a chosen representative is the same finite type as the
corresponding fibre of the quotient map. -/
noncomputable def classFiberEquiv (P : Setoid V) (q : Quotient P) :
    {v : V // P v (Quotient.out q)} ≃ {v : V // Quotient.mk P v = q} where
  toFun v := ⟨v.1, by
    have h : Quotient.mk P v.1 = Quotient.mk P (Quotient.out q) := Quotient.sound v.2
    rw [h]
    exact Quotient.out_eq q⟩
  invFun v := ⟨v.1, by
    have h : Quotient.mk P v.1 = Quotient.mk P (Quotient.out q) := by
      rw [v.2, Quotient.out_eq]
    exact Quotient.exact h⟩
  left_inv _ := Subtype.ext rfl
  right_inv _ := Subtype.ext rfl

/-- The quotient fibres, tagged by their quotient point, reassemble into `V`. -/
noncomputable def quotientSigmaEquiv (P : Setoid V) :
    (Σ q : Quotient P, {v : V // Quotient.mk P v = q}) ≃ V where
  toFun x := x.2.1
  invFun v := ⟨Quotient.mk P v, v, rfl⟩
  left_inv x := by
    obtain ⟨q, v, hv⟩ := x
    cases hv
    rfl
  right_inv _ := rfl

omit [DecidableEq V] in
theorem sum_card_setoid_classes (P : Setoid V) :
    (∑ q : Quotient P, Nat.card {v : V // P v (Quotient.out q)}) = Fintype.card V := by
  classical
  calc (∑ q : Quotient P, Nat.card {v : V // P v (Quotient.out q)})
      = ∑ q : Quotient P, Nat.card {v : V // Quotient.mk P v = q} :=
        Finset.sum_congr rfl fun q _ => Nat.card_congr (classFiberEquiv P q)
    _ = Nat.card (Σ q : Quotient P, {v : V // Quotient.mk P v = q}) := Nat.card_sigma.symm
    _ = Nat.card V := Nat.card_congr (quotientSigmaEquiv P)
    _ = Fintype.card V := Nat.card_eq_fintype_card

/-! ## From a packing to a colouring -/

omit [Fintype E] [DecidableEq E] in
theorem packing_index_unique {k : ℕ} {T : Fin k → Finset E}
    (hdisj : ∀ i j, i ≠ j → Disjoint (T i) (T j)) {e : E} {i j : Fin k} (hei : e ∈ T i)
    (hej : e ∈ T j) : i = j := by
  by_contra hij
  exact Finset.disjoint_left.mp (hdisj i j hij) hei hej

/-- Colour every edge already used by a packing with its (unique) tree index and
send everything else to the new residual colour. -/
noncomputable def coloringOfPacking {k : ℕ} (T : Fin k → Finset E) : E → Fin (k + 1) :=
  fun e => if h : ∃ i : Fin k, e ∈ T i then (Classical.choose h).castSucc else Fin.last k

theorem colorClass_coloringOfPacking {k : ℕ} {T : Fin k → Finset E}
    (hdisj : ∀ i j, i ≠ j → Disjoint (T i) (T j)) (i : Fin k) :
    colorClass (coloringOfPacking T) i.castSucc = T i := by
  classical
  ext e
  rw [mem_colorClass]
  by_cases hex : ∃ j : Fin k, e ∈ T j
  · have hspec := Classical.choose_spec hex
    rw [coloringOfPacking, dif_pos hex]
    constructor
    · intro hEq
      have : Classical.choose hex = i := Fin.castSucc_injective _ hEq
      exact this ▸ hspec
    · intro he
      exact congrArg Fin.castSucc (packing_index_unique hdisj hspec he)
  · rw [coloringOfPacking, dif_neg hex]
    constructor
    · intro hEq
      exact absurd hEq.symm (Fin.castSucc_ne_last i)
    · intro he
      exact absurd ⟨i, he⟩ hex

end FiniteGraph

end CycleDoubleCover
