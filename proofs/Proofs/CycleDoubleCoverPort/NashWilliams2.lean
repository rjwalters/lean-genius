import Proofs.CycleDoubleCoverPort.NashWilliams

/-
# Cycle Double Cover port, step 4 (part 2): contraction, cyclic edges, spanning trees

Second slice of the port of upstream `CDCLean/NashWilliams.lean` (3,657 lines).
Part 1 landed as `Proofs/CycleDoubleCoverPort/NashWilliams.lean` in #43629 and
carries the whole vocabulary of Kaiser's proof of the Nash-Williams--Tutte
tree-packing theorem together with the lemma layers independent of the long
local-exchange argument.

This part opens the deferred layer, covering upstream lines ~801-1348: the
interaction between a partition and the multigraph it is imposed on
(contraction, internal connectedness), the theory of cyclic edges (edges lying
on a circuit), the forest inequality, and the extraction of a spanning tree from
a connected edge set.

## Provenance and licensing

Upstream: https://github.com/openai/cdc-lean, file `CDCLean/NashWilliams.lean`,
pinned at Lean `v4.31.0` / Mathlib `9a9483a92959bc92bd6a60176dd1fe597298c1f8`
(the same pin this repository uses). Original authorship is upstream's.

`openai/cdc-lean` carries **no license file**, so default copyright applies —
it is *not* public domain and its absence of a license is not a grant. The
operator recorded an explicit risk acceptance on #37507 (comment of 2026-08-03)
permitting vendoring with attribution; upstream is used here with attribution
under that accepted risk, pending any license grant.

That permission is not exercised by this file: **no upstream text is vendored
here**. Every declaration below is an *independent re-derivation* — the upstream
source was consulted only for the mathematical content (the shapes of the
definitions and the statements of the results) and every proof script was
written from scratch against this repository's Mathlib pin. Later parts of step
4 may vendor with attribution instead; such files will say so in their headers,
so vendored material stays distinguishable from our own work.

## Deviations from upstream (all statement-preserving)

* Upstream proves the two "lift a contracted route back to the multigraph"
  arguments (`connects_of_internal_of_quotient_connects` and
  `cyclicEdge_of_quotient_cyclic_of_internal`) by two near-identical ~80-line
  scripts. Here a single lemma `reachableIn_out_of_quotient_reachable` is
  proved once, parameterised by the edge set `R` used downstairs and by the set
  `F` of contracted edges the route is allowed to use; both applications are
  then three lines. Its hypotheses are exactly what the two call sites supply:
  `R` contains all edges internal to a class and all quotient edges of `F`.
* The "both ends of an inside edge stay in the class" step of
  `inside_induce_connected` is factored out as
  `mem_class_of_supportGraph_insideEdges_adj`, and the projection step of
  `quotientGraph_connected_of_connects` as
  `quotientGraph_adj_of_mem_crossingClass` /
  `quotient_reachable_of_supportGraph_adj`, so that both connectivity transfer
  theorems become short.
* `reachableIn_of_rel_of_internal` names the "`P`-related vertices are
  `S`-reachable" consequence of `InternallyConnected` that upstream re-derives
  inline at each use.

Statements needing decidable equality on `Quotient P` (which our Mathlib pin
cannot synthesise for a bare `Setoid`) are elaborated under `open Classical in`;
this affects only the erased instance arguments of `supportGraph` / `Connects`,
not the propositions themselves.

## Ported in this part

`mem_class_of_supportGraph_insideEdges_adj` (new), `inside_induce_connected`,
`quotientGraph_adj_of_mem_crossingClass` (new),
`quotient_reachable_of_supportGraph_adj` (new),
`quotientGraph_connected_of_connects`, `reachableIn_of_rel_of_internal` (new),
`insideEdges_subset_erase_of_crossing`, `reachableIn_out_of_quotient_reachable`
(new), `connects_of_internal_of_quotient_connects`,
`cyclicEdge_of_quotient_cyclic_of_internal`, `reachableIn_erase_of_cyclic`,
`componentSetoid_erase_eq_of_cyclic`, `component_card_lt_of_not_cyclic`,
`card_add_components_le_of_no_cyclic`,
`exists_cyclic_of_disconnected_of_card_ge`, `connects_erase_of_cyclic`,
`exists_isSpanningTree_subset_of_connects`,
`supportGraph_isTree_of_spanningTree`, `symEdge_injOn_of_spanningTree`.

## Still deferred (later parts of step 4)

`reachableIn_inside_of_walk_of_no_crossing`,
`exists_crossing_tree_edge_of_not_internal_reachable`,
`rel_of_reachableIn_inside`, `path_edge_ends_rel_start_of_no_crossing`, the
whole `*_exchange_of_path_edge` family, `refineSetoid_exchange_eq_of_path_internal`,
`prefixTrees_swap_of_path_edge`, the `residualComponents_swap_*` family,
`exists_internal_tree_subset`,
`crossingClass_card_eq_of_spanningTree_of_internal`,
`quotient_card_sub_one_le_crossingClass_card`,
`quotient_card_sub_one_le_crossingEdges_card`,
`satisfiesTreePackingCondition_of_hasTreePacking`,
`hasSuperfluousEdge_of_condition_of_disconnected`, the
`exists_*_level_tree_edge_*` family, `finiteLevelValue*`,
`kaiserPartition_eq_upto_of_min_exchange`, `HasSuperfluousLevel`,
`minSuperfluousLevel*`, `HasKaiserImprovementStep`,
`hasKaiserImprovementStep_of_condition`,
`exists_connected_residual_of_kaiser_step`, `hasTreePacking_of_kaiser_steps`,
`hasTreePacking_of_condition` and the headline `nashWilliamsTutte`.

There are no `sorry`s, no `native_decide`, and no `axiom` declarations here.
This file does **not** discharge `CycleDoubleCover.cycleDoubleCover_of_bridgeless`;
that is the final step of the port (see #37507).
-/

namespace CycleDoubleCover

namespace FiniteGraph

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
  (G : FiniteGraph V E)

/-! ## Internal connectedness as connectedness of an induced subgraph -/

omit [DecidableEq V] [DecidableEq E] in
/-- Every edge of the support graph of `G.insideEdges S P u` has both of its ends
in the `P`-class of `u`. -/
theorem mem_class_of_supportGraph_insideEdges_adj {S : Finset E} {P : Setoid V} {u a b : V}
    (hab : (G.supportGraph (G.insideEdges S P u)).Adj a b) : P a u ∧ P b u := by
  rw [G.supportGraph_adj_iff] at hab
  obtain ⟨-, e, he, hends⟩ := hab
  obtain ⟨-, h0, h1⟩ := G.mem_insideEdges.mp he
  rcases hends with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact ⟨h0, h1⟩
  · exact ⟨h1, h0⟩

omit [DecidableEq V] [DecidableEq E] in
/-- Internal connectedness of one edge set becomes ordinary connectedness once we
restrict to a single class of the partition. -/
theorem inside_induce_connected [Nonempty V] (S : Finset E) (P : Setoid V) (u : V)
    (hS : G.InternallyConnected S P) :
    ((G.supportGraph (G.insideEdges S P u)).induce {v : V | P v u}).Connected := by
  have huu : u ∈ {v : V | P v u} := P.refl' u
  haveI : Nonempty ({v : V | P v u} : Set V) := ⟨⟨u, huu⟩⟩
  refine { preconnected := ?_ }
  rintro ⟨x, hx⟩ ⟨y, hy⟩
  have hx' : P x u := hx
  have hy' : P y u := hy
  have hreach : (G.supportGraph (G.insideEdges S P u)).Reachable x y := by
    have h := hS x y (P.trans' hx' (P.symm' hy'))
    rwa [G.insideEdges_eq_of_rel (S := S) hx'] at h
  obtain ⟨p⟩ := hreach
  exact ⟨p.induce _ (walk_support_subset_of_adj p hx
    (fun hab => G.mem_class_of_supportGraph_insideEdges_adj hab))⟩

/-! ## Contraction: routes upstairs and downstairs -/

omit [DecidableEq V] [DecidableEq E] in
open Classical in
/-- A crossing edge object becomes a genuine edge of the contracted multigraph. -/
theorem quotientGraph_adj_of_mem_crossingClass (S : Finset E) (P : Setoid V) {e : E}
    (he : e ∈ G.crossingClass S P) :
    ((G.quotientGraph S P).supportGraph Finset.univ).Adj
      (Quotient.mk P (G.endAt e 0)) (Quotient.mk P (G.endAt e 1)) := by
  rw [(G.quotientGraph S P).supportGraph_adj_iff]
  refine ⟨?_, ⟨e, he⟩, Finset.mem_univ _, Or.inl ⟨rfl, rfl⟩⟩
  intro hq
  exact (G.mem_crossingClass.mp he).2 (Quotient.exact hq)

open Classical in
/-- Contraction sends an edge of the support graph either to an edge of the
contracted support graph or to a single point. -/
theorem quotient_reachable_of_supportGraph_adj (S : Finset E) (P : Setoid V) {x y : V}
    (hxy : (G.supportGraph S).Adj x y) :
    ((G.quotientGraph S P).supportGraph Finset.univ).Reachable
      (Quotient.mk P x) (Quotient.mk P y) := by
  classical
  rw [G.supportGraph_adj_iff] at hxy
  obtain ⟨-, e, heS, hends⟩ := hxy
  by_cases hcross : P (G.endAt e 0) (G.endAt e 1)
  · have hq : Quotient.mk P (G.endAt e 0) = Quotient.mk P (G.endAt e 1) :=
      Quotient.sound hcross
    rcases hends with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · rw [hq]
    · rw [hq]
  · have hadj := G.quotientGraph_adj_of_mem_crossingClass S P
      (G.mem_crossingClass.mpr ⟨heS, hcross⟩)
    rcases hends with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact hadj.reachable
    · exact hadj.reachable.symm

open Classical in
/-- Contracting the classes of a partition preserves connectedness. -/
theorem quotientGraph_connected_of_connects [Nonempty V] (S : Finset E) (P : Setoid V)
    (hS : G.Connects S) : (G.quotientGraph S P).Connects Finset.univ := by
  classical
  haveI : Nonempty (Quotient P) := ⟨Quotient.mk P (Classical.arbitrary V)⟩
  refine { preconnected := ?_ }
  intro q r
  obtain ⟨x, rfl⟩ := Quotient.exists_rep q
  obtain ⟨y, rfl⟩ := Quotient.exists_rep r
  exact reachable_map_of_adj_reachable (Quotient.mk P)
    (fun hab => G.quotient_reachable_of_supportGraph_adj S P hab) (hS.preconnected x y)

omit [DecidableEq V] [DecidableEq E] in
/-- If `S` joins up each class from the inside, then `P`-related vertices are
`S`-reachable. -/
theorem reachableIn_of_rel_of_internal {S : Finset E} {P : Setoid V}
    (hInt : G.InternallyConnected S P) {a b : V} (hab : P a b) : G.ReachableIn S a b :=
  G.reachableIn_mono (G.insideEdges_subset S P a) (hInt a b hab)

omit [DecidableEq V] in
/-- Edges internal to a class never coincide with a crossing edge, so they survive
its deletion. -/
theorem insideEdges_subset_erase_of_crossing {S : Finset E} {P : Setoid V} {e : E}
    (he : e ∈ G.crossingClass S P) (u : V) : G.insideEdges S P u ⊆ S.erase e := by
  intro f hf
  obtain ⟨hfS, h0, h1⟩ := G.mem_insideEdges.mp hf
  refine Finset.mem_erase.mpr ⟨?_, hfS⟩
  rintro rfl
  exact (G.mem_crossingClass.mp he).2 (P.trans' h0 (P.symm' h1))

omit [DecidableEq V] [DecidableEq E] in
open Classical in
/-- Lift a route of the contracted multigraph to a route of `G`, between chosen
representatives of the two endpoints.

The edge set `R` used downstairs is a parameter: it only has to contain every
edge internal to a class (`hIn`) and every edge object underlying a contracted
edge the route may use (`hF`). Taking `R = S`, `F = univ` gives the converse of
`quotientGraph_connected_of_connects`; taking `R = S.erase e`,
`F = univ.erase e` lifts circuits. -/
theorem reachableIn_out_of_quotient_reachable {S R : Finset E} {P : Setoid V}
    (hInt : G.InternallyConnected S P) (hIn : ∀ u : V, G.insideEdges S P u ⊆ R)
    {F : Finset {e : E // e ∈ G.crossingClass S P}} (hF : ∀ f ∈ F, f.1 ∈ R)
    {q r : Quotient P}
    (h : ((G.quotientGraph S P).supportGraph F).Reachable q r) :
    G.ReachableIn R (Quotient.out q) (Quotient.out r) := by
  classical
  have hstep : ∀ {x y : V}, P x y → G.ReachableIn R x y := fun {x _} hxy =>
    G.reachableIn_mono (hIn x) (hInt _ _ hxy)
  refine reachable_map_of_adj_reachable (H := (G.quotientGraph S P).supportGraph F)
    (K := G.supportGraph R) Quotient.out ?_ h
  intro a b hab
  rw [(G.quotientGraph S P).supportGraph_adj_iff] at hab
  obtain ⟨-, f, hfF, hends⟩ := hab
  have hadj : (G.supportGraph R).Adj (G.endAt f.1 0) (G.endAt f.1 1) := by
    rw [G.supportGraph_adj_iff]
    exact ⟨G.loopless f.1, f.1, hF f hfF, Or.inl ⟨rfl, rfl⟩⟩
  have h0 : P (Quotient.out (Quotient.mk P (G.endAt f.1 0))) (G.endAt f.1 0) :=
    Quotient.mk_out _
  have h1 : P (Quotient.out (Quotient.mk P (G.endAt f.1 1))) (G.endAt f.1 1) :=
    Quotient.mk_out _
  rcases hends with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact (hstep h0).trans (hadj.reachable.trans (hstep h1).symm)
  · exact (hstep h1).trans (hadj.reachable.symm.trans (hstep h0).symm)

open Classical in
/-- Converse of `quotientGraph_connected_of_connects` in the presence of internal
connectedness. -/
theorem connects_of_internal_of_quotient_connects [Nonempty V] (S : Finset E) (P : Setoid V)
    (hInt : G.InternallyConnected S P) (hQ : (G.quotientGraph S P).Connects Finset.univ) :
    G.Connects S := by
  classical
  refine { preconnected := ?_ }
  intro u v
  have hu : G.ReachableIn S u (Quotient.out (Quotient.mk P u)) :=
    G.reachableIn_of_rel_of_internal hInt (P.symm' (Quotient.mk_out u))
  have hv : G.ReachableIn S v (Quotient.out (Quotient.mk P v)) :=
    G.reachableIn_of_rel_of_internal hInt (P.symm' (Quotient.mk_out v))
  have hmid := G.reachableIn_out_of_quotient_reachable (R := S) hInt
    (G.insideEdges_subset S P) (F := Finset.univ)
    (fun f _ => (G.mem_crossingClass.mp f.2).1)
    (hQ.preconnected (Quotient.mk P u) (Quotient.mk P v))
  exact hu.trans (hmid.trans hv.symm)

open Classical in
/-- A circuit through a contracted edge lifts to a circuit through the underlying
edge object: the internal detours avoid it because it crosses the partition. -/
theorem cyclicEdge_of_quotient_cyclic_of_internal [Nonempty V] {S : Finset E} {P : Setoid V}
    (hInt : G.InternallyConnected S P) {e : {e : E // e ∈ G.crossingClass S P}}
    (he : (G.quotientGraph S P).IsCyclicEdge Finset.univ e) : G.IsCyclicEdge S e.1 := by
  classical
  refine ⟨(G.mem_crossingClass.mp e.2).1, ?_⟩
  have hstep : ∀ {x y : V}, P x y → G.ReachableIn (S.erase e.1) x y := fun {x _} hxy =>
    G.reachableIn_mono (G.insideEdges_subset_erase_of_crossing e.2 x) (hInt _ _ hxy)
  have hlift := G.reachableIn_out_of_quotient_reachable (R := S.erase e.1) hInt
    (G.insideEdges_subset_erase_of_crossing e.2)
    (F := Finset.univ.erase e)
    (fun f hf => Finset.mem_erase.mpr
      ⟨fun hEq => (Finset.mem_erase.mp hf).1 (Subtype.ext hEq),
        (G.mem_crossingClass.mp f.2).1⟩)
    he.2
  exact (hstep (P.symm' (Quotient.mk_out (G.endAt e.1 0)))).trans
    (hlift.trans (hstep (P.symm' (Quotient.mk_out (G.endAt e.1 1)))).symm)

/-! ## Cyclic edges -/

omit [DecidableEq V] in
/-- Deleting an edge that lies on a circuit destroys no reachability. -/
theorem reachableIn_erase_of_cyclic {S : Finset E} {e : E} (he : G.IsCyclicEdge S e) {u v : V}
    (h : G.ReachableIn S u v) : G.ReachableIn (S.erase e) u v := by
  have hstep : ∀ {x y : V}, (G.supportGraph S).Adj x y →
      (G.supportGraph (S.erase e)).Reachable x y := by
    intro x y hxy
    rw [G.supportGraph_adj_iff] at hxy
    obtain ⟨hne, f, hfS, hends⟩ := hxy
    by_cases hfe : f = e
    · subst hfe
      rcases hends with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact he.2
      · exact he.2.symm
    · refine SimpleGraph.Adj.reachable ?_
      rw [G.supportGraph_adj_iff]
      exact ⟨hne, f, Finset.mem_erase.mpr ⟨hfe, hfS⟩, hends⟩
  exact reachable_of_adj_reachable hstep h

omit [DecidableEq V] in
theorem componentSetoid_erase_eq_of_cyclic {S : Finset E} {e : E} (he : G.IsCyclicEdge S e) :
    G.componentSetoid (S.erase e) = G.componentSetoid S :=
  Setoid.ext fun _ _ =>
    ⟨fun h => G.reachableIn_mono (Finset.erase_subset _ _) h,
      fun h => G.reachableIn_erase_of_cyclic he h⟩

omit [DecidableEq V] in
/-- Deleting an edge that lies on no circuit strictly increases the number of
connected components. -/
theorem component_card_lt_of_not_cyclic [Nonempty V] {S : Finset E} {e : E} (heS : e ∈ S)
    (hnc : ¬ G.IsCyclicEdge S e) :
    Nat.card (G.supportGraph S).ConnectedComponent <
      Nat.card (G.supportGraph (S.erase e)).ConnectedComponent := by
  classical
  have hHK : G.supportGraph (S.erase e) ≤ G.supportGraph S :=
    G.supportGraph_mono (Finset.erase_subset _ _)
  haveI : Fintype (G.supportGraph (S.erase e)).ConnectedComponent := Fintype.ofFinite _
  haveI : Fintype (G.supportGraph S).ConnectedComponent := Fintype.ofFinite _
  have hsurj : Function.Surjective
      (SimpleGraph.ConnectedComponent.map (SimpleGraph.Hom.ofLE hHK)) :=
    SimpleGraph.ConnectedComponent.surjective_map_ofLE hHK
  have hnotinj : ¬ Function.Injective
      (SimpleGraph.ConnectedComponent.map (SimpleGraph.Hom.ofLE hHK)) := by
    intro hinj
    refine hnc ⟨heS, ?_⟩
    have hadj : (G.supportGraph S).Adj (G.endAt e 0) (G.endAt e 1) := by
      rw [G.supportGraph_adj_iff]
      exact ⟨G.loopless e, e, heS, Or.inl ⟨rfl, rfl⟩⟩
    have hmk : (G.supportGraph (S.erase e)).connectedComponentMk (G.endAt e 0)
        = (G.supportGraph (S.erase e)).connectedComponentMk (G.endAt e 1) := by
      apply hinj
      exact SimpleGraph.ConnectedComponent.eq.mpr hadj.reachable
    exact SimpleGraph.ConnectedComponent.eq.mp hmk
  have hlt := Fintype.card_lt_of_surjective_not_injective _ hsurj hnotinj
  simpa [Nat.card_eq_fintype_card] using hlt

/-- The forest inequality: a circuit-free set of edge objects satisfies
`#edges + #components ≤ #vertices`. -/
theorem card_add_components_le_of_no_cyclic [Nonempty V] (S : Finset E)
    (hno : ∀ e ∈ S, ¬ G.IsCyclicEdge S e) :
    S.card + Nat.card (G.supportGraph S).ConnectedComponent ≤ Fintype.card V := by
  classical
  induction S using Finset.induction_on with
  | empty => simpa using G.component_card_le_vertex_card (∅ : Finset E)
  | @insert e T heT ih =>
      have hnoT : ∀ f ∈ T, ¬ G.IsCyclicEdge T f := fun f hf hcyc =>
        hno f (Finset.mem_insert_of_mem hf)
          (G.isCyclicEdge_mono (Finset.subset_insert e T) hcyc)
      have hih := ih hnoT
      have hlt := G.component_card_lt_of_not_cyclic (S := insert e T) (e := e)
        (Finset.mem_insert_self e T) (hno e (Finset.mem_insert_self e T))
      rw [Finset.erase_insert heT] at hlt
      have hcard : (insert e T).card = T.card + 1 := Finset.card_insert_of_notMem heT
      omega

/-- A disconnected edge set with at least `|V| - 1` members must contain a circuit:
otherwise the forest inequality leaves no room for two components. -/
theorem exists_cyclic_of_disconnected_of_card_ge [Nonempty V] (S : Finset E)
    (hdisc : ¬ G.Connects S) (hcard : Fintype.card V - 1 ≤ S.card) :
    ∃ e : E, G.IsCyclicEdge S e := by
  classical
  by_contra hnone
  push Not at hnone
  have hforest := G.card_add_components_le_of_no_cyclic S fun e _ => hnone e
  have hcomp : 1 < Nat.card (G.supportGraph S).ConnectedComponent := by
    by_contra hle
    push Not at hle
    haveI : Subsingleton (G.supportGraph S).ConnectedComponent :=
      Finite.card_le_one_iff_subsingleton.mp hle
    refine hdisc { preconnected := fun u v => ?_ }
    exact SimpleGraph.ConnectedComponent.eq.mp (Subsingleton.elim _ _)
  have hVpos : 0 < Fintype.card V := Fintype.card_pos
  omega

omit [DecidableEq V] in
theorem connects_erase_of_cyclic [Nonempty V] {S : Finset E} {e : E}
    (he : G.IsCyclicEdge S e) (hS : G.Connects S) : G.Connects (S.erase e) :=
  { preconnected := fun u v => G.reachableIn_erase_of_cyclic he (hS.preconnected u v) }

/-! ## Extracting a spanning tree -/

/-- Every connected set of edge objects contains a spanning tree: take a simple
spanning tree of the support graph and lift each of its edges to one edge
object. -/
theorem exists_isSpanningTree_subset_of_connects [Nonempty V] (S : Finset E)
    (hS : G.Connects S) : ∃ T : Finset E, T ⊆ S ∧ G.IsSpanningTree T := by
  classical
  obtain ⟨H, hHle, hHtree⟩ := hS.exists_isTree_le
  haveI : Fintype H.edgeSet := Fintype.ofFinite _
  haveI : Fintype (G.supportGraph S).edgeSet := Fintype.ofFinite _
  have hchoice : ∀ z : H.edgeFinset, ∃ f : E, f ∈ S ∧ G.symEdge f = (z : Sym2 V) := by
    intro z
    have hz : (z : Sym2 V) ∈ (G.supportGraph S).edgeSet :=
      SimpleGraph.edgeSet_mono hHle (SimpleGraph.mem_edgeFinset.mp z.2)
    exact G.exists_edge_of_mem_supportGraph_edgeSet S hz
  choose φ hφS hφEq using hchoice
  refine ⟨Finset.univ.image φ, ?_, ?_, ?_⟩
  · intro f hf
    obtain ⟨z, -, rfl⟩ := Finset.mem_image.mp hf
    exact hφS z
  · haveI : Fintype (G.supportGraph (Finset.univ.image φ)).edgeSet := Fintype.ofFinite _
    refine hHtree.connected.mono ?_
    rw [← SimpleGraph.edgeFinset_subset_edgeFinset]
    intro z hz
    rw [G.edgeFinset_supportGraph (Finset.univ.image φ)]
    exact Finset.mem_image.mpr ⟨φ ⟨z, hz⟩,
      Finset.mem_image.mpr ⟨⟨z, hz⟩, Finset.mem_univ _, rfl⟩, hφEq _⟩
  · have hinj : Function.Injective φ := by
      intro z w hzw
      apply Subtype.ext
      rw [← hφEq z, ← hφEq w, hzw]
    rw [Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_coe]
    exact hHtree.card_edgeFinset

omit [DecidableEq E] in
/-- The support graph of a spanning tree is a simple tree: the edge-count bound
forces the support map to lose nothing. -/
theorem supportGraph_isTree_of_spanningTree [Nonempty V] {T : Finset E}
    (hT : G.IsSpanningTree T) : (G.supportGraph T).IsTree := by
  haveI : Fintype (G.supportGraph T).edgeSet := Fintype.ofFinite _
  rw [SimpleGraph.isTree_iff_connected_and_card]
  refine ⟨hT.1, ?_⟩
  have hle : (G.supportGraph T).edgeFinset.card ≤ T.card := by
    rw [G.edgeFinset_supportGraph T]
    exact Finset.card_image_le
  have hEdge : Nat.card (G.supportGraph T).edgeSet = (G.supportGraph T).edgeFinset.card := by
    rw [Nat.card_eq_fintype_card, SimpleGraph.edgeFinset_card]
  have hlow := hT.1.card_vert_le_card_edgeSet_add_one
  have hV : Nat.card V = Fintype.card V := Nat.card_eq_fintype_card
  have hTcard := hT.2
  omega

omit [DecidableEq E] in
/-- Distinct edge objects of a spanning tree have distinct end pairs. -/
theorem symEdge_injOn_of_spanningTree [Nonempty V] {T : Finset E}
    (hT : G.IsSpanningTree T) : Set.InjOn G.symEdge T := by
  haveI : Fintype (G.supportGraph T).edgeSet := Fintype.ofFinite _
  have htree := G.supportGraph_isTree_of_spanningTree hT
  refine Finset.card_image_iff.mp ?_
  have h1 : (T.image G.symEdge).card = (G.supportGraph T).edgeFinset.card := by
    rw [G.edgeFinset_supportGraph T]
  have h2 := htree.card_edgeFinset
  have h3 := hT.2
  omega

end FiniteGraph

end CycleDoubleCover
