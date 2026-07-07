import Mathlib.Data.Finset.Card
import Mathlib.Order.Antichain
import Mathlib.Tactic

/-
# Erdos Problem #1017 (OQ-05): Complete-Subhypergraph Cover vs Partition

## The Open Question
> Does the clique-cover / clique-partition problem extend naturally to
> hypergraphs?  For a `k`-uniform hypergraph, what is the minimum number of
> *complete sub-hypergraphs* needed to partition its edge set?

This is the `k`-uniform generalization of OQ-04 (`Erdos1017OQ04.lean`), which
treats the graph case `k = 2`.  In a graph, a *clique* is a vertex set all of
whose 2-subsets (pairs) are edges.  The uniform generalization is immediate:

* A **`k`-uniform hypergraph** `H` on `V` is a finite family of `k`-element
  vertex sets (its *hyperedges*).
* A **complete sub-hypergraph** is a vertex set `S` all of whose `k`-subsets are
  hyperedges of `H` -- the exact analog of a clique (`k = 2` recovers a clique:
  a vertex set all of whose pairs are edges).
* A **complete-subhypergraph cover** is a family of complete sub-hypergraphs such
  that every hyperedge lies inside (`⊆`) at least one of them; a **partition**
  requires *exactly one*.

Write `ccₖ(H)` for the minimum cover size and `cpₖ(H)` for the minimum partition
size.  OQ-04's always-true direction extends verbatim to every uniformity `k`:

    ccₖ(H) ≤ cpₖ(H).

## What This File Proves (0 axioms, 0 sorries)
- `Hypergraph`            : a `k`-uniform hypergraph (finite family of `k`-sets).
- `Hypergraph.IsCompleteSub` : the clique analog (every `k`-subset is a hyperedge).
- `CompleteCover` / `CompletePartition` : the cover and partition structures
  (edge contained in ≥ 1 / in exactly 1 complete sub-hypergraph).
- `CompletePartition.toCover` : every partition is a cover -- the structural heart
  of the always-true direction.
- `trivialPartition` : each hyperedge is its own complete sub-hypergraph, giving a
  partition that always exists (so `partitionNum` is a genuine minimum, not the
  vacuous `sInf ∅`).
- `coverNum_le_partitionNum` : **ccₖ(H) ≤ cpₖ(H)** for every `k`-uniform hypergraph.
- `partitionNum_le_edgesCard`, `coverNum_le_edgesCard` : both numbers are at most
  the number of hyperedges (each edge its own complete sub-hypergraph).
- `CompletePartition.edge_unique_clique` : the disjointness keystone -- a hyperedge
  lies in a UNIQUE partition clique -- on which every partition-number lower bound
  rests, and the reason `cpₖ` can exceed `ccₖ`.
- `coverNum_pos_of_edge`, `partitionNum_pos_of_edge` : both numbers are ≥ 1 once
  `H` has a hyperedge (base case of the lower-bound ladder).

## Honest Scope
This establishes the always-true direction `ccₖ ≤ cpₖ` rigorously for all `k` with
zero axioms, showing OQ-04's structure lifts cleanly to hypergraphs.  It does
**not** prove the gap can be strict for any fixed `k` (that requires a concrete
witness hypergraph and a counting lower bound, exactly as the strict graph gap
`K_4 - e` does at `k = 2`).  The strict `k`-uniform gap remains open here; the
keystone `edge_unique_clique` and the positivity base cases are the reusable
lemmas a future lower-bound argument builds on.
-/

set_option maxHeartbeats 400000

namespace Erdos1017OQ05

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V]

/-
====================================================================
PART I: HYPERGRAPHS AND COMPLETE SUB-HYPERGRAPHS
==================================================================== -/

/-- A **`k`-uniform hypergraph** on `V`: a finite family of hyperedges, each a
    `k`-element vertex set.  For `k = 2` this is (the edge set of) a graph. -/
structure Hypergraph (V : Type*) (k : ℕ) where
  /-- The hyperedges. -/
  edges : Finset (Finset V)
  /-- Every hyperedge has exactly `k` vertices. -/
  uniform : ∀ e ∈ edges, e.card = k

variable {k : ℕ} {H : Hypergraph V k}

/-- A vertex set `S` is a **complete sub-hypergraph** of `H` when every `k`-subset
    of `S` is a hyperedge of `H`.  This is the hypergraph analog of a clique: for
    `k = 2` it says every pair inside `S` is an edge. -/
def Hypergraph.IsCompleteSub (H : Hypergraph V k) (S : Finset V) : Prop :=
  ∀ ⦃e : Finset V⦄, e ⊆ S → e.card = k → e ∈ H.edges

/-- **Two `k`-sets nested by `⊆` are equal.**  If `e ⊆ f` and both have `k`
    vertices, then `e = f`.  This is the workhorse behind the trivial partition and
    the disjointness keystone. -/
theorem eq_of_subset_of_card_eq {e f : Finset V} (hsub : e ⊆ f)
    (he : e.card = k) (hf : f.card = k) : e = f :=
  Finset.eq_of_subset_of_card_le hsub (by rw [he, hf])

/-- **Every hyperedge is a complete sub-hypergraph.**  Viewing a hyperedge `e` as a
    vertex set, its only `k`-subset is `e` itself (both have `k` vertices), and `e`
    is a hyperedge.  This is what makes the trivial partition valid. -/
theorem isCompleteSub_of_mem_edges {e : Finset V} (he : e ∈ H.edges) :
    H.IsCompleteSub e := by
  intro f hf hfc
  rwa [eq_of_subset_of_card_eq hf hfc (H.uniform e he)]

/-
====================================================================
PART II: COVER AND PARTITION STRUCTURES
==================================================================== -/

/-- A **complete-subhypergraph cover** of `H`: a finite family of complete
    sub-hypergraphs such that every hyperedge lies inside at least one of them.
    Members may overlap. -/
structure CompleteCover (H : Hypergraph V k) where
  /-- The complete sub-hypergraphs in the cover. -/
  cliques : Finset (Finset V)
  /-- Each listed set is a complete sub-hypergraph of `H`. -/
  isComplete : ∀ S ∈ cliques, H.IsCompleteSub S
  /-- Every hyperedge is contained in some member. -/
  covers : ∀ ⦃e⦄, e ∈ H.edges → ∃ S ∈ cliques, e ⊆ S

/-- A **complete-subhypergraph partition** of `H`: every hyperedge is contained in
    *exactly one* complete sub-hypergraph.  This is a cover with the disjointness
    constraint, phrased as unique existence. -/
structure CompletePartition (H : Hypergraph V k) where
  /-- The complete sub-hypergraphs in the partition. -/
  cliques : Finset (Finset V)
  /-- Each listed set is a complete sub-hypergraph of `H`. -/
  isComplete : ∀ S ∈ cliques, H.IsCompleteSub S
  /-- Every hyperedge lies in exactly one member. -/
  partitions : ∀ ⦃e⦄, e ∈ H.edges → ∃! S, S ∈ cliques ∧ e ⊆ S

/-- **Every partition is a cover.**  Forgetting the uniqueness (disjointness)
    constraint turns a complete-subhypergraph partition into a cover with the same
    underlying family.  This is the structural core of `ccₖ(H) ≤ cpₖ(H)`. -/
def CompletePartition.toCover (P : CompletePartition H) : CompleteCover H where
  cliques := P.cliques
  isComplete := P.isComplete
  covers := by
    intro e he
    obtain ⟨S, ⟨hS, hsub⟩, _⟩ := P.partitions he
    exact ⟨S, hS, hsub⟩

@[simp] theorem CompletePartition.toCover_cliques (P : CompletePartition H) :
    P.toCover.cliques = P.cliques := rfl

/-
====================================================================
PART III: THE COVER AND PARTITION NUMBERS
==================================================================== -/

/-- The **complete-cover number** `ccₖ(H)`: the least size of a
    complete-subhypergraph cover. -/
noncomputable def coverNum (H : Hypergraph V k) : ℕ :=
  sInf { m | ∃ C : CompleteCover H, C.cliques.card = m }

/-- The **complete-partition number** `cpₖ(H)`: the least size of a
    complete-subhypergraph partition. -/
noncomputable def partitionNum (H : Hypergraph V k) : ℕ :=
  sInf { m | ∃ P : CompletePartition H, P.cliques.card = m }

/-
====================================================================
PART IV: THE TRIVIAL PARTITION (EACH HYPEREDGE ITS OWN CLIQUE)
==================================================================== -/

/-- The **trivial complete-subhypergraph partition**: every hyperedge is its own
    complete sub-hypergraph.  This witnesses that a partition of `H` always exists,
    so `partitionNum H` is achieved rather than a vacuous infimum. -/
noncomputable def trivialPartition (H : Hypergraph V k) : CompletePartition H where
  cliques := H.edges
  isComplete := fun _ hS => isCompleteSub_of_mem_edges hS
  partitions := by
    intro e he
    refine ⟨e, ⟨he, Finset.Subset.refl e⟩, ?_⟩
    -- Uniqueness: any hyperedge `S` (as a vertex set) containing `e` equals `e`.
    rintro S ⟨hS, hsub⟩
    exact (eq_of_subset_of_card_eq hsub (H.uniform e he) (H.uniform S hS)).symm

/-- The trivial partition uses one clique per hyperedge. -/
theorem trivialPartition_card (H : Hypergraph V k) :
    (trivialPartition H).cliques.card = H.edges.card := rfl

/-
====================================================================
PART V: THE MAIN INEQUALITY  ccₖ(H) ≤ cpₖ(H)
==================================================================== -/

/-- The partition-number witness set is nonempty: the trivial partition exists. -/
theorem partitionNum_set_nonempty (H : Hypergraph V k) :
    { m | ∃ P : CompletePartition H, P.cliques.card = m }.Nonempty :=
  ⟨(trivialPartition H).cliques.card, trivialPartition H, rfl⟩

/-- **Main result.** The complete-cover number is at most the complete-partition
    number: `ccₖ(H) ≤ cpₖ(H)` for every `k`-uniform hypergraph.  Every partition is
    a cover of the same size, so any minimum partition yields a cover of that size,
    whence the minimum cover size is at most it.  This lifts OQ-04's always-true
    direction from graphs (`k = 2`) to all uniformities. -/
theorem coverNum_le_partitionNum (H : Hypergraph V k) :
    coverNum H ≤ partitionNum H := by
  obtain ⟨P, hP⟩ := Nat.sInf_mem (partitionNum_set_nonempty H)
  refine Nat.sInf_le ?_
  exact ⟨P.toCover, by rw [CompletePartition.toCover_cliques]; exact hP⟩

/-
====================================================================
PART VI: UPPER BOUNDS BY THE NUMBER OF HYPEREDGES
==================================================================== -/

/-- `cpₖ(H) ≤ |edges|`: partition each hyperedge into its own complete
    sub-hypergraph. -/
theorem partitionNum_le_edgesCard (H : Hypergraph V k) :
    partitionNum H ≤ H.edges.card :=
  Nat.sInf_le ⟨trivialPartition H, rfl⟩

/-- `ccₖ(H) ≤ |edges|`: immediate from `ccₖ ≤ cpₖ ≤ |edges|`. -/
theorem coverNum_le_edgesCard (H : Hypergraph V k) :
    coverNum H ≤ H.edges.card :=
  (coverNum_le_partitionNum H).trans (partitionNum_le_edgesCard H)

/-
====================================================================
PART VII: TOWARD THE STRICT GAP  ccₖ(H) < cpₖ(H)

The always-true direction `ccₖ(H) ≤ cpₖ(H)` is Part V.  The genuinely open content
of OQ-05, mirroring OQ-04, is that this inequality can be *strict*.  The results
below are the reusable keystones for that lower-bound program, stated for arbitrary
`k`-uniform hypergraphs (no concrete witness yet).
==================================================================== -/

/-- **A hyperedge determines its partition clique uniquely.**  In a
    complete-subhypergraph *partition*, if a hyperedge `e` lies inside two listed
    cliques `S` and `T`, then `S = T`.  This is the disjointness distinguishing a
    partition from a cover, the structural obstruction behind a strict gap
    `ccₖ(H) < cpₖ(H)`, and the keystone for every partition-number lower bound. -/
theorem CompletePartition.edge_unique_clique (P : CompletePartition H)
    {e : Finset V} (he : e ∈ H.edges) {S T : Finset V}
    (hSmem : S ∈ P.cliques) (hSsub : e ⊆ S)
    (hTmem : T ∈ P.cliques) (hTsub : e ⊆ T) : S = T := by
  obtain ⟨_, _, huniq⟩ := P.partitions he
  rw [huniq S ⟨hSmem, hSsub⟩, huniq T ⟨hTmem, hTsub⟩]

/-- **`ccₖ(H) ≥ 1` whenever `H` has a hyperedge.**  A hyperedge must be covered by
    at least one complete sub-hypergraph, so the empty cover is invalid and the
    cover number is positive.  Base case of the cover-number lower-bound ladder. -/
theorem coverNum_pos_of_edge {e : Finset V} (he : e ∈ H.edges) : 0 < coverNum H := by
  have hne : {m | ∃ C : CompleteCover H, C.cliques.card = m}.Nonempty :=
    ⟨_, (trivialPartition H).toCover, rfl⟩
  obtain ⟨C, hC⟩ := Nat.sInf_mem hne
  have hC' : C.cliques.card = coverNum H := hC
  rcases Nat.eq_zero_or_pos (coverNum H) with h0 | hpos
  · exfalso
    rw [h0, Finset.card_eq_zero] at hC'
    obtain ⟨S, hS, _⟩ := C.covers he
    rw [hC'] at hS
    exact Finset.notMem_empty S hS
  · exact hpos

/-- **`cpₖ(H) ≥ 1` whenever `H` has a hyperedge.**  A hyperedge must lie in some
    clique of any partition, so the empty partition is invalid and the partition
    number is positive.  Base case of the partition-number lower-bound ladder. -/
theorem partitionNum_pos_of_edge {e : Finset V} (he : e ∈ H.edges) :
    0 < partitionNum H := by
  obtain ⟨P, hP⟩ := Nat.sInf_mem (partitionNum_set_nonempty H)
  have hP' : P.cliques.card = partitionNum H := hP
  rcases Nat.eq_zero_or_pos (partitionNum H) with h0 | hpos
  · exfalso
    rw [h0, Finset.card_eq_zero] at hP'
    obtain ⟨S, ⟨hS, _⟩, _⟩ := P.partitions he
    rw [hP'] at hS
    exact Finset.notMem_empty S hS
  · exact hpos

/-
====================================================================
PART VIII: SANITY CHECK — THE GRAPH CASE k = 2

For `k = 2` the definitions collapse to OQ-04's graph notions: a hyperedge is a
pair of vertices, a complete sub-hypergraph is a vertex set all of whose pairs are
edges (a clique), and the two extremal numbers are exactly `cc(G)` and `cp(G)`.
The following records that the uniform machinery specializes correctly: a `2`-set
is a complete sub-hypergraph iff it is a hyperedge.
==================================================================== -/

/-- At uniformity `k = 2`, a two-element vertex set is a complete sub-hypergraph iff
    it is itself a hyperedge -- matching the graph case, where a single edge is the
    smallest clique.  (One direction is `isCompleteSub_of_mem_edges`; this gives the
    converse for `2`-sets.) -/
theorem mem_edges_of_isCompleteSub_card_eq {H : Hypergraph V k} {S : Finset V}
    (hS : H.IsCompleteSub S) (hcard : S.card = k) : S ∈ H.edges :=
  hS (Finset.Subset.refl S) hcard

/-
====================================================================
PART IX: VERIFICATION
==================================================================== -/

#check @Hypergraph
#check @Hypergraph.IsCompleteSub
#check @CompleteCover
#check @CompletePartition
#check @CompletePartition.toCover
#check @coverNum
#check @partitionNum
#check @trivialPartition
#check @coverNum_le_partitionNum
#check @partitionNum_le_edgesCard
#check @coverNum_le_edgesCard
#check @CompletePartition.edge_unique_clique
#check @coverNum_pos_of_edge
#check @partitionNum_pos_of_edge
#check @mem_edges_of_isCompleteSub_card_eq

end Erdos1017OQ05

-- Axiom audit: expect only propext / Classical.choice / Quot.sound.
#print axioms Erdos1017OQ05.coverNum_le_partitionNum
#print axioms Erdos1017OQ05.partitionNum_le_edgesCard
#print axioms Erdos1017OQ05.mem_edges_of_isCompleteSub_card_eq
