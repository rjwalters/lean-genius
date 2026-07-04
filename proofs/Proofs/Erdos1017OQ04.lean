import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Data.Finset.Card
import Mathlib.Tactic

/-
# Erdos Problem #1017 (OQ-04): Clique Cover vs Clique Partition

## The Open Question
> Can Lovasz's covering result be strengthened to a *partition* result by
> controlling edge overlaps? The gap between the covering number and the
> partition number is not well understood.

An **edge clique cover** of a graph `G` is a collection of cliques such that
every edge lies in *at least one* clique (overlaps allowed). An **edge clique
partition** is the stronger notion: every edge lies in *exactly one* clique.

Write `cc(G)` for the minimum size of a cover and `cp(G)` for the minimum size
of a partition. The question of OQ-04 is whether a minimum cover can always be
converted into an equally small partition. The two numbers are genuinely
different quantities, and the *direction* that always holds is

    cc(G) <= cp(G).

## What This File Proves (0 axioms, 0 sorries)
- `EdgeCliqueCover`     : the covering structure (overlaps allowed).
- `EdgeCliquePartition` : the partition structure (each edge covered exactly
  once, via `ExistsUnique`).
- `EdgeCliquePartition.toCover` : every partition is a cover (forget
  disjointness). This is the structural heart of the "partition => cover"
  direction.
- `trivialPartition` : the partition of `G` into its individual edges, giving a
  witness that a partition always exists (so `partitionNum` is achieved, not the
  vacuous `sInf` of the empty set).
- `coverNum_le_partitionNum` : **cc(G) <= cp(G)** for every finite graph.
- `partitionNum_le_edgeCliquesCard`, `coverNum_le_edgeCliquesCard` : both numbers
  are at most the number of two-element cliques (each edge as its own clique).
- `EdgeCliquePartition.edge_unique_clique` : the edge-disjointness core of a
  partition (an edge lies in a unique partition clique) -- the keystone every
  partition-number lower bound is built on, and the structural reason `cp` can
  exceed `cc`. See Part VI.
- `coverNum_pos_of_edge`, `partitionNum_pos_of_edge` : both numbers are >= 1 once
  `G` has an edge (the base case of the lower-bound ladder toward the strict gap).

## Relation to OQ-01
The companion file `Erdos1017OQ01.lean` defines a structure it calls
`EdgeCliquePartition` whose only constraint is the `covers` field -- with no
disjointness requirement. That object is in fact an *edge clique cover* in the
terminology here, and its `cliquePartitionNum` is really `cc(G)`. This file
makes the cover/partition distinction explicit and pins down the inequality
relating the two, which is the well-defined mathematical content behind OQ-04's
"covering vs partition" gap.

## The Strict Gap (Part VII-VIII, 0 axioms, 0 sorries)
- `partition_card_choose_two_sum` : the **counting identity**
  `sum_{C in P} (C.card choose 2) = (edgeCliques G).card = |E(G)|` for every edge
  clique partition `P`. This is the quantitative keystone of every partition-number
  lower bound.
- `bookGraph` : the book graph `B2 = K_4 - e` on `Fin 4` (delete the edge `{2,3}`).
- `coverNum_bookGraph_le_two` : `cc(B2) <= 2` via the two-triangle cover.
- `partitionNum_bookGraph_ge_three` : `cp(B2) >= 3` via the counting identity
  (each clique has `<= 3` vertices, so each term is in `{0,1,3}`, and two such
  terms cannot sum to `5`).
- `coverNum_lt_partitionNum_bookGraph` : **`cc(B2) < cp(B2)`**, a fully verified
  strict gap. This answers OQ-04 in the negative: a minimum clique cover cannot in
  general be converted into an equally small partition.

## Honest Scope
Everything here is machine-checked with zero axioms and zero sorries. The result
`cc(B2) < cp(B2)` is an exact strict gap on a concrete graph, not merely the
always-true inequality `cc <= cp`. What remains open in the broader OQ-04 program
is the *quantitative* question of how large the gap `cp(G) - cc(G)` can be as a
function of `|V|` or `|E|`; the book graph only exhibits gap `>= 1`.
-/

set_option maxHeartbeats 400000

namespace Erdos1017OQ04

open Finset SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V]

/-
====================================================================
PART I: COVER AND PARTITION STRUCTURES
==================================================================== -/

/-- An **edge clique cover** of `G`: a finite collection of cliques such that
    every edge of `G` lies in at least one clique. Cliques may overlap. -/
structure EdgeCliqueCover (G : SimpleGraph V) [DecidableRel G.Adj] where
  /-- The cliques in the cover. -/
  cliques : Finset (Finset V)
  /-- Each listed set is a clique of `G`. -/
  isClique : ∀ S ∈ cliques, G.IsClique (↑S : Set V)
  /-- Every edge is covered by some clique. -/
  covers : ∀ ⦃v w⦄, G.Adj v w → ∃ S ∈ cliques, v ∈ S ∧ w ∈ S

/-- An **edge clique partition** of `G`: a finite collection of cliques such
    that every edge of `G` lies in *exactly one* clique. This is a cover with
    the additional (edge-)disjointness constraint, phrased as unique existence. -/
structure EdgeCliquePartition (G : SimpleGraph V) [DecidableRel G.Adj] where
  /-- The cliques in the partition. -/
  cliques : Finset (Finset V)
  /-- Each listed set is a clique of `G`. -/
  isClique : ∀ S ∈ cliques, G.IsClique (↑S : Set V)
  /-- Every edge lies in exactly one clique. -/
  partitions : ∀ ⦃v w⦄, G.Adj v w → ∃! S, S ∈ cliques ∧ v ∈ S ∧ w ∈ S

variable {G : SimpleGraph V} [DecidableRel G.Adj]

/-- **Every partition is a cover.** Forgetting the disjointness (uniqueness)
    constraint turns an edge clique partition into an edge clique cover with the
    same underlying set of cliques. This is the structural core of the
    always-true direction `cc(G) <= cp(G)`. -/
def EdgeCliquePartition.toCover (P : EdgeCliquePartition G) : EdgeCliqueCover G where
  cliques := P.cliques
  isClique := P.isClique
  covers := by
    intro v w hvw
    obtain ⟨S, ⟨hS, hv, hw⟩, _⟩ := P.partitions hvw
    exact ⟨S, hS, hv, hw⟩

@[simp] theorem EdgeCliquePartition.toCover_cliques (P : EdgeCliquePartition G) :
    P.toCover.cliques = P.cliques := rfl

/-
====================================================================
PART II: THE COVER AND PARTITION NUMBERS
==================================================================== -/

/-- The **clique cover number** `cc(G)`: the least number of cliques in an edge
    clique cover of `G`. -/
noncomputable def coverNum (G : SimpleGraph V) [DecidableRel G.Adj] : ℕ :=
  sInf { m | ∃ C : EdgeCliqueCover G, C.cliques.card = m }

/-- The **clique partition number** `cp(G)`: the least number of cliques in an
    edge clique partition of `G`. -/
noncomputable def partitionNum (G : SimpleGraph V) [DecidableRel G.Adj] : ℕ :=
  sInf { m | ∃ P : EdgeCliquePartition G, P.cliques.card = m }

/-
====================================================================
PART III: THE TRIVIAL PARTITION (EACH EDGE ITS OWN CLIQUE)
==================================================================== -/

/-- The collection of all two-element cliques of `G`, i.e. its edges viewed as
    two-element vertex sets. -/
noncomputable def edgeCliques (G : SimpleGraph V) [DecidableRel G.Adj] :
    Finset (Finset V) :=
  Finset.univ.filter (fun S => S.card = 2 ∧ G.IsClique (↑S : Set V))

/-- A pair `{v, w}` of adjacent vertices is a clique of `G`. -/
theorem isClique_pair {v w : V} (h : G.Adj v w) :
    G.IsClique (↑({v, w} : Finset V) : Set V) := by
  rw [SimpleGraph.isClique_iff, Finset.coe_insert, Finset.coe_singleton]
  intro x hx y hy hxy
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx hy
  rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
  · exact absurd rfl hxy
  · exact h
  · exact h.symm
  · exact absurd rfl hxy

/-- The cardinality of a pair of distinct elements is two. -/
theorem card_pair_eq_two {v w : V} (h : v ≠ w) :
    ({v, w} : Finset V).card = 2 := by
  rw [Finset.card_insert_of_not_mem (by rw [Finset.mem_singleton]; exact h)]
  simp

/-- Membership in `edgeCliques`: the two-element sets that are cliques are
    exactly the `{v, w}` with `v` and `w` adjacent. -/
theorem mem_edgeCliques {S : Finset V} :
    S ∈ edgeCliques G ↔ S.card = 2 ∧ G.IsClique (↑S : Set V) := by
  simp [edgeCliques]

/-- The **trivial edge clique partition**: every edge is its own clique. This
    witnesses that an edge clique partition of `G` always exists. -/
noncomputable def trivialPartition (G : SimpleGraph V) [DecidableRel G.Adj] :
    EdgeCliquePartition G where
  cliques := edgeCliques G
  isClique := by
    intro S hS
    exact (mem_edgeCliques.mp hS).2
  partitions := by
    intro v w hvw
    have hvw_ne : v ≠ w := hvw.ne
    have hcard : ({v, w} : Finset V).card = 2 := card_pair_eq_two hvw_ne
    refine ⟨{v, w}, ⟨?_, ?_, ?_⟩, ?_⟩
    · -- {v,w} is a two-element clique, hence in edgeCliques
      exact mem_edgeCliques.mpr ⟨hcard, isClique_pair hvw⟩
    · exact Finset.mem_insert_self v {w}
    · exact Finset.mem_insert_of_mem (Finset.mem_singleton_self w)
    · -- uniqueness: any two-element clique containing v and w equals {v,w}
      rintro S ⟨hS, hvS, hwS⟩
      have hSc : S.card = 2 := (mem_edgeCliques.mp hS).1
      have hsub : ({v, w} : Finset V) ⊆ S := by
        intro x hx
        rcases Finset.mem_insert.mp hx with rfl | hx
        · exact hvS
        · rw [Finset.mem_singleton] at hx; rw [hx]; exact hwS
      exact (Finset.eq_of_subset_of_card_le hsub (hSc.trans hcard.symm).le).symm

/-
====================================================================
PART IV: THE MAIN INEQUALITY  cc(G) <= cp(G)
==================================================================== -/

/-- The partition-number witness set is nonempty: the trivial partition exists. -/
theorem partitionNum_set_nonempty (G : SimpleGraph V) [DecidableRel G.Adj] :
    { m | ∃ P : EdgeCliquePartition G, P.cliques.card = m }.Nonempty :=
  ⟨(trivialPartition G).cliques.card, trivialPartition G, rfl⟩

/-- **Main result.** The clique cover number is at most the clique partition
    number: `cc(G) <= cp(G)`. Every partition is a cover of the same size, so any
    partition of size `cp(G)` gives a cover of size `cp(G)`, whence `cc(G)` (the
    minimum cover size) is at most `cp(G)`. -/
theorem coverNum_le_partitionNum (G : SimpleGraph V) [DecidableRel G.Adj] :
    coverNum G ≤ partitionNum G := by
  -- The partition number is achieved by some partition `P`.
  obtain ⟨P, hP⟩ := Nat.sInf_mem (partitionNum_set_nonempty G)
  -- `P.toCover` is a cover of the same size, so `partitionNum G` is a valid
  -- cover size, and `coverNum G` (an infimum) is at most it.
  refine Nat.sInf_le ?_
  exact ⟨P.toCover, by rw [EdgeCliquePartition.toCover_cliques]; exact hP⟩

/-
====================================================================
PART V: UPPER BOUNDS BY THE NUMBER OF EDGE-CLIQUES
==================================================================== -/

/-- The trivial partition uses exactly the two-element cliques, one per edge. -/
theorem trivialPartition_card (G : SimpleGraph V) [DecidableRel G.Adj] :
    (trivialPartition G).cliques.card = (edgeCliques G).card := rfl

/-- `cp(G) <= |edgeCliques G|`: partition each edge into its own clique. -/
theorem partitionNum_le_edgeCliquesCard (G : SimpleGraph V) [DecidableRel G.Adj] :
    partitionNum G ≤ (edgeCliques G).card :=
  Nat.sInf_le ⟨trivialPartition G, rfl⟩

/-- `cc(G) <= |edgeCliques G|`: immediate from `cc <= cp <= |edgeCliques|`. -/
theorem coverNum_le_edgeCliquesCard (G : SimpleGraph V) [DecidableRel G.Adj] :
    coverNum G ≤ (edgeCliques G).card :=
  (coverNum_le_partitionNum G).trans (partitionNum_le_edgeCliquesCard G)

/-
====================================================================
PART VI: TOWARD THE STRICT GAP  cc(G) < cp(G)

The always-true direction `cc(G) <= cp(G)` is Part IV.  The genuinely open
content of OQ-04 is that this inequality can be *strict*: converting a minimum
cover into a partition can force strictly more cliques.  The intended witness is
the book graph `K_4` minus an edge (`cc = 2 < 3 = cp`).

The results below are the reusable keystones for that lower-bound program, stated
for arbitrary graphs (no concrete witness yet):

* `EdgeCliquePartition.edge_unique_clique` : the *edge-disjointness* core of a
  partition -- an edge lies in a UNIQUE partition clique, so two partition
  cliques sharing an edge coincide.  This is exactly the property a cover lacks,
  and the structural reason `cp` can exceed `cc`.  It is the hypothesis every
  partition-number lower bound (including the counting identity
  `sum_{C} C(|C|,2) = |E|`) is built on.
* `coverNum_pos_of_edge` / `partitionNum_pos_of_edge` : both numbers are at least
  one once `G` has an edge (an edge cannot be covered by zero cliques) -- the base
  case of any lower-bound ladder.
==================================================================== -/

omit [Fintype V] [DecidableEq V] in
/-- **An edge determines its partition clique uniquely.**  In an edge clique
    *partition*, if an edge `{v, w}` (with `G.Adj v w`) lies in two listed cliques
    `S` and `T`, then `S = T`.  This is the edge-disjointness that distinguishes a
    partition from a cover: distinct partition cliques share no edge.  It is the
    structural obstruction behind a strict gap `cc(G) < cp(G)` and the keystone for
    every partition-number lower bound (e.g. the counting identity
    `sum_{C in P} C(|C|,2) = |E(G)|`). -/
theorem EdgeCliquePartition.edge_unique_clique (P : EdgeCliquePartition G)
    {v w : V} (hvw : G.Adj v w) {S T : Finset V}
    (hSmem : S ∈ P.cliques) (hvS : v ∈ S) (hwS : w ∈ S)
    (hTmem : T ∈ P.cliques) (hvT : v ∈ T) (hwT : w ∈ T) : S = T := by
  obtain ⟨_, _, huniq⟩ := P.partitions hvw
  rw [huniq S ⟨hSmem, hvS, hwS⟩, huniq T ⟨hTmem, hvT, hwT⟩]

/-- **`cc(G) >= 1` whenever `G` has an edge.**  An edge must be covered by at
    least one clique, so the empty cover is invalid and the cover number is
    positive.  Base case of the cover-number lower-bound ladder. -/
theorem coverNum_pos_of_edge {v w : V} (h : G.Adj v w) : 0 < coverNum G := by
  have hne : {m | ∃ C : EdgeCliqueCover G, C.cliques.card = m}.Nonempty :=
    ⟨_, (trivialPartition G).toCover, rfl⟩
  obtain ⟨C, hC⟩ := Nat.sInf_mem hne
  have hC' : C.cliques.card = coverNum G := hC
  rcases Nat.eq_zero_or_pos (coverNum G) with h0 | hpos
  · exfalso
    rw [h0, Finset.card_eq_zero] at hC'
    obtain ⟨S, hS, _, _⟩ := C.covers h
    rw [hC'] at hS
    exact Finset.notMem_empty S hS
  · exact hpos

/-- **`cp(G) >= 1` whenever `G` has an edge.**  An edge must lie in some clique of
    any partition, so the empty partition is invalid and the partition number is
    positive.  Base case of the partition-number lower-bound ladder. -/
theorem partitionNum_pos_of_edge {v w : V} (h : G.Adj v w) : 0 < partitionNum G := by
  obtain ⟨P, hP⟩ := Nat.sInf_mem (partitionNum_set_nonempty G)
  have hP' : P.cliques.card = partitionNum G := hP
  rcases Nat.eq_zero_or_pos (partitionNum G) with h0 | hpos
  · exfalso
    rw [h0, Finset.card_eq_zero] at hP'
    obtain ⟨S, ⟨hS, _, _⟩, _⟩ := P.partitions h
    rw [hP'] at hS
    exact Finset.notMem_empty S hS
  · exact hpos

/-
====================================================================
PART VII: THE COUNTING IDENTITY  sum_{C in P} C(|C|,2) = |E(G)|

This is the quantitative keystone of every clique-partition lower bound.
In an edge clique *partition* each edge lies in exactly one clique, and inside
a clique `C` every one of its `C(|C|,2)` vertex-pairs is an edge.  Summing the
internal edge-counts over the partition therefore counts each edge of `G`
exactly once:

    sum_{C in P.cliques} (C.card choose 2) = (edgeCliques G).card = |E(G)|.

Here `edgeCliques G` is the set of two-element cliques of `G`, i.e. its edges
represented as two-element vertex sets -- so `(edgeCliques G).card` is the
number of edges of `G`.  The whole identity is developed at this level, avoiding
`Sym2` entirely: the internal edges of a clique `C` are exactly the members of
`C.powersetCard 2`, and the partition property makes the union over cliques a
*disjoint* union covering `edgeCliques G`.
==================================================================== -/

/-- Two mutually-adjacent (distinct) vertices of a clique are adjacent in `G`.
    A convenience unfolding of `IsClique` (which is `Set.Pairwise G.Adj`). -/
theorem adj_of_mem_clique {C : Finset V} (hC : G.IsClique (↑C : Set V))
    {v w : V} (hv : v ∈ C) (hw : w ∈ C) (hvw : v ≠ w) : G.Adj v w :=
  hC (Finset.mem_coe.mpr hv) (Finset.mem_coe.mpr hw) hvw

/-- **Every two-element subset of a clique is an edge.**  If `C` is a clique of
    `G`, each of its `C(|C|,2)` two-element subsets is itself a two-element clique,
    hence a member of `edgeCliques G`. -/
theorem powersetCard_two_subset_edgeCliques {C : Finset V}
    (hC : G.IsClique (↑C : Set V)) : C.powersetCard 2 ⊆ edgeCliques G := by
  intro S hS
  rw [Finset.mem_powersetCard] at hS
  obtain ⟨hSsub, hScard⟩ := hS
  rw [mem_edgeCliques]
  exact ⟨hScard, hC.subset (Finset.coe_subset.mpr hSsub)⟩

/-- **The partition cliques carve `edgeCliques G` into disjoint two-subset blocks.**
    Every edge (two-element clique) of `G` is a two-element subset of exactly one
    partition clique, so `edgeCliques G` is the (disjoint) union over `P.cliques`
    of the two-element subsets of each clique. -/
theorem edgeCliques_eq_biUnion (P : EdgeCliquePartition G) :
    edgeCliques G = P.cliques.biUnion (fun C => C.powersetCard 2) := by
  ext S
  simp only [Finset.mem_biUnion]
  constructor
  · intro hS
    rw [mem_edgeCliques] at hS
    obtain ⟨hScard, hSclique⟩ := hS
    obtain ⟨v, w, hvw, rfl⟩ := Finset.card_eq_two.mp hScard
    have hadj : G.Adj v w :=
      adj_of_mem_clique hSclique (Finset.mem_insert_self v {w})
        (Finset.mem_insert_of_mem (Finset.mem_singleton_self w)) hvw
    obtain ⟨C, ⟨hCmem, hvC, hwC⟩, _⟩ := P.partitions hadj
    refine ⟨C, hCmem, ?_⟩
    rw [Finset.mem_powersetCard]
    refine ⟨?_, hScard⟩
    intro x hx
    rcases Finset.mem_insert.mp hx with rfl | hx
    · exact hvC
    · rw [Finset.mem_singleton] at hx; rw [hx]; exact hwC
  · rintro ⟨C, hCmem, hSC⟩
    exact powersetCard_two_subset_edgeCliques (P.isClique C hCmem) hSC

/-- **The two-subset blocks of distinct partition cliques are disjoint.**  If a
    two-element set `{v, w}` lies in two partition cliques `C` and `D`, then the
    edge `{v, w}` is common to both, so `edge_unique_clique` forces `C = D`.  This
    is where the partition (as opposed to cover) hypothesis is used. -/
theorem powersetCard_two_pairwiseDisjoint (P : EdgeCliquePartition G) :
    (P.cliques : Set (Finset V)).PairwiseDisjoint (fun C => C.powersetCard 2) := by
  intro C hC D hD hCD
  simp only [Finset.mem_coe] at hC hD
  show Disjoint (C.powersetCard 2) (D.powersetCard 2)
  rw [Finset.disjoint_left]
  intro S hSC hSD
  rw [Finset.mem_powersetCard] at hSC hSD
  obtain ⟨hSsubC, hScard⟩ := hSC
  obtain ⟨hSsubD, _⟩ := hSD
  obtain ⟨v, w, hvw, rfl⟩ := Finset.card_eq_two.mp hScard
  have hvC : v ∈ C := hSsubC (Finset.mem_insert_self v {w})
  have hwC : w ∈ C := hSsubC (Finset.mem_insert_of_mem (Finset.mem_singleton_self w))
  have hvD : v ∈ D := hSsubD (Finset.mem_insert_self v {w})
  have hwD : w ∈ D := hSsubD (Finset.mem_insert_of_mem (Finset.mem_singleton_self w))
  have hadj : G.Adj v w := adj_of_mem_clique (P.isClique C hC) hvC hwC hvw
  exact hCD (P.edge_unique_clique hadj hC hvC hwC hD hvD hwD)

/-- **The clique-partition counting identity.**  For any edge clique partition `P`
    of `G`,

        sum_{C in P.cliques} (C.card choose 2) = (edgeCliques G).card = |E(G)|.

    Each clique `C` contributes its `C(|C|,2)` internal edges, and the partition
    property guarantees these blocks are disjoint and exhaust every edge.  This
    turns clique-partition lower bounds into arithmetic: any bound on the possible
    clique sizes bounds the number of cliques needed to reach `|E(G)|`. -/
theorem partition_card_choose_two_sum (P : EdgeCliquePartition G) :
    ∑ C ∈ P.cliques, C.card.choose 2 = (edgeCliques G).card := by
  rw [edgeCliques_eq_biUnion P,
      Finset.card_biUnion (powersetCard_two_pairwiseDisjoint P)]
  exact Finset.sum_congr rfl (fun C _ => (Finset.card_powersetCard 2 C).symm)

/-
====================================================================
PART VIII: A VERIFIED STRICT GAP  cc(G) < cp(G)  (BOOK GRAPH K4 - e)

The always-true direction `cc(G) <= cp(G)` (Part IV) can be *strict*: this
answers OQ-04 in the negative -- a minimum cover cannot in general be converted
into an equally small partition.  The witness is the **book graph**
`B2 = K4 - e`, the complete graph on `{0,1,2,3}` with the single edge `{2,3}`
removed.  It has `5` edges and its two triangles `{0,1,2}`, `{0,1,3}` overlap on
the edge `{0,1}`:

* `cc(B2) <= 2`: the two triangles cover all `5` edges (`bookCover`).
* `cp(B2) >= 3`: a partition cannot use both triangles (they share `{0,1}`), and
  by the counting identity its cliques' sizes must satisfy
  `sum (C(|C|,2)) = 5`.  Every clique has `<= 3` vertices (no `K4`, since `2,3`
  are non-adjacent), so each term is in `{0,1,3}`; two such terms never sum to
  `5`, forcing at least `3` cliques.

Hence `cc(B2) <= 2 < 3 <= cp(B2)`, a *verified* strict gap.
==================================================================== -/

/-- The **book graph** `B2 = K4 - e`: the complete graph on `Fin 4` with the edge
    `{2, 3}` deleted.  Two vertices are adjacent iff they are distinct and not the
    removed pair `{2, 3}`. -/
def bookGraph : SimpleGraph (Fin 4) where
  Adj a b := a ≠ b ∧ ¬ (a = 2 ∧ b = 3) ∧ ¬ (a = 3 ∧ b = 2)
  symm := by
    intro a b h
    exact ⟨h.1.symm, fun hc => h.2.2 ⟨hc.2, hc.1⟩, fun hc => h.2.1 ⟨hc.2, hc.1⟩⟩
  loopless := by intro a h; exact h.1 rfl

instance : DecidableRel bookGraph.Adj := fun a b =>
  inferInstanceAs (Decidable (a ≠ b ∧ ¬ (a = 2 ∧ b = 3) ∧ ¬ (a = 3 ∧ b = 2)))

/-- **The two triangles cover `B2`.**  `{0,1,2}` and `{0,1,3}` are triangles whose
    union covers all five edges, so they form an edge clique cover of size `2`. -/
def bookCover : EdgeCliqueCover bookGraph where
  cliques := {{0, 1, 2}, {0, 1, 3}}
  isClique := by decide
  covers := by decide

/-- **`cc(B2) <= 2`.**  The two-triangle cover witnesses that the cover number is
    at most `2`. -/
theorem coverNum_bookGraph_le_two : coverNum bookGraph ≤ 2 :=
  Nat.sInf_le ⟨bookCover, by decide⟩

/-- **No clique of `B2` has more than three vertices.**  A four-vertex clique would
    be all of `{0,1,2,3}`, forcing `2` and `3` adjacent -- but that edge was
    deleted.  This caps each term of the counting identity at `C(3,2) = 3`. -/
theorem bookGraph_clique_card_le_three {C : Finset (Fin 4)}
    (hC : bookGraph.IsClique (↑C : Set (Fin 4))) : C.card ≤ 3 := by
  by_contra h
  push_neg at h
  have hub : C.card ≤ 4 := by have := Finset.card_le_univ C; simpa using this
  have h4 : C.card = 4 := by omega
  have huniv : C = Finset.univ :=
    Finset.eq_univ_of_card C (by rw [h4, Fintype.card_fin])
  have h2 : (2 : Fin 4) ∈ C := by rw [huniv]; exact Finset.mem_univ _
  have h3 : (3 : Fin 4) ∈ C := by rw [huniv]; exact Finset.mem_univ _
  have hadj : bookGraph.Adj 2 3 := adj_of_mem_clique hC h2 h3 (by decide)
  exact absurd hadj (by decide)

/-- **Any edge clique partition of `B2` uses at least three cliques.**  By the
    counting identity `sum (C(|C|,2)) = |E(B2)| = 5`, with each clique of size
    `<= 3` so each term in `{0,1,3}`.  A finset of at most two such terms cannot
    sum to `5`, so the partition has at least three cliques. -/
theorem bookGraph_partition_card_ge_three (P : EdgeCliquePartition bookGraph) :
    3 ≤ P.cliques.card := by
  have hsum : ∑ C ∈ P.cliques, C.card.choose 2 = 5 := by
    rw [partition_card_choose_two_sum P]; decide
  have hf : ∀ C ∈ P.cliques,
      C.card.choose 2 = 0 ∨ C.card.choose 2 = 1 ∨ C.card.choose 2 = 3 := by
    intro C hC
    have hle : C.card ≤ 3 := bookGraph_clique_card_le_three (P.isClique C hC)
    have : C.card = 0 ∨ C.card = 1 ∨ C.card = 2 ∨ C.card = 3 := by omega
    rcases this with h | h | h | h <;> rw [h] <;> decide
  by_contra hlt
  push_neg at hlt
  rcases (show P.cliques.card = 0 ∨ P.cliques.card = 1 ∨ P.cliques.card = 2
      from by omega) with h | h | h
  · rw [Finset.card_eq_zero] at h
    rw [h, Finset.sum_empty] at hsum
    exact absurd hsum (by decide)
  · obtain ⟨a, ha⟩ := Finset.card_eq_one.mp h
    have hmem : a ∈ P.cliques := by rw [ha]; exact Finset.mem_singleton_self a
    rw [ha, Finset.sum_singleton] at hsum
    rcases hf a hmem with h1 | h1 | h1 <;> omega
  · obtain ⟨a, b, hab, hs⟩ := Finset.card_eq_two.mp h
    have hma : a ∈ P.cliques := by rw [hs]; exact Finset.mem_insert_self a {b}
    have hmb : b ∈ P.cliques := by
      rw [hs]; exact Finset.mem_insert_of_mem (Finset.mem_singleton_self b)
    rw [hs, Finset.sum_pair hab] at hsum
    rcases hf a hma with h1 | h1 | h1 <;> rcases hf b hmb with h2 | h2 | h2 <;> omega

/-- **`cp(B2) >= 3`.**  Every partition of `B2` uses at least three cliques, so the
    partition number (the minimum such count) is at least `3`. -/
theorem partitionNum_bookGraph_ge_three : 3 ≤ partitionNum bookGraph := by
  obtain ⟨P, hP⟩ := Nat.sInf_mem (partitionNum_set_nonempty bookGraph)
  rw [show partitionNum bookGraph = P.cliques.card from hP.symm]
  exact bookGraph_partition_card_ge_three P

/-- **Verified strict gap `cc(B2) < cp(B2)`.**  Combining `cc(B2) <= 2` with
    `cp(B2) >= 3` gives `cc(B2) <= 2 < 3 <= cp(B2)`.  This is a fully machine-checked
    (0 axioms, 0 sorries) counterexample to strengthening the cover inequality to a
    partition equality -- the negative answer to OQ-04. -/
theorem coverNum_lt_partitionNum_bookGraph :
    coverNum bookGraph < partitionNum bookGraph :=
  lt_of_le_of_lt coverNum_bookGraph_le_two
    (lt_of_lt_of_le (by norm_num) partitionNum_bookGraph_ge_three)

/-
====================================================================
PART IX: VERIFICATION
==================================================================== -/

#check @EdgeCliqueCover
#check @EdgeCliquePartition
#check @EdgeCliquePartition.toCover
#check @coverNum
#check @partitionNum
#check @trivialPartition
#check @coverNum_le_partitionNum
#check @partitionNum_le_edgeCliquesCard
#check @coverNum_le_edgeCliquesCard
#check @EdgeCliquePartition.edge_unique_clique
#check @coverNum_pos_of_edge
#check @partitionNum_pos_of_edge
#check @partition_card_choose_two_sum
#check @bookGraph
#check @coverNum_bookGraph_le_two
#check @partitionNum_bookGraph_ge_three
#check @coverNum_lt_partitionNum_bookGraph

end Erdos1017OQ04
