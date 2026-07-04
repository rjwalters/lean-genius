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

## Honest Scope
This establishes the always-true direction `cc <= cp` rigorously and with zero
axioms. It does **not** prove the gap can be strict (that requires a lower-bound
argument on a concrete graph -- see the `nextSteps` in the knowledge file). The
strict gap is what shows OQ-04's strengthening genuinely fails; the book graph
`K_4` minus an edge is the intended witness (`cc = 2 < 3 = cp`).
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
PART VII: VERIFICATION
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

end Erdos1017OQ04
