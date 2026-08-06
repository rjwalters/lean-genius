import Proofs.Erdos85NonadjacentCloneSplit
import Proofs.Erdos85DeletePair
import Proofs.Erdos85LocalMatchingComponents

/-!
# Adjacent-clone splitting

This file isolates the exact graph-facing endpoint of the sharper adjacent
split.  A partition of the deleted vertex's neighbourhood must keep every
edge of the induced local matching on one side.  Once such a balanced
partition is supplied, the order-raising surgery is automatic.
-/

open SimpleGraph

namespace Erdos85

/-- The graph induced by the neighbours of `x`, represented after deleting
`x` from the ambient vertex type. -/
def deletedNeighborhoodInducedGraph
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (x : V) :
    SimpleGraph {y : {v : V // v ≠ x} //
      y ∈ (deletedNeighborhood G x : Set {v : V // v ≠ x})} :=
  (G.induce (fun v ↦ v ≠ x)).induce
    (fun y ↦ y ∈ (deletedNeighborhood G x : Set {v : V // v ≠ x}))

/-- Disjoint subsets of a deleted vertex's neighbourhood, with no edge
crossing between them, satisfy connected-pair attachment compatibility. -/
theorem adjacentCloneSelectors_compatible
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G) (x : V)
    (S T : Finset {v : V // v ≠ x})
    (hS : S ⊆ deletedNeighborhood G x)
    (hT : T ⊆ deletedNeighborhood G x)
    (hdisj : Disjoint S T)
    (hcross : ∀ ⦃a⦄, a ∈ S → ∀ ⦃b⦄, b ∈ T →
      ¬ (G.induce (setOf fun v => v ≠ x)).Adj a b) :
    PairedAttachmentCompatible (G.induce (setOf fun v => v ≠ x)) S T := by
  have hfull : CommonNeighborIndependent
      (G.induce (setOf fun v => v ≠ x))
      (deletedNeighborhood G x) := by
    intro a ha b hb hab
    rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
    intro z hz
    rw [Finset.mem_inter, mem_neighborFinset, mem_neighborFinset] at hz
    have hax : G.Adj a.1 x := (mem_deletedNeighborhood G x a).1 ha
    have hbx : G.Adj b.1 x := (mem_deletedNeighborhood G x b).1 hb
    exact hfree (containsC4_of_two_common
      (fun h => hab (Subtype.ext h))
      (fun h => z.2 h.symm)
      hax.symm hbx.symm hz.1.symm hz.2.symm)
  refine ⟨?_, ?_, ?_, hcross⟩
  · intro a ha b hb hab
    exact hfull (hS ha) (hS hb) hab
  · intro a ha b hb hab
    exact hfull (hT ha) (hT hb) hab
  · rw [Finset.card_le_one]
    intro a ha _b _hb
    exact False.elim ((Finset.disjoint_left.mp hdisj)
      (Finset.mem_inter.mp ha).1 (Finset.mem_inter.mp ha).2)

/-- **Balanced adjacent-clone split.**  A balanced union-cover of `N(x)`
which does not cut an edge of the induced neighbourhood raises the order by
one while preserving minimum degree and `C₄`-freeness. -/
theorem c4FreeMinDegreeWitness_succ_of_balanced_adjacentClone_partition
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (x : V)
    {N d : ℕ} (hVcard : Fintype.card V = N)
    (hmin : d ≤ G.minDegree) (hfree : ¬ containsC4 V G)
    (hd : 1 ≤ d)
    (S T : Finset {v : V // v ≠ x})
    (hS : S ⊆ deletedNeighborhood G x)
    (hT : T ⊆ deletedNeighborhood G x)
    (hdisj : Disjoint S T) (hcover : S ∪ T = deletedNeighborhood G x)
    (hScard : d - 1 ≤ S.card) (hTcard : d - 1 ≤ T.card)
    (hcross : ∀ ⦃a⦄, a ∈ S → ∀ ⦃b⦄, b ∈ T →
      ¬ (G.induce (setOf fun v => v ≠ x)).Adj a b) :
    C4FreeMinDegreeWitness (N + 1) d := by
  letI : Nonempty V := ⟨x⟩
  have hcard' : Fintype.card V = (N - 1) + 1 := by
    have hxcard : 1 ≤ N := by
      rw [← hVcard]
      exact Fintype.card_pos
    omega
  have hw := c4FreeMinDegreeWitness_delete_add_pair
    G x hcard' hmin hfree S T hScard hTcard hd
      (adjacentCloneSelectors_compatible G hfree x S T hS hT hdisj hcross)
      (fun y hy _ => by
        rw [hcover]
        exact (mem_deletedNeighborhood G x y).2 hy)
  convert hw using 1 <;> omega

/-- The local closure condition is exactly that no edge of `G[N(x)]` is cut
by the partition. -/
theorem noCross_iff_localMatching_edges_not_cut
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (x : V)
    (S T : Finset {v : V // v ≠ x}) :
    (∀ ⦃a⦄, a ∈ S → ∀ ⦃b⦄, b ∈ T →
      ¬ (G.induce (setOf fun v => v ≠ x)).Adj a b) ↔
    (∀ ⦃a⦄, a ∈ S → ∀ ⦃b⦄, b ∈ T → ¬ G.Adj a.1 b.1) := by
  rfl

/-- The graph induced by the surviving neighbours of a deleted vertex has
degree at most one: two distinct local neighbours would form a `C₄` together
with the deleted vertex. -/
theorem deletedNeighborhood_induced_degree_ncard_le_one
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G) (x : V)
    (z : {y : {v : V // v ≠ x} //
      y ∈ (deletedNeighborhood G x : Set {v : V // v ≠ x})}) :
    ((((G.induce (fun v ↦ v ≠ x)).induce
      (fun y ↦ y ∈ (deletedNeighborhood G x : Set {v : V // v ≠ x}))).neighborSet z).ncard) ≤ 1 := by
  classical
  rw [Set.ncard_le_one_iff_subsingleton]
  intro a ha b hb
  by_contra hab
  change G.Adj z.1.1 a.1.1 at ha
  change G.Adj z.1.1 b.1.1 at hb
  have hax : G.Adj a.1.1 x :=
    (mem_deletedNeighborhood G x a.1).1 a.2
  have hbx : G.Adj b.1.1 x :=
    (mem_deletedNeighborhood G x b.1).1 b.2
  apply hfree
  exact containsC4_of_two_common
    (fun h ↦ hab (Subtype.ext (Subtype.ext h)))
    (fun h ↦ z.1.2 h)
    ha hb hax.symm hbx.symm

theorem deletedNeighborhoodInducedGraph_degree_ncard_le_one
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G) (x : V)
    (z : {y : {v : V // v ≠ x} //
      y ∈ (deletedNeighborhood G x : Set {v : V // v ≠ x})}) :
    ((deletedNeighborhoodInducedGraph G x).neighborSet z).ncard ≤ 1 := by
  exact deletedNeighborhood_induced_degree_ncard_le_one G hfree x z

/-- **Sharp adjacent-clone split.**  If a `C₄`-free minimum-degree-`d`
graph has a vertex of degree at least `2*d-1`, split the local matching into
two intact balanced component unions and replace the vertex by an adjacent
pair.  This raises the order by one while preserving minimum degree `d`. -/
theorem c4FreeMinDegreeWitness_succ_of_vertex_degree_ge_two_mul_sub_one
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (x : V)
    {N d : ℕ} (hVcard : Fintype.card V = N)
    (hmin : d ≤ G.minDegree) (hfree : ¬ containsC4 V G)
    (hd : 1 ≤ d) (hxdegree : 2 * d - 1 ≤ G.degree x) :
    C4FreeMinDegreeWitness (N + 1) d := by
  classical
  let H : SimpleGraph {v : V // v ≠ x} := G.induce (fun v ↦ v ≠ x)
  let U : Finset {v : V // v ≠ x} := deletedNeighborhood G x
  have hUcard : 2 * (d - 1) + 1 ≤ U.card := by
    change 2 * (d - 1) + 1 ≤ (deletedNeighborhood G x).card
    rw [card_deletedNeighborhood]
    omega
  obtain ⟨S, T, hS, hT, hdisj, hcover, hScard, hTcard, hcross⟩ :=
    exists_balanced_noCross_partition_finset H U (d - 1)
      (deletedNeighborhood_induced_degree_ncard_le_one G hfree x) hUcard
  exact c4FreeMinDegreeWitness_succ_of_balanced_adjacentClone_partition
    G x hVcard hmin hfree hd S T hS hT hdisj hcover
      hScard hTcard hcross

/-- Contrapositive obstruction form of the sharp split: if this particular
witness cannot be extended by any construction, every one of its degrees is
at most `2*d-2`. -/
theorem degree_le_two_mul_sub_two_of_not_witness_succ
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {N d : ℕ} (hVcard : Fintype.card V = N)
    (hmin : d ≤ G.minDegree) (hfree : ¬ containsC4 V G)
    (hd : 1 ≤ d) (hno : ¬ C4FreeMinDegreeWitness (N + 1) d) :
    ∀ v, G.degree v ≤ 2 * d - 2 := by
  intro v
  by_contra hv
  have hvhigh : 2 * d - 1 ≤ G.degree v := by omega
  exact hno (c4FreeMinDegreeWitness_succ_of_vertex_degree_ge_two_mul_sub_one
    G v hVcard hmin hfree hd hvhigh)

/-- **Odd-parameter refinement.**  When `d` is odd, the target size `d-1`
is even, so a degree `2*d-2` neighbourhood already has an exact union of
local-matching components of size `d-1`. -/
theorem c4FreeMinDegreeWitness_succ_of_odd_vertex_degree_ge_two_mul_sub_two
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (x : V)
    {N d : ℕ} (hVcard : Fintype.card V = N)
    (hmin : d ≤ G.minDegree) (hfree : ¬ containsC4 V G)
    (hd : 1 ≤ d) (hdOdd : d % 2 = 1)
    (hxdegree : 2 * d - 2 ≤ G.degree x) :
    C4FreeMinDegreeWitness (N + 1) d := by
  classical
  let H : SimpleGraph {v : V // v ≠ x} := G.induce (fun v ↦ v ≠ x)
  let U : Finset {v : V // v ≠ x} := deletedNeighborhood G x
  have hUcard : 2 * (d - 1) ≤ U.card := by
    change 2 * (d - 1) ≤ (deletedNeighborhood G x).card
    rw [card_deletedNeighborhood]
    omega
  have heven : (d - 1) % 2 = 0 := by omega
  obtain ⟨S, T, hS, hT, hdisj, hcover, hScard, hTcard, hcross⟩ :=
    exists_balanced_noCross_partition_finset_of_even H U (d - 1)
      (deletedNeighborhood_induced_degree_ncard_le_one G hfree x)
      hUcard heven
  exact c4FreeMinDegreeWitness_succ_of_balanced_adjacentClone_partition
    G x hVcard hmin hfree hd S T hS hT hdisj hcover
      hScard hTcard hcross

/-- In a nonextendable odd-`d` witness, every degree is at most `2*d-3`. -/
theorem degree_le_two_mul_sub_three_of_odd_not_witness_succ
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {N d : ℕ} (hVcard : Fintype.card V = N)
    (hmin : d ≤ G.minDegree) (hfree : ¬ containsC4 V G)
    (hd : 1 ≤ d) (hdOdd : d % 2 = 1)
    (hno : ¬ C4FreeMinDegreeWitness (N + 1) d) :
    ∀ v, G.degree v ≤ 2 * d - 3 := by
  intro v
  by_contra hv
  have hvhigh : 2 * d - 2 ≤ G.degree v := by omega
  exact hno
    (c4FreeMinDegreeWitness_succ_of_odd_vertex_degree_ge_two_mul_sub_two
      G v hVcard hmin hfree hd hdOdd hvhigh)

/-- At degree `2*d-2`, a singleton component of the local matching removes
the parity obstruction and again permits adjacent-clone splitting. -/
theorem c4FreeMinDegreeWitness_succ_of_vertex_degree_ge_two_mul_sub_two_of_localSingleton
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (x : V)
    {N d : ℕ} (hVcard : Fintype.card V = N)
    (hmin : d ≤ G.minDegree) (hfree : ¬ containsC4 V G)
    (hd : 1 ≤ d) (hxdegree : 2 * d - 2 ≤ G.degree x)
    (hsingleton : ∃ c : (deletedNeighborhoodInducedGraph G x).ConnectedComponent,
      c.supp.ncard = 1) :
    C4FreeMinDegreeWitness (N + 1) d := by
  classical
  let H : SimpleGraph {v : V // v ≠ x} := G.induce (fun v ↦ v ≠ x)
  let U : Finset {v : V // v ≠ x} := deletedNeighborhood G x
  have hUcard : 2 * (d - 1) ≤ U.card := by
    change 2 * (d - 1) ≤ (deletedNeighborhood G x).card
    rw [card_deletedNeighborhood]
    omega
  have hs : ∃ c : (H.induce (fun y ↦ y ∈ (U : Set {v : V // v ≠ x}))).ConnectedComponent,
      c.supp.ncard = 1 := by
    change ∃ c : (deletedNeighborhoodInducedGraph G x).ConnectedComponent,
      c.supp.ncard = 1
    exact hsingleton
  obtain ⟨S, T, hS, hT, hdisj, hcover, hScard, hTcard, hcross⟩ :=
    exists_balanced_noCross_partition_finset_of_parity H U (d - 1)
      (deletedNeighborhood_induced_degree_ncard_le_one G hfree x)
      hUcard (Or.inr hs)
  exact c4FreeMinDegreeWitness_succ_of_balanced_adjacentClone_partition
    G x hVcard hmin hfree hd S T hS hT hdisj hcover
      hScard hTcard hcross

/-- Equality-case rigidity for a nonextendable witness: every local component
at a vertex of degree at least `2*d-2` has size two.  Equivalently, that
vertex's induced neighbourhood is a perfect matching. -/
theorem localComponents_eq_two_of_not_witness_succ_of_degree_ge_two_mul_sub_two
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (x : V)
    {N d : ℕ} (hVcard : Fintype.card V = N)
    (hmin : d ≤ G.minDegree) (hfree : ¬ containsC4 V G)
    (hd : 1 ≤ d) (hno : ¬ C4FreeMinDegreeWitness (N + 1) d)
    (hxdegree : 2 * d - 2 ≤ G.degree x) :
    ∀ c : (deletedNeighborhoodInducedGraph G x).ConnectedComponent,
      c.supp.ncard = 2 := by
  classical
  let K := deletedNeighborhoodInducedGraph G x
  have hdegreeK : ∀ z, K.degree z ≤ 1 := by
    intro z
    have heq : K.degree z = (K.neighborSet z).ncard := by
      rw [Set.ncard_eq_toFinset_card']
      rfl
    rw [heq]
    exact deletedNeighborhoodInducedGraph_degree_ncard_le_one G hfree x z
  intro c
  have hle := connectedComponent_supp_ncard_le_two_of_degree_le_one
    K hdegreeK c
  have hpos := c.nonempty_supp.ncard_pos
  by_contra hc
  have hone : c.supp.ncard = 1 := by omega
  exact hno
    (c4FreeMinDegreeWitness_succ_of_vertex_degree_ge_two_mul_sub_two_of_localSingleton
      G x hVcard hmin hfree hd hxdegree ⟨c, hone⟩)

end Erdos85
