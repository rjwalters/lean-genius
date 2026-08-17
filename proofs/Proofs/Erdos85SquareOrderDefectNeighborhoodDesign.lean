import Proofs.Erdos85ExteriorDefectDecomposition
import Proofs.Erdos85SquareOrderSectorProfile
import Proofs.Erdos85SquareOrderDefectIncidence

/-!
# Original neighborhoods as a design on the defect complement

For a `C₄`-free graph, the neighborhoods of the original graph are not
arbitrary subsets of the second-order defect graph.  Each is defect-independent,
and every distinct defect nonedge lies in exactly one neighborhood.  At square
order the blocks all have size `d` or `d+1`.

This is the vertex-level structure absent from incidence-count and spectral
relaxations of the nonregular square-order problem.
-/

open SimpleGraph

namespace Erdos85

noncomputable section

def squareOrderDefectOwnerBlock
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (z : V) : Finset V :=
  G.neighborFinset z

def squareOrderDefectBranch
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (u z : V) : Finset V :=
  (G.neighborFinset z).erase u

def squareOrderDefectNonneighbors
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (u : V) : Finset V :=
  (Finset.univ.erase u) \ (secondOrderDefectGraph G).neighborFinset u

/-- Two distinct points in one original neighborhood cannot be adjacent in
the second-order defect graph. -/
theorem not_defectAdj_of_mem_squareOrderDefectOwnerBlock
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) {z u v : V}
    (hu : u ∈ squareOrderDefectOwnerBlock G z)
    (hv : v ∈ squareOrderDefectOwnerBlock G z) (huv : u ≠ v) :
    ¬ (secondOrderDefectGraph G).Adj u v := by
  intro hD
  have hzero :=
    (secondOrderDefectGraph_adj_iff_card_common_eq_zero G hfree huv).mp hD
  have hzmem : z ∈ G.neighborFinset u ∩ G.neighborFinset v := by
    simp only [Finset.mem_inter, SimpleGraph.mem_neighborFinset]
    constructor
    · simpa [squareOrderDefectOwnerBlock, G.adj_comm,
        SimpleGraph.mem_neighborFinset] using hu
    · simpa [squareOrderDefectOwnerBlock, G.adj_comm,
        SimpleGraph.mem_neighborFinset] using hv
  have hpos : 0 < (G.neighborFinset u ∩ G.neighborFinset v).card :=
    Finset.card_pos.mpr ⟨z, hzmem⟩
  omega

/-- Every distinct defect nonedge has a unique owner: its unique common
neighbor in the original graph. -/
theorem existsUnique_squareOrderDefectOwner_of_not_adj
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) {u v : V} (huv : u ≠ v)
    (hnot : ¬ (secondOrderDefectGraph G).Adj u v) :
    ∃! z : V, u ∈ squareOrderDefectOwnerBlock G z ∧
      v ∈ squareOrderDefectOwnerBlock G z := by
  have hcard := card_common_eq_if_secondOrderDefect G hfree u v huv
  have hnotmem :
      v ∉ (secondOrderDefectGraph G).neighborFinset u := by
    simpa [SimpleGraph.mem_neighborFinset] using hnot
  rw [if_neg hnotmem] at hcard
  obtain ⟨z, hz⟩ := Finset.card_eq_one.mp hcard
  have hzmem : z ∈ G.neighborFinset u ∩ G.neighborFinset v := by
    rw [hz]
    simp
  refine ⟨z, ?_, ?_⟩
  · constructor
    · simpa [squareOrderDefectOwnerBlock, G.adj_comm,
        SimpleGraph.mem_neighborFinset] using (Finset.mem_inter.mp hzmem).1
    · simpa [squareOrderDefectOwnerBlock, G.adj_comm,
        SimpleGraph.mem_neighborFinset] using (Finset.mem_inter.mp hzmem).2
  · intro w hw
    have hwmem : w ∈ G.neighborFinset u ∩ G.neighborFinset v := by
      simp only [Finset.mem_inter, SimpleGraph.mem_neighborFinset]
      constructor
      · simpa [squareOrderDefectOwnerBlock, G.adj_comm,
          SimpleGraph.mem_neighborFinset] using hw.1
      · simpa [squareOrderDefectOwnerBlock, G.adj_comm,
          SimpleGraph.mem_neighborFinset] using hw.2
    rw [hz] at hwmem
    simpa using hwmem

/-- Exact pair-design interface: distinct pairs are defect nonedges precisely
when they have a unique original-neighborhood owner. -/
theorem not_defectAdj_iff_existsUnique_squareOrderDefectOwner
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) {u v : V} (huv : u ≠ v) :
    ¬ (secondOrderDefectGraph G).Adj u v ↔
      ∃! z : V, u ∈ squareOrderDefectOwnerBlock G z ∧
        v ∈ squareOrderDefectOwnerBlock G z := by
  constructor
  · exact existsUnique_squareOrderDefectOwner_of_not_adj G hfree huv
  · rintro ⟨z, hz, _hunique⟩
    exact not_defectAdj_of_mem_squareOrderDefectOwnerBlock
      G hfree hz.1 hz.2 huv

/-- Around a fixed point `u`, the punctured neighborhoods of its original
neighbors cover exactly the distinct defect nonneighbors of `u`. -/
theorem squareOrder_defectBranches_biUnion_eq_nonneighbors
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) (u : V) :
    (G.neighborFinset u).biUnion (squareOrderDefectBranch G u) =
      squareOrderDefectNonneighbors G u := by
  ext v
  constructor
  · intro hv
    rw [Finset.mem_biUnion] at hv
    obtain ⟨z, hzu, hvz⟩ := hv
    have hvne : v ≠ u := Finset.ne_of_mem_erase hvz
    have huz : u ∈ squareOrderDefectOwnerBlock G z := by
      simpa [squareOrderDefectOwnerBlock, SimpleGraph.mem_neighborFinset,
        G.adj_comm] using hzu
    have hvowner : v ∈ squareOrderDefectOwnerBlock G z := by
      exact Finset.mem_of_mem_erase hvz
    have hnot := not_defectAdj_of_mem_squareOrderDefectOwnerBlock
      G hfree huz hvowner hvne.symm
    simp [squareOrderDefectNonneighbors, hvne, hnot,
      SimpleGraph.mem_neighborFinset]
  · intro hv
    have hvdata : v ≠ u ∧ ¬ (secondOrderDefectGraph G).Adj u v := by
      simpa [squareOrderDefectNonneighbors, SimpleGraph.mem_neighborFinset]
        using hv
    obtain ⟨z, hz, _hunique⟩ :=
      existsUnique_squareOrderDefectOwner_of_not_adj
        G hfree hvdata.1.symm hvdata.2
    rw [Finset.mem_biUnion]
    refine ⟨z, ?_, ?_⟩
    · simpa [squareOrderDefectOwnerBlock, SimpleGraph.mem_neighborFinset,
        G.adj_comm] using hz.1
    · exact Finset.mem_erase.mpr ⟨hvdata.1, by
        simpa [squareOrderDefectOwnerBlock] using hz.2⟩

/-- The branches in the preceding cover are pairwise disjoint. -/
theorem squareOrder_defectBranches_pairwise_disjoint
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G) (u : V) :
    ∀ z ∈ G.neighborFinset u, ∀ w ∈ G.neighborFinset u,
      z ≠ w → Disjoint (squareOrderDefectBranch G u z)
        (squareOrderDefectBranch G u w) := by
  intro z hzu w hwu hzw
  rw [Finset.disjoint_left]
  intro v hvz hvw
  have hvz' : G.Adj z v := by
    simpa [squareOrderDefectBranch, SimpleGraph.mem_neighborFinset] using
      Finset.mem_of_mem_erase hvz
  have hvw' : G.Adj w v := by
    simpa [squareOrderDefectBranch, SimpleGraph.mem_neighborFinset] using
      Finset.mem_of_mem_erase hvw
  have hvu : v ≠ u := Finset.ne_of_mem_erase hvz
  have huz : G.Adj u z := by simpa [SimpleGraph.mem_neighborFinset] using hzu
  have huw : G.Adj u w := by simpa [SimpleGraph.mem_neighborFinset] using hwu
  exact hfree (containsC4_of_two_common hzw hvu.symm huz huw hvz'.symm hvw'.symm)

/-- A branch through an adjacent owner `z` has size `deg(z)-1`. -/
theorem card_squareOrderDefectBranch_eq_degree_sub_one
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] {u z : V}
    (huz : G.Adj u z) :
    (squareOrderDefectBranch G u z).card = G.degree z - 1 := by
  have humem : u ∈ G.neighborFinset z := by
    simpa [SimpleGraph.mem_neighborFinset, G.adj_comm] using huz
  rw [squareOrderDefectBranch, Finset.card_erase_of_mem humem,
    G.card_neighborFinset_eq_degree]

/-- At square order a branch is large (size `d`) exactly when its owner is
high (degree `d+1`). -/
theorem squareOrder_card_defectBranch_eq_iff_owner_high
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G)
    {d : ℕ} (hd : 2 ≤ d) (hmin : ∀ y : V, d ≤ G.degree y)
    (hcover : ∀ {u v}, G.Adj u v → G.degree u = d ∨ G.degree v = d)
    (hcard : Fintype.card V = d * d) {u z : V} (huz : G.Adj u z) :
    (squareOrderDefectBranch G u z).card = d ↔ G.degree z = d + 1 := by
  rw [card_squareOrderDefectBranch_eq_degree_sub_one G huz]
  rcases squareOrder_degree_eq_or_succ_of_tightEdgeCover
      G hfree hd hmin hcover hcard z with hz | hz <;> omega

/-- The incidence weight `k(u)` is exactly the number of large branches in
the local defect-nonneighbor partition at `u`. -/
theorem squareOrder_card_largeDefectBranches_eq_highIncidence
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G)
    {d : ℕ} (hd : 2 ≤ d) (hmin : ∀ y : V, d ≤ G.degree y)
    (hcover : ∀ {u v}, G.Adj u v → G.degree u = d ∨ G.degree v = d)
    (hcard : Fintype.card V = d * d) (u : V) :
    ((G.neighborFinset u).filter fun z =>
        (squareOrderDefectBranch G u z).card = d).card =
      squareOrderHighIncidenceCount G d u := by
  unfold squareOrderHighIncidenceCount
  congr 1
  ext z
  simp only [Finset.mem_filter, Finset.mem_inter,
    SimpleGraph.mem_neighborFinset]
  constructor
  · rintro ⟨huz, hbranch⟩
    exact ⟨huz, Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      (squareOrder_card_defectBranch_eq_iff_owner_high
        G hfree hd hmin hcover hcard huz).mp hbranch⟩⟩
  · rintro ⟨huz, hz⟩
    exact ⟨huz, (squareOrder_card_defectBranch_eq_iff_owner_high
      G hfree hd hmin hcover hcard huz).mpr (Finset.mem_filter.mp hz).2⟩

/-- A vertex distinct from a branch owner has at most one original neighbor
inside that branch.  Thus vertices route through the local branch partition
as partial transversals. -/
theorem card_neighbors_inter_squareOrderDefectBranch_le_one
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G) (u : V) {z v : V} (hzv : z ≠ v) :
    (G.neighborFinset v ∩ squareOrderDefectBranch G u z).card ≤ 1 := by
  have hsub :
      G.neighborFinset v ∩ squareOrderDefectBranch G u z ⊆
        G.neighborFinset v ∩ G.neighborFinset z := by
    intro x hx
    exact Finset.mem_inter.mpr ⟨(Finset.mem_inter.mp hx).1,
      Finset.mem_of_mem_erase (Finset.mem_inter.mp hx).2⟩
  exact (Finset.card_le_card hsub).trans
    (common_le_one_of_not_containsC4 hfree v z hzv.symm)

/-- A vertex adjacent to the center misses every branch except its own; in
its own branch it sees the entire punctured neighborhood. -/
theorem card_neighbors_inter_squareOrderDefectBranch_of_adj_center
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G) {u v z : V}
    (huv : G.Adj u v) (huz : G.Adj u z) :
    (G.neighborFinset v ∩ squareOrderDefectBranch G u z).card =
      if v = z then G.degree z - 1 else 0 := by
  by_cases hvz : v = z
  · subst v
    rw [if_pos rfl]
    have hsub : squareOrderDefectBranch G u z ⊆ G.neighborFinset z := by
      exact Finset.erase_subset _ _
    rw [Finset.inter_eq_right.mpr hsub,
      card_squareOrderDefectBranch_eq_degree_sub_one G huz]
  · rw [if_neg hvz, Finset.card_eq_zero]
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro x hx
    have hxv : G.Adj v x := by
      simpa [SimpleGraph.mem_neighborFinset] using (Finset.mem_inter.mp hx).1
    have hxz : G.Adj z x := by
      simpa [squareOrderDefectBranch, SimpleGraph.mem_neighborFinset] using
        Finset.mem_of_mem_erase (Finset.mem_inter.mp hx).2
    have hxu : x ≠ u := Finset.ne_of_mem_erase (Finset.mem_inter.mp hx).2
    exact hfree (containsC4_of_two_common hvz hxu.symm
      huv huz hxv.symm hxz.symm)

/-- A high vertex nonadjacent to a low center has exactly `d` neighbors in
the center's branch union (and its remaining unique neighbor in the center's
defect neighborhood).  Together with the one-per-branch bound, this is the
perfect-transversal count. -/
theorem squareOrder_card_highNeighbors_inter_defectNonneighbors_eq
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G)
    {d : ℕ} (hd : 2 ≤ d) (hmin : ∀ y : V, d ≤ G.degree y)
    (hcard : Fintype.card V = d * d) {u v : V}
    (hu : G.degree u = d) (hv : G.degree v = d + 1)
    (huv : ¬ G.Adj u v) :
    (G.neighborFinset v ∩ squareOrderDefectNonneighbors G u).card = d := by
  let D := secondOrderDefectGraph G
  let A := G.neighborFinset v
  let B := D.neighborFinset u
  have hleak := squareOrder_card_highNeighbors_inter_defectNeighbors
    G hfree hd hmin hcard hv hu
  rw [if_neg (by simpa [G.adj_comm] using huv)] at hleak
  change (A ∩ B).card = 1 at hleak
  have husplit : A \ B = A ∩ squareOrderDefectNonneighbors G u := by
    ext x
    by_cases hxv : G.Adj v x
    · have hxu : x ≠ u := by
        intro h
        subst x
        exact huv (by simpa [G.adj_comm] using hxv)
      simp [A, B, D, squareOrderDefectNonneighbors,
        SimpleGraph.mem_neighborFinset, hxv, hxu]
    · simp [A, B, D, squareOrderDefectNonneighbors,
        SimpleGraph.mem_neighborFinset, hxv]
  have hpartition := Finset.card_sdiff_add_card_inter A B
  rw [husplit, hleak] at hpartition
  have hAcard : A.card = d + 1 := by
    change (G.neighborFinset v).card = d + 1
    rw [G.card_neighborFinset_eq_degree, hv]
  rw [hAcard] at hpartition
  change (A ∩ squareOrderDefectNonneighbors G u).card = d
  omega

/-- Under the preceding hypotheses the aggregate transversal is pointwise
perfect: the high vertex meets every branch at the low center exactly once. -/
theorem squareOrder_card_highNeighbors_inter_defectBranch_eq_one
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G)
    {d : ℕ} (hd : 2 ≤ d) (hmin : ∀ y : V, d ≤ G.degree y)
    (hcard : Fintype.card V = d * d) {u v z : V}
    (hu : G.degree u = d) (hv : G.degree v = d + 1)
    (huv : ¬ G.Adj u v) (hzu : z ∈ G.neighborFinset u) :
    (G.neighborFinset v ∩ squareOrderDefectBranch G u z).card = 1 := by
  let S := G.neighborFinset u
  let F := fun z => G.neighborFinset v ∩ squareOrderDefectBranch G u z
  have hpair : (S : Set V).PairwiseDisjoint F := by
    intro a ha b hb hab
    exact (squareOrder_defectBranches_pairwise_disjoint G hfree u
      a ha b hb hab).mono Finset.inter_subset_right Finset.inter_subset_right
  have hunion : S.biUnion F =
      G.neighborFinset v ∩ squareOrderDefectNonneighbors G u := by
    rw [← squareOrder_defectBranches_biUnion_eq_nonneighbors G hfree u]
    ext x
    simp only [S, F, Finset.mem_biUnion, Finset.mem_inter,
      SimpleGraph.mem_neighborFinset]
    aesop
  have hsum : ∑ a ∈ S, (F a).card = d := by
    rw [← Finset.card_biUnion hpair, hunion]
    exact squareOrder_card_highNeighbors_inter_defectNonneighbors_eq
      G hfree hd hmin hcard hu hv huv
  have hScard : S.card = d := by
    dsimp [S]
    exact hu
  have hle : ∀ a ∈ S, (F a).card ≤ 1 := by
    intro a ha
    have hav : a ≠ v := by
      have hua : G.Adj u a := by
        simpa [S, SimpleGraph.mem_neighborFinset] using ha
      intro h
      subst a
      exact huv hua
    exact card_neighbors_inter_squareOrderDefectBranch_le_one G hfree u hav
  have hzS : z ∈ S := hzu
  by_contra hne
  have hz0 : (F z).card = 0 := by
    change (F z).card ≠ 1 at hne
    have := hle z hzS
    omega
  have herase : ∑ a ∈ S.erase z, (F a).card ≤ (S.erase z).card := by
    calc
      ∑ a ∈ S.erase z, (F a).card ≤ ∑ _a ∈ S.erase z, 1 :=
        Finset.sum_le_sum fun a ha => hle a (Finset.mem_of_mem_erase ha)
      _ = (S.erase z).card := by simp
  have hsum' : (∑ a ∈ S.erase z, (F a).card) + (F z).card = d := by
    exact (Finset.sum_erase_add S (fun a => (F a).card) hzS).trans hsum
  rw [hz0, add_zero] at hsum'
  rw [Finset.card_erase_of_mem hzS, hScard] at herase
  omega

/-- Branchwise refinement of the high-incidence equation.  A branch at a low
center receives one incidence from every high vertex not adjacent to the
center.  If its owner is itself high, that owner contributes all `d` points
of the branch as one additional full row. -/
theorem squareOrder_sum_highIncidence_over_defectBranch
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G)
    {d : ℕ} (hd : 2 ≤ d) (hmin : ∀ y : V, d ≤ G.degree y)
    (hcard : Fintype.card V = d * d) {u z : V}
    (hu : G.degree u = d) (huz : G.Adj u z) :
    (∑ x ∈ squareOrderDefectBranch G u z,
        squareOrderHighIncidenceCount G d x) =
      (squareOrderHighVertices G d).card -
          squareOrderHighIncidenceCount G d u +
        if G.degree z = d + 1 then d else 0 := by
  let H := squareOrderHighVertices G d
  let B := squareOrderDefectBranch G u z
  have hswap := sum_card_neighbor_inter_comm G B H
  have hterm : ∀ v ∈ H,
      (G.neighborFinset v ∩ B).card =
        (if ¬ G.Adj u v then 1 else 0) + (if v = z then d else 0) := by
    intro v hv
    have hvHigh : G.degree v = d + 1 := (Finset.mem_filter.mp hv).2
    by_cases huv : G.Adj u v
    · have hadj := card_neighbors_inter_squareOrderDefectBranch_of_adj_center
        G hfree huv huz
      change (G.neighborFinset v ∩ B).card = _ at hadj ⊢
      rw [hadj]
      by_cases hvz : v = z
      · subst v
        simp [huz, hvHigh]
      · simp [huv, hvz]
    · have hone := squareOrder_card_highNeighbors_inter_defectBranch_eq_one
        G hfree hd hmin hcard hu hvHigh huv
        (by simpa [SimpleGraph.mem_neighborFinset] using huz)
      change (G.neighborFinset v ∩ B).card = _ at hone ⊢
      have hvz : v ≠ z := by
        intro h
        subst v
        exact huv huz
      simp [hone, huv, hvz]
  have hfirst :
      (∑ v ∈ H, if ¬ G.Adj u v then 1 else 0) =
        (H \ G.neighborFinset u).card := by
    rw [Finset.sum_boole]
    apply congrArg Finset.card
    ext v
    simp [SimpleGraph.mem_neighborFinset]
  have hsecond :
      (∑ v ∈ H, if v = z then d else 0) =
        if z ∈ H then d else 0 := by
    by_cases hzH : z ∈ H
    · simp [hzH]
    · simp [hzH]
  change
    (∑ x ∈ B, (G.neighborFinset x ∩ H).card) =
      H.card - (G.neighborFinset u ∩ H).card +
        if G.degree z = d + 1 then d else 0
  rw [hswap]
  calc
    (∑ v ∈ H, (G.neighborFinset v ∩ B).card) =
        ∑ v ∈ H, ((if ¬ G.Adj u v then 1 else 0) +
          (if v = z then d else 0)) := by
      apply Finset.sum_congr rfl
      exact hterm
    _ = (H \ G.neighborFinset u).card + (if z ∈ H then d else 0) := by
      rw [Finset.sum_add_distrib, hfirst, hsecond]
    _ = H.card - (G.neighborFinset u ∩ H).card +
          if G.degree z = d + 1 then d else 0 := by
      rw [Finset.card_sdiff]
      simp [H, squareOrderHighVertices]

/-- At square order every owner block has size `d` or `d+1`. -/
theorem squareOrder_card_defectOwnerBlock_eq_or_succ
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G)
    {d : ℕ} (hd : 2 ≤ d) (hmin : ∀ y : V, d ≤ G.degree y)
    (hcover : ∀ {u v}, G.Adj u v → G.degree u = d ∨ G.degree v = d)
    (hcard : Fintype.card V = d * d) (z : V) :
    (squareOrderDefectOwnerBlock G z).card = d ∨
      (squareOrderDefectOwnerBlock G z).card = d + 1 := by
  simpa [squareOrderDefectOwnerBlock, G.card_neighborFinset_eq_degree] using
    squareOrder_degree_eq_or_succ_of_tightEdgeCover
      G hfree hd hmin hcover hcard z

end

end Erdos85
