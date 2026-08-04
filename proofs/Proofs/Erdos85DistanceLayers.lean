import Proofs.Erdos85RepairSet

/-!
# Distance layers in regular C4-free witnesses

Around a vertex `x`, the second-neighbor branches indexed by `N(x)` are
pairwise disjoint in a `C₄`-free graph.  In a `d`-regular graph each branch has
at least `d-2` vertices, because a neighbor of `x` has at most one further
neighbor inside `N(x)`.
-/

open SimpleGraph

namespace Erdos85

/-- The genuinely new neighbors reached through `y ∈ N(x)`. -/
def secondLayerBranch {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (x : V)
    (y : {z : V // z ∈ G.neighborSet x}) : Finset V :=
  G.neighborFinset y.1 \ insert x (G.neighborFinset x)

/-- Vertices at graph distance exactly two from `x`. -/
def secondLayer {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (x : V) : Finset V :=
  Finset.univ.biUnion (secondLayerBranch G x)

/-- Regard a first neighbor as a vertex of the graph with `x` deleted. -/
def neighborAsRemaining {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (x : V)
    (y : {z : V // z ∈ G.neighborSet x}) : {z : V // z ≠ x} :=
  ⟨y.1, (G.ne_of_adj y.2).symm⟩

/-- First-neighbor indices whose corresponding remaining vertex lies in `R`. -/
def selectedNeighborIndices {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (x : V)
    (R : Finset {z : V // z ≠ x}) :
    Finset {z : V // z ∈ G.neighborSet x} :=
  Finset.univ.filter fun y => neighborAsRemaining G x y ∈ R

/-- Selecting first neighbors is cardinality-preserving: these indices are
exactly `R ∩ N(x)`. -/
theorem card_selectedNeighborIndices
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (x : V)
    (R : Finset {z : V // z ≠ x}) :
    (selectedNeighborIndices G x R).card =
      (R ∩ deletedNeighborhood G x).card := by
  apply Finset.card_bij (fun y _ => neighborAsRemaining G x y)
  · intro y hy
    rw [Finset.mem_inter]
    have hyR : neighborAsRemaining G x y ∈ R := by
      simpa [selectedNeighborIndices] using hy
    exact ⟨hyR, (mem_deletedNeighborhood G x _).mpr y.2.symm⟩
  · intro a ha b hb hab
    apply Subtype.ext
    change a.1 = b.1
    have hv := congrArg (fun q : {z : V // z ≠ x} => q.1) hab
    simpa [neighborAsRemaining] using hv
  · intro a ha
    have haN : G.Adj a.1 x :=
      (mem_deletedNeighborhood G x a).mp (Finset.mem_inter.mp ha).2
    let y : {z : V // z ∈ G.neighborSet x} := ⟨a.1, haN.symm⟩
    refine ⟨y, ?_, ?_⟩
    · simpa [selectedNeighborIndices, y, neighborAsRemaining] using
        (Finset.mem_inter.mp ha).1
    · exact Subtype.ext rfl

/-- Distinct first-neighbor branches are disjoint in a `C₄`-free graph. -/
theorem secondLayerBranch_pairwiseDisjoint
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G) (x : V) :
    (↑(Finset.univ : Finset {z : V // z ∈ G.neighborSet x}) : Set _).PairwiseDisjoint
      (secondLayerBranch G x) := by
  intro y _ z _ hyz
  change Disjoint (secondLayerBranch G x y) (secondLayerBranch G x z)
  rw [Finset.disjoint_left]
  intro w hwy hwz
  have hyw : G.Adj y.1 w := (G.mem_neighborFinset y.1 w).mp
    (Finset.mem_sdiff.mp hwy).1
  have hzw : G.Adj z.1 w := (G.mem_neighborFinset z.1 w).mp
    (Finset.mem_sdiff.mp hwz).1
  have hxy : G.Adj x y.1 := y.2
  have hxz : G.Adj x z.1 := z.2
  have hyzne : y.1 ≠ z.1 := fun h => hyz (Subtype.ext h)
  have hxw : x ≠ w := by
    intro h
    subst w
    exact (Finset.mem_sdiff.mp hwy).2 (by simp)
  exact hfree (containsC4_of_two_common hyzne hxw hxy hxz hyw.symm hzw.symm)

/-- The closed neighborhood, the second layer, and the external repair
reservoir exhaust the vertex set.  This partition is purely definitional and
does not require the graph to be `C₄`-free. -/
theorem closedNeighborhood_union_secondLayer_union_external_eq_univ
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (x : V) :
    insert x (G.neighborFinset x) ∪ secondLayer G x ∪
        (externalRepairCandidates G x).map
          ⟨Subtype.val, Subtype.val_injective⟩ = Finset.univ := by
  classical
  apply Finset.eq_univ_of_forall
  intro z
  by_cases hzx : z = x
  · subst z
    exact Finset.mem_union_left _ (Finset.mem_union_left _ (by simp))
  by_cases hxz : G.Adj x z
  · exact Finset.mem_union_left _ (Finset.mem_union_left _
      (Finset.mem_insert.mpr (Or.inr ((G.mem_neighborFinset x z).mpr hxz))))
  by_cases hnear : ∃ y : V, G.Adj x y ∧ G.Adj y z
  · obtain ⟨y, hxy, hyz⟩ := hnear
    have hzD : z ∈ secondLayer G x := by
      rw [secondLayer, Finset.mem_biUnion]
      let y' : {w : V // w ∈ G.neighborSet x} := ⟨y, hxy⟩
      refine ⟨y', Finset.mem_univ _, Finset.mem_sdiff.mpr ⟨?_, ?_⟩⟩
      · exact (G.mem_neighborFinset y z).mpr hyz
      · intro hzC
        rcases Finset.mem_insert.mp hzC with hzx' | hzxN
        · exact hzx hzx'
        · exact hxz ((G.mem_neighborFinset x z).mp hzxN)
    exact Finset.mem_union_left _ (Finset.mem_union_right _ hzD)
  · have ha : ⟨z, hzx⟩ ∈ externalRepairCandidates G x := by
      rw [mem_externalRepairCandidates]
      refine ⟨?_, ?_⟩
      · exact fun h => hxz h.symm
      · intro b hbx hzb
        exact hnear ⟨b.1, hbx.symm, hzb.symm⟩
    apply Finset.mem_union_right
    rw [Finset.mem_map]
    exact ⟨⟨z, hzx⟩, ha, rfl⟩

/-- Exact cardinal form of the distance partition.  In particular, the size
of the external repair reservoir is exactly the number of vertices beyond
distance two from `x`. -/
theorem card_externalRepairCandidates_add_card_secondLayer_add_degree_add_one
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (x : V) :
    (externalRepairCandidates G x).card + (secondLayer G x).card +
        G.degree x + 1 = Fintype.card V := by
  classical
  let C : Finset V := insert x (G.neighborFinset x)
  let D : Finset V := secondLayer G x
  let F : Finset V := (externalRepairCandidates G x).map
    ⟨Subtype.val, Subtype.val_injective⟩
  have hCD : Disjoint C D := by
    rw [Finset.disjoint_left]
    intro z hzC hzD
    change z ∈ secondLayer G x at hzD
    rw [secondLayer, Finset.mem_biUnion] at hzD
    obtain ⟨y, _, hy⟩ := hzD
    exact (Finset.mem_sdiff.mp hy).2 hzC
  have hCF : Disjoint C F := by
    rw [Finset.disjoint_left]
    intro z hzC hzF
    rw [Finset.mem_map] at hzF
    obtain ⟨a, ha, rfl⟩ := hzF
    rcases Finset.mem_insert.mp hzC with hax | hax
    · exact a.2 hax
    · exact (mem_externalRepairCandidates G x a).mp ha |>.1
        (((G.mem_neighborFinset x a.1).mp hax).symm)
  have hDF : Disjoint D F := by
    rw [Finset.disjoint_left]
    intro z hzD hzF
    rw [Finset.mem_map] at hzF
    obtain ⟨a, ha, rfl⟩ := hzF
    change a.1 ∈ secondLayer G x at hzD
    rw [secondLayer, Finset.mem_biUnion] at hzD
    obtain ⟨y, _, hy⟩ := hzD
    have hya : G.Adj y.1 a.1 := (G.mem_neighborFinset y.1 a.1).mp
      (Finset.mem_sdiff.mp hy).1
    let b : {z : V // z ≠ x} := ⟨y.1, (G.ne_of_adj y.2).symm⟩
    exact ((mem_externalRepairCandidates G x a).mp ha |>.2 b y.2.symm) hya.symm
  have hUnionDisj : Disjoint (C ∪ D) F :=
    Finset.disjoint_union_left.mpr ⟨hCF, hDF⟩
  have hcover : C ∪ D ∪ F = Finset.univ := by
    simpa [C, D, F] using
      closedNeighborhood_union_secondLayer_union_external_eq_univ G x
  have hcard := congrArg Finset.card hcover
  rw [Finset.card_union_of_disjoint hUnionDisj,
    Finset.card_union_of_disjoint hCD] at hcard
  have hCcard : C.card = G.degree x + 1 := by
    have hxN : x ∉ G.neighborFinset x := by simp
    simp [C, Finset.card_insert_of_notMem hxN,
      G.card_neighborFinset_eq_degree]
  have hFcard : F.card = (externalRepairCandidates G x).card := by simp [F]
  simp only [Finset.card_univ] at hcard
  change C.card + D.card + F.card = Fintype.card V at hcard
  simp only [hCcard, hFcard] at hcard
  simpa [D, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hcard

/-- In a regular `C₄`-free graph, every first-neighbor branch contains at
least `d-2` second-layer vertices. -/
theorem sub_two_le_card_secondLayerBranch_of_regular
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G) {d : ℕ}
    (hreg : ∀ v, G.degree v = d) (x : V)
    (y : {z : V // z ∈ G.neighborSet x}) :
    d - 2 ≤ (secondLayerBranch G x y).card := by
  let N := G.neighborFinset x
  let M := G.neighborFinset y.1
  have hxy : G.Adj x y.1 := y.2
  have hcommon := common_le_one_of_not_containsC4 hfree x y.1
    (G.ne_of_adj hxy)
  have hinter : insert x N ∩ M = insert x (N ∩ M) := by
    ext z
    simp only [Finset.mem_inter, Finset.mem_insert]
    constructor
    · rintro ⟨hzx | hzN, hzM⟩
      · exact Or.inl hzx
      · exact Or.inr ⟨hzN, hzM⟩
    · rintro (rfl | ⟨hzN, hzM⟩)
      · exact ⟨Or.inl rfl, by simpa [M] using hxy.symm⟩
      · exact ⟨Or.inr hzN, hzM⟩
  have hxnot : x ∉ N ∩ M := by simp [N]
  have hinterCard : (insert x N ∩ M).card ≤ 2 := by
    rw [hinter, Finset.card_insert_of_notMem hxnot]
    change (G.neighborFinset x ∩ G.neighborFinset y.1).card + 1 ≤ 2
    omega
  have hpart := Finset.card_sdiff_add_card_inter M (insert x N)
  rw [Finset.inter_comm] at hpart
  change (secondLayerBranch G x y).card + (insert x N ∩ M).card = M.card at hpart
  have hMcard : M.card = d := by
    change (G.neighborFinset y.1).card = d
    rw [G.card_neighborFinset_eq_degree, hreg y.1]
  omega

/-- If a first neighbor is itself a repair candidate, it has no neighbor in
`N(x)`, so its second-layer branch has size at least `d-1`. -/
theorem sub_one_le_card_secondLayerBranch_of_candidate
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {d : ℕ} (hreg : ∀ v, G.degree v = d) (x : V)
    (y : {z : V // z ∈ G.neighborSet x})
    (hycand : neighborAsRemaining G x y ∈ repairCandidates G x) :
    d - 1 ≤ (secondLayerBranch G x y).card := by
  let N := G.neighborFinset x
  let M := G.neighborFinset y.1
  have hxy : G.Adj x y.1 := y.2
  have hNM : N ∩ M = ∅ := by
    rw [Finset.eq_empty_iff_forall_notMem]
    intro z hz
    rw [Finset.mem_inter] at hz
    have hxz : G.Adj z x := ((G.mem_neighborFinset x z).mp hz.1).symm
    have hyz : G.Adj y.1 z := (G.mem_neighborFinset y.1 z).mp hz.2
    let b : {w : V // w ≠ x} := ⟨z, (G.ne_of_adj hxz)⟩
    have hbmem : b ∈ deletedNeighborhood G x :=
      (mem_deletedNeighborhood G x b).mpr hxz
    have hanti := (mem_repairCandidates G x (neighborAsRemaining G x y)).mp
      hycand b hbmem
    exact hanti hyz
  have hinter : insert x N ∩ M = {x} := by
    ext z
    simp only [Finset.mem_inter, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨rfl | hzN, hzM⟩
      · rfl
      · exfalso
        have : z ∈ N ∩ M := Finset.mem_inter.mpr ⟨hzN, hzM⟩
        rw [hNM] at this
        exact Finset.notMem_empty z this
    · rintro rfl
      exact ⟨Or.inl rfl, by simpa [M] using hxy.symm⟩
  have hpart := Finset.card_sdiff_add_card_inter M (insert x N)
  rw [Finset.inter_comm, hinter] at hpart
  change (secondLayerBranch G x y).card + ({x} : Finset V).card = M.card at hpart
  have hMcard : M.card = d := by
    change (G.neighborFinset y.1).card = d
    rw [G.card_neighborFinset_eq_degree, hreg y.1]
  simp only [Finset.card_singleton] at hpart
  omega

/-- A regular degree-`d` `C₄`-free graph has at least `d(d-2)` vertices in the
second layer around every vertex. -/
theorem mul_sub_two_le_card_secondLayer_of_regular
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G) {d : ℕ}
    (hreg : ∀ v, G.degree v = d) (x : V) :
    d * (d - 2) ≤ (secondLayer G x).card := by
  classical
  have hdisj := secondLayerBranch_pairwiseDisjoint G hfree x
  rw [secondLayer, Finset.card_biUnion hdisj]
  calc
    d * (d - 2) = ∑ _y : {z : V // z ∈ G.neighborSet x}, (d - 2) := by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_subtype]
      have heq : Finset.univ.filter (fun z => z ∈ G.neighborSet x) =
          G.neighborFinset x := by ext z; simp
      rw [heq, G.card_neighborFinset_eq_degree, hreg x]
      simp
    _ ≤ ∑ y, (secondLayerBranch G x y).card :=
      Finset.sum_le_sum fun y _ =>
        sub_two_le_card_secondLayerBranch_of_regular G hfree hreg x y

/-- Every selected repair candidate inside `N(x)` contributes one extra
second-layer vertex beyond the uniform `d-2` branch bound. -/
theorem base_add_internal_repair_le_card_secondLayer_of_regular
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G) {d : ℕ} (hd : 2 ≤ d)
    (hreg : ∀ v, G.degree v = d) (x : V)
    (R : Finset {z : V // z ≠ x}) (hsub : R ⊆ repairCandidates G x) :
    d * (d - 2) + (R ∩ deletedNeighborhood G x).card ≤
      (secondLayer G x).card := by
  classical
  let J := selectedNeighborIndices G x R
  have hJcard : J.card = (R ∩ deletedNeighborhood G x).card := by
    simpa [J] using card_selectedNeighborIndices G x R
  have hbranch : ∀ y : {z : V // z ∈ G.neighborSet x},
      (d - 2) + (if y ∈ J then 1 else 0) ≤
        (secondLayerBranch G x y).card := by
    intro y
    by_cases hy : y ∈ J
    · rw [if_pos hy]
      have hyR : neighborAsRemaining G x y ∈ R := by
        simpa [J, selectedNeighborIndices] using hy
      have hstrong := sub_one_le_card_secondLayerBranch_of_candidate
        G hreg x y (hsub hyR)
      omega
    · rw [if_neg hy, Nat.add_zero]
      exact sub_two_le_card_secondLayerBranch_of_regular G hfree hreg x y
  have hdisj := secondLayerBranch_pairwiseDisjoint G hfree x
  rw [secondLayer, Finset.card_biUnion hdisj]
  calc
    d * (d - 2) + (R ∩ deletedNeighborhood G x).card =
        ∑ y : {z : V // z ∈ G.neighborSet x},
          ((d - 2) + (if y ∈ J then 1 else 0)) := by
      rw [Finset.sum_add_distrib]
      have hNcard : Fintype.card {z : V // z ∈ G.neighborSet x} = d := by
        rw [Fintype.card_subtype]
        have heq : Finset.univ.filter (fun z => z ∈ G.neighborSet x) =
            G.neighborFinset x := by ext z; simp
        rw [heq, G.card_neighborFinset_eq_degree, hreg x]
      have hNcardAdj : Fintype.card {z : V // G.Adj x z} = d := by
        let e : {z : V // z ∈ G.neighborSet x} ≃ {z : V // G.Adj x z} :=
          Equiv.subtypeEquivRight (fun _ => Iff.rfl)
        rw [← Fintype.card_congr e]
        exact hNcard
      simp [hNcardAdj, hJcard, J]
    _ ≤ ∑ y, (secondLayerBranch G x y).card :=
      Finset.sum_le_sum fun y _ => hbranch y

/-- The closed neighborhood, second layer, and external repair reservoir are
pairwise disjoint.  Combining this partition with the second-layer lower bound
gives a sharp upper bound on the reservoir. -/
theorem card_externalRepairCandidates_add_mooreBase_le_of_regular
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G) {d : ℕ}
    (hreg : ∀ v, G.degree v = d) (x : V) :
    (externalRepairCandidates G x).card + (d * (d - 1) + 1) ≤
      Fintype.card V := by
  classical
  let C : Finset V := insert x (G.neighborFinset x)
  let D : Finset V := secondLayer G x
  let F : Finset V := (externalRepairCandidates G x).map
    ⟨Subtype.val, Subtype.val_injective⟩
  have hCD : Disjoint C D := by
    rw [Finset.disjoint_left]
    intro z hzC hzD
    change z ∈ secondLayer G x at hzD
    rw [secondLayer, Finset.mem_biUnion] at hzD
    obtain ⟨y, _, hy⟩ := hzD
    exact (Finset.mem_sdiff.mp hy).2 hzC
  have hCF : Disjoint C F := by
    rw [Finset.disjoint_left]
    intro z hzC hzF
    rw [Finset.mem_map] at hzF
    obtain ⟨a, ha, rfl⟩ := hzF
    rcases Finset.mem_insert.mp hzC with hax | hax
    · exact a.2 hax
    · have hAdj : G.Adj a.1 x :=
        ((G.mem_neighborFinset x a.1).mp hax).symm
      exact (mem_externalRepairCandidates G x a).mp ha |>.1 hAdj
  have hDF : Disjoint D F := by
    rw [Finset.disjoint_left]
    intro z hzD hzF
    rw [Finset.mem_map] at hzF
    obtain ⟨a, ha, rfl⟩ := hzF
    change a.1 ∈ secondLayer G x at hzD
    rw [secondLayer, Finset.mem_biUnion] at hzD
    obtain ⟨y, _, hy⟩ := hzD
    have hya : G.Adj y.1 a.1 := (G.mem_neighborFinset y.1 a.1).mp
      (Finset.mem_sdiff.mp hy).1
    let b : {z : V // z ≠ x} := ⟨y.1, (G.ne_of_adj y.2).symm⟩
    have hbx : G.Adj b.1 x := y.2.symm
    have hfar := (mem_externalRepairCandidates G x a).mp ha |>.2 b hbx
    exact hfar hya.symm
  have hUnionDisj : Disjoint (C ∪ D) F := Finset.disjoint_union_left.mpr ⟨hCF, hDF⟩
  have htotal : (C ∪ D ∪ F).card ≤ Fintype.card V := by
    simpa using Finset.card_le_card (show C ∪ D ∪ F ⊆ Finset.univ from
      fun _ _ => Finset.mem_univ _)
  have hCcard : C.card = d + 1 := by
    have hxN : x ∉ G.neighborFinset x := by simp
    simp [C, Finset.card_insert_of_notMem hxN,
      G.card_neighborFinset_eq_degree, hreg x]
  have hFcard : F.card = (externalRepairCandidates G x).card := by
    simp [F]
  have hDcard : d * (d - 2) ≤ D.card := by
    simpa [D] using mul_sub_two_le_card_secondLayer_of_regular G hfree hreg x
  rw [Finset.card_union_of_disjoint hUnionDisj,
    Finset.card_union_of_disjoint hCD, hCcard, hFcard] at htotal
  by_cases hd : d < 2
  · interval_cases d <;> norm_num at htotal ⊢ <;> omega
  · have hd2 : 2 ≤ d := by omega
    have hsub2 : d - 2 + 2 = d := by omega
    have hsub1 : d - 1 + 1 = d := by omega
    have halg : d * (d - 1) = d + d * (d - 2) := by nlinarith
    omega

/-- Refined reservoir bound: every chosen repair candidate inside `N(x)` costs
one additional second-layer vertex. -/
theorem card_external_add_internalRepair_add_mooreBase_le_of_regular
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G) {d : ℕ} (hd : 2 ≤ d)
    (hreg : ∀ v, G.degree v = d) (x : V)
    (R : Finset {z : V // z ≠ x}) (hsub : R ⊆ repairCandidates G x) :
    (externalRepairCandidates G x).card +
        (R ∩ deletedNeighborhood G x).card +
        (d * (d - 1) + 1) ≤ Fintype.card V := by
  classical
  let C : Finset V := insert x (G.neighborFinset x)
  let D : Finset V := secondLayer G x
  let F : Finset V := (externalRepairCandidates G x).map
    ⟨Subtype.val, Subtype.val_injective⟩
  have hCD : Disjoint C D := by
    rw [Finset.disjoint_left]
    intro z hzC hzD
    change z ∈ secondLayer G x at hzD
    rw [secondLayer, Finset.mem_biUnion] at hzD
    obtain ⟨y, _, hy⟩ := hzD
    exact (Finset.mem_sdiff.mp hy).2 hzC
  have hCF : Disjoint C F := by
    rw [Finset.disjoint_left]
    intro z hzC hzF
    rw [Finset.mem_map] at hzF
    obtain ⟨a, ha, rfl⟩ := hzF
    rcases Finset.mem_insert.mp hzC with hax | hax
    · exact a.2 hax
    · exact (mem_externalRepairCandidates G x a).mp ha |>.1
        (((G.mem_neighborFinset x a.1).mp hax).symm)
  have hDF : Disjoint D F := by
    rw [Finset.disjoint_left]
    intro z hzD hzF
    rw [Finset.mem_map] at hzF
    obtain ⟨a, ha, rfl⟩ := hzF
    change a.1 ∈ secondLayer G x at hzD
    rw [secondLayer, Finset.mem_biUnion] at hzD
    obtain ⟨y, _, hy⟩ := hzD
    have hya : G.Adj y.1 a.1 := (G.mem_neighborFinset y.1 a.1).mp
      (Finset.mem_sdiff.mp hy).1
    let b : {z : V // z ≠ x} := ⟨y.1, (G.ne_of_adj y.2).symm⟩
    exact ((mem_externalRepairCandidates G x a).mp ha |>.2 b y.2.symm) hya.symm
  have hUnionDisj : Disjoint (C ∪ D) F := Finset.disjoint_union_left.mpr ⟨hCF, hDF⟩
  have htotal : (C ∪ D ∪ F).card ≤ Fintype.card V := by
    exact Finset.card_le_card (fun _ _ => Finset.mem_univ _)
  have hCcard : C.card = d + 1 := by
    have hxN : x ∉ G.neighborFinset x := by simp
    simp [C, Finset.card_insert_of_notMem hxN,
      G.card_neighborFinset_eq_degree, hreg x]
  have hFcard : F.card = (externalRepairCandidates G x).card := by simp [F]
  have hDcard : d * (d - 2) + (R ∩ deletedNeighborhood G x).card ≤ D.card := by
    simpa [D] using base_add_internal_repair_le_card_secondLayer_of_regular
      G hfree hd hreg x R hsub
  rw [Finset.card_union_of_disjoint hUnionDisj,
    Finset.card_union_of_disjoint hCD, hCcard, hFcard] at htotal
  have hsub2 : d - 2 + 2 = d := by omega
  have hsub1 : d - 1 + 1 = d := by omega
  have halg : d * (d - 1) = d + d * (d - 2) := by nlinarith
  omega

/-- Therefore the canonical repair surgery on a regular witness can exist only
above the order `d²-1`. -/
theorem degree_sq_sub_one_le_card_of_regular_hasRepairSet
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G) {d : ℕ}
    (hreg : ∀ v, G.degree v = d) (hrepair : HasRepairSet G d) :
    d * d - 1 ≤ Fintype.card V := by
  obtain ⟨x, hx⟩ := exists_card_externalRepairCandidates_of_hasRepairSet G hrepair
  have hbound := card_externalRepairCandidates_add_mooreBase_le_of_regular
    G hfree hreg x
  by_cases hd : d < 2
  · interval_cases d <;> norm_num
  · have hsub2 : d - 2 + 2 = d := by omega
    have hsub1 : d - 1 + 1 = d := by omega
    have hd2 : 2 ≤ d := by omega
    have hprod : 1 ≤ d * d := by nlinarith
    have hsq : d * d - 1 + 1 = d * d := Nat.sub_add_cancel hprod
    have halg : d * d - 1 = (d - 2) + (d * (d - 1) + 1) := by
      nlinarith
    omega

/-- Sharp repair obstruction for regular witnesses: the canonical repair-set
surgery requires order at least `d²`. -/
theorem degree_sq_le_card_of_regular_hasRepairSet
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G) {d : ℕ} (hd : 2 ≤ d)
    (hreg : ∀ v, G.degree v = d) (hrepair : HasRepairSet G d) :
    d * d ≤ Fintype.card V := by
  rw [hasRepairSet_iff_exists_subset_candidates] at hrepair
  obtain ⟨x, R, hRcard, _, hinter, hsub⟩ := hrepair
  have hrefined := card_external_add_internalRepair_add_mooreBase_le_of_regular
    G hfree hd hreg x R hsub
  have hdiffSub : R \ deletedNeighborhood G x ⊆
      externalRepairCandidates G x := by
    intro a ha
    exact Finset.mem_sdiff.mpr
      ⟨hsub (Finset.mem_sdiff.mp ha).1, (Finset.mem_sdiff.mp ha).2⟩
  have hdiff := Finset.card_le_card hdiffSub
  have hpartition := Finset.card_sdiff_add_card_inter R (deletedNeighborhood G x)
  have hsub1 : d - 1 + 1 = d := by omega
  have halg : d * d = (d - 1) + (d * (d - 1) + 1) := by nlinarith
  omega

/-- In particular, every regular witness below order `d²` fails the canonical
repair-set criterion. -/
theorem not_hasRepairSet_of_regular_card_lt_degree_sq
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G) {d : ℕ} (hd : 2 ≤ d)
    (hreg : ∀ v, G.degree v = d)
    (hsmall : Fintype.card V < d * d) :
    ¬ HasRepairSet G d := by
  intro hrepair
  exact (not_lt_of_ge
    (degree_sq_le_card_of_regular_hasRepairSet G hfree hd hreg hrepair)) hsmall

/-- In particular, every regular witness at the common-neighbor counting bound
`d(d-1)+1` fails the canonical repair surgery. -/
theorem not_hasRepairSet_of_regular_card_eq_mul_pred_add_one
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G) {d : ℕ} (hd : 2 ≤ d)
    (hreg : ∀ v, G.degree v = d)
    (hcard : Fintype.card V = d * (d - 1) + 1) :
    ¬ HasRepairSet G d := by
  apply not_hasRepairSet_of_regular_card_lt_degree_sq G hfree hd hreg
  rw [hcard]
  have hsub : d - 1 + 1 = d := by omega
  nlinarith

/-- Uniform explanation of the order-15 stress-test failure: no 4-regular
`C₄`-free graph on 15 vertices has a canonical repair set. -/
theorem not_hasRepairSet_four_regular_fifteen
    (G : SimpleGraph (Fin 15)) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 (Fin 15) G)
    (hreg : ∀ v, G.degree v = 4) :
    ¬ HasRepairSet G 4 := by
  exact not_hasRepairSet_of_regular_card_lt_degree_sq
    (d := 4) G hfree (by norm_num) hreg (by norm_num)

/-- Below order `d²-1`, a regular `C₄`-free witness cannot satisfy the
canonical repair-set criterion. -/
theorem not_hasRepairSet_of_regular_card_lt_degree_sq_sub_one
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G) {d : ℕ}
    (hreg : ∀ v, G.degree v = d)
    (hsmall : Fintype.card V < d * d - 1) :
    ¬ HasRepairSet G d := by
  intro hrepair
  have hbound := degree_sq_sub_one_le_card_of_regular_hasRepairSet
    G hfree hreg hrepair
  omega

/-! ## A minimum-degree Moore-layer bound

The preceding branch argument does not intrinsically require regularity.  A
minimum-degree lower bound controls every branch, while the number of branches
is the actual degree of the center.  This sharper asymmetric form is useful at
order 32.
-/

/-- Every branch has at least `d-2` vertices under minimum degree `d`. -/
theorem sub_two_le_card_secondLayerBranch_of_minDegree
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G) {d : ℕ} (hmin : d ≤ G.minDegree)
    (x : V) (y : {z : V // z ∈ G.neighborSet x}) :
    d - 2 ≤ (secondLayerBranch G x y).card := by
  let N := G.neighborFinset x
  let M := G.neighborFinset y.1
  have hxy : G.Adj x y.1 := y.2
  have hcommon := common_le_one_of_not_containsC4 hfree x y.1
    (G.ne_of_adj hxy)
  have hinter : insert x N ∩ M = insert x (N ∩ M) := by
    ext z
    simp only [Finset.mem_inter, Finset.mem_insert]
    constructor
    · rintro ⟨hzx | hzN, hzM⟩
      · exact Or.inl hzx
      · exact Or.inr ⟨hzN, hzM⟩
    · rintro (rfl | ⟨hzN, hzM⟩)
      · exact ⟨Or.inl rfl, by simpa [M] using hxy.symm⟩
      · exact ⟨Or.inr hzN, hzM⟩
  have hxnot : x ∉ N ∩ M := by simp [N]
  have hinterCard : (insert x N ∩ M).card ≤ 2 := by
    rw [hinter, Finset.card_insert_of_notMem hxnot]
    change (G.neighborFinset x ∩ G.neighborFinset y.1).card + 1 ≤ 2
    omega
  have hpart := Finset.card_sdiff_add_card_inter M (insert x N)
  rw [Finset.inter_comm] at hpart
  change (secondLayerBranch G x y).card + (insert x N ∩ M).card = M.card at hpart
  have hMlower : d ≤ M.card := by
    change d ≤ (G.neighborFinset y.1).card
    rw [G.card_neighborFinset_eq_degree]
    exact le_trans hmin (G.minDegree_le_degree y.1)
  omega

/-- The second layer has at least `deg(x)(d-2)` vertices when the whole graph
has minimum degree at least `d`. -/
theorem degree_mul_sub_two_le_card_secondLayer_of_minDegree
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G) {d : ℕ} (hmin : d ≤ G.minDegree)
    (x : V) :
    G.degree x * (d - 2) ≤ (secondLayer G x).card := by
  classical
  have hdisj := secondLayerBranch_pairwiseDisjoint G hfree x
  rw [secondLayer, Finset.card_biUnion hdisj]
  calc
    G.degree x * (d - 2) =
        ∑ _y : {z : V // z ∈ G.neighborSet x}, (d - 2) := by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_subtype]
      have heq : Finset.univ.filter (fun z => z ∈ G.neighborSet x) =
          G.neighborFinset x := by ext z; simp
      rw [heq, G.card_neighborFinset_eq_degree]
      simp
    _ ≤ ∑ y, (secondLayerBranch G x y).card :=
      Finset.sum_le_sum fun y _ =>
        sub_two_le_card_secondLayerBranch_of_minDegree G hfree hmin x y

/-- Closed first layer and second layer give the asymmetric Moore bound
`1 + deg(x) + deg(x)(d-2) ≤ |V|`. -/
theorem one_add_degree_add_mul_sub_two_le_card_of_minDegree
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G) {d : ℕ} (hmin : d ≤ G.minDegree)
    (x : V) :
    1 + G.degree x + G.degree x * (d - 2) ≤ Fintype.card V := by
  classical
  let C : Finset V := insert x (G.neighborFinset x)
  let D : Finset V := secondLayer G x
  have hCD : Disjoint C D := by
    rw [Finset.disjoint_left]
    intro z hzC hzD
    change z ∈ secondLayer G x at hzD
    rw [secondLayer, Finset.mem_biUnion] at hzD
    obtain ⟨y, _, hzy⟩ := hzD
    exact (Finset.mem_sdiff.mp hzy).2 hzC
  have hcardUnion : C.card + D.card ≤ Fintype.card V := by
    rw [← Finset.card_union_of_disjoint hCD]
    exact Finset.card_le_univ _
  have hCcard : C.card = 1 + G.degree x := by
    change (insert x (G.neighborFinset x)).card = 1 + G.degree x
    rw [Finset.card_insert_of_notMem]
    · rw [G.card_neighborFinset_eq_degree]
      omega
    · simp
  have hDlower := degree_mul_sub_two_le_card_secondLayer_of_minDegree
    G hfree hmin x
  change G.degree x * (d - 2) ≤ D.card at hDlower
  omega

/-- Degree inside the graph induced by `N(x)` is the number of common
neighbours with `x`. -/
theorem degree_induce_neighborSet_eq_card_common
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (x : V)
    (y : {z : V // z ∈ G.neighborSet x}) :
    (G.induce (G.neighborSet x)).degree y =
      (G.neighborFinset x ∩ G.neighborFinset y.1).card := by
  rw [← SimpleGraph.card_neighborFinset_eq_degree,
    ← Finset.card_map (f := Function.Embedding.subtype (· ∈ G.neighborSet x)),
    G.map_neighborFinset_induce]
  rw [Finset.inter_comm]
  congr 1

/-- In a `C₄`-free graph the graph induced by any neighborhood has maximum
degree at most one, hence is a matching together with isolated vertices. -/
theorem sum_localNeighborhood_degrees_le_degree
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G) (x : V) :
    (∑ y : {z : V // z ∈ G.neighborSet x},
      (G.induce (G.neighborSet x)).degree y) ≤ G.degree x := by
  classical
  calc
    (∑ y : {z : V // z ∈ G.neighborSet x},
        (G.induce (G.neighborSet x)).degree y) ≤
        ∑ _y : {z : V // z ∈ G.neighborSet x}, 1 := by
      apply Finset.sum_le_sum
      intro y _
      rw [degree_induce_neighborSet_eq_card_common]
      exact common_le_one_of_not_containsC4 hfree x y.1 (G.ne_of_adj y.2)
    _ = G.degree x := by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_subtype]
      have heq : Finset.univ.filter (fun z => z ∈ G.neighborSet x) =
          G.neighborFinset x := by ext z; simp
      rw [heq, G.card_neighborFinset_eq_degree]
      simp

/-- Exact branch accounting: the neighbors of `y` are partitioned into the
second-layer branch, the center `x`, and the common neighbors of `x,y`. -/
theorem card_secondLayerBranch_add_common_add_one
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (x : V)
    (y : {z : V // z ∈ G.neighborSet x}) :
    (secondLayerBranch G x y).card +
      (G.neighborFinset x ∩ G.neighborFinset y.1).card + 1 =
        G.degree y.1 := by
  let N := G.neighborFinset x
  let M := G.neighborFinset y.1
  have hxy : G.Adj x y.1 := y.2
  have hinter : insert x N ∩ M = insert x (N ∩ M) := by
    ext z
    simp only [Finset.mem_inter, Finset.mem_insert]
    constructor
    · rintro ⟨hzx | hzN, hzM⟩
      · exact Or.inl hzx
      · exact Or.inr ⟨hzN, hzM⟩
    · rintro (rfl | ⟨hzN, hzM⟩)
      · exact ⟨Or.inl rfl, by simpa [M] using hxy.symm⟩
      · exact ⟨Or.inr hzN, hzM⟩
  have hxnot : x ∉ N ∩ M := by simp [N]
  have hpart := Finset.card_sdiff_add_card_inter M (insert x N)
  rw [Finset.inter_comm, hinter, Finset.card_insert_of_notMem hxnot] at hpart
  change (secondLayerBranch G x y).card +
      ((G.neighborFinset x ∩ G.neighborFinset y.1).card + 1) =
        (G.neighborFinset y.1).card at hpart
  rw [G.card_neighborFinset_eq_degree] at hpart
  omega

/-- Exact regular reservoir identity.  The deficit from the Moore tree is
precisely the total degree inside the neighborhood of the center (equivalently,
twice the number of triangles through the center):
`external + d² + 1 = |V| + Σ deg(G[N(x)])`. -/
theorem card_external_add_degree_sq_add_one_eq_card_add_localDegreeSum
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G) {d : ℕ}
    (hreg : ∀ v, G.degree v = d) (x : V) :
    (externalRepairCandidates G x).card + d * d + 1 =
      Fintype.card V +
        ∑ y : {z : V // z ∈ G.neighborSet x},
          (G.induce (G.neighborSet x)).degree y := by
  classical
  let S := ∑ y : {z : V // z ∈ G.neighborSet x},
    (G.induce (G.neighborSet x)).degree y
  have hdisj := secondLayerBranch_pairwiseDisjoint G hfree x
  have hD : (secondLayer G x).card =
      ∑ y : {z : V // z ∈ G.neighborSet x},
        (secondLayerBranch G x y).card := by
    rw [secondLayer, Finset.card_biUnion hdisj]
  have hNcard : Fintype.card {z : V // z ∈ G.neighborSet x} = d := by
    rw [Fintype.card_subtype]
    have heq : Finset.univ.filter (fun z => z ∈ G.neighborSet x) =
        G.neighborFinset x := by ext z; simp
    rw [heq, G.card_neighborFinset_eq_degree, hreg x]
  have hNcardAdj : Fintype.card {z : V // G.Adj x z} = d := by
    let e : {z : V // z ∈ G.neighborSet x} ≃ {z : V // G.Adj x z} :=
      Equiv.subtypeEquivRight (fun _ => Iff.rfl)
    rw [← Fintype.card_congr e]
    exact hNcard
  have hbranches :
      (∑ y : {z : V // z ∈ G.neighborSet x},
          ((secondLayerBranch G x y).card +
            (G.induce (G.neighborSet x)).degree y + 1)) =
        ∑ _y : {z : V // z ∈ G.neighborSet x}, d := by
    apply Finset.sum_congr rfl
    intro y _
    rw [degree_induce_neighborSet_eq_card_common]
    exact card_secondLayerBranch_add_common_add_one G x y |>.trans (hreg y.1)
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib] at hbranches
  have hones : (∑ _y : {z : V // z ∈ G.neighborSet x}, 1) = d := by
    simp [hNcardAdj]
  have hds : (∑ _y : {z : V // z ∈ G.neighborSet x}, d) = d * d := by
    simp [hNcardAdj]
  rw [hones, hds] at hbranches
  have hbranches' : (secondLayer G x).card + S + d = d * d := by
    rw [hD]
    omega
  have hpartition :=
    card_externalRepairCandidates_add_card_secondLayer_add_degree_add_one G x
  rw [hreg x] at hpartition
  change (externalRepairCandidates G x).card + (secondLayer G x).card + d + 1 =
    Fintype.card V at hpartition
  change (externalRepairCandidates G x).card + d * d + 1 =
    Fintype.card V + S
  omega

/-- Symmetry of length-three walk counting, expressed through common-neighbour
counts at the two endpoints. -/
theorem sum_card_common_over_neighbors_comm
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (x y : V) :
    (∑ z ∈ G.neighborFinset x,
      (G.neighborFinset z ∩ G.neighborFinset y).card) =
    ∑ z ∈ G.neighborFinset y,
      (G.neighborFinset x ∩ G.neighborFinset z).card := by
  classical
  let A := (G.neighborFinset x).sigma fun z =>
    G.neighborFinset z ∩ G.neighborFinset y
  let B := (G.neighborFinset y).sigma fun z =>
    G.neighborFinset x ∩ G.neighborFinset z
  rw [← Finset.card_sigma, ← Finset.card_sigma]
  change A.card = B.card
  apply Finset.card_bij (fun p _ => ⟨p.2, p.1⟩)
  · intro p hp
    simp only [A, Finset.mem_sigma] at hp
    simp only [B, Finset.mem_sigma]
    have hp2 := Finset.mem_inter.mp hp.2
    exact ⟨hp2.2, Finset.mem_inter.mpr
      ⟨hp.1, (G.mem_neighborFinset p.2 p.1).mpr
        ((G.mem_neighborFinset p.1 p.2).mp hp2.1).symm⟩⟩
  · intro p hp q hq heq
    cases p
    cases q
    cases heq
    rfl
  · intro p hp
    simp only [B, Finset.mem_sigma] at hp
    have hp2 := Finset.mem_inter.mp hp.2
    let q : (z : V) × V := ⟨p.2, p.1⟩
    have hq : q ∈ A := by
      simp only [A, Finset.mem_sigma]
      exact ⟨hp2.1, Finset.mem_inter.mpr
        ⟨(G.mem_neighborFinset p.2 p.1).mpr
          ((G.mem_neighborFinset p.1 p.2).mp hp2.2).symm, hp.1⟩⟩
    exact ⟨q, hq, by simp [q]⟩

end Erdos85
