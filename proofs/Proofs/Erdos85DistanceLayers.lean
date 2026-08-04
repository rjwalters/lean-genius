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

end Erdos85
