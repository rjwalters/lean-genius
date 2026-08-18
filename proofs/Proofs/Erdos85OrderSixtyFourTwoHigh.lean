import Proofs.Erdos85OrderSixtyFourBranchReduction

/-! # The two-high order-64 branch -/

open SimpleGraph

namespace Erdos85

/-- In a `C₄`-free graph, two distinct neighbors of a base vertex have that
base as their unique common neighbor. -/
theorem orderSixtyFour_common_neighbor_eq_base
    (G : SimpleGraph (Fin 64)) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 (Fin 64) G)
    {a y z : Fin 64}
    (hay : G.Adj a y) (haz : G.Adj a z) (hyz : y ≠ z) :
    G.neighborFinset y ∩ G.neighborFinset z = {a} := by
  have hamem : a ∈ G.neighborFinset y ∩ G.neighborFinset z := by
    rw [Finset.mem_inter, SimpleGraph.mem_neighborFinset,
      SimpleGraph.mem_neighborFinset]
    exact ⟨hay.symm, haz.symm⟩
  have hle : (G.neighborFinset y ∩ G.neighborFinset z).card ≤ 1 :=
    card_inter_neighborFinset_le_one hfree hyz
  have hone : (G.neighborFinset y ∩ G.neighborFinset z).card = 1 := by
    have hpos : 0 < (G.neighborFinset y ∩ G.neighborFinset z).card :=
      Finset.card_pos.mpr ⟨a, hamem⟩
    omega
  obtain ⟨w, hw⟩ := Finset.card_eq_one.mp hone
  have haw : a = w := by
    rw [hw, Finset.mem_singleton] at hamem
    exact hamem
  simpa [haw] using hw

/-- In the two-high branch there is a unique vertex incident with both high
vertices.  This canonical double-contact vertex is the pivot for the ensuing
slide-saturation geometry. -/
theorem orderSixtyFour_existsUnique_two_high_contact
    (G : SimpleGraph (Fin 64)) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 (Fin 64) G)
    (hmin : ∀ x : Fin 64, 8 ≤ G.degree x)
    (hcover : ∀ {u v}, G.Adj u v →
      G.degree u = 8 ∨ G.degree v = 8)
    (hh : (squareOrderHighVertices G 8).card = 2) :
    ∃! x : Fin 64,
      (G.neighborFinset x ∩ squareOrderHighVertices G 8).card = 2 := by
  have hp := orderSixtyFour_two_high_graph_profile G hfree hmin hcover hh
  dsimp only at hp
  let S := Finset.univ.filter fun x : Fin 64 =>
    (G.neighborFinset x ∩ squareOrderHighVertices G 8).card = 2
  have hScard : S.card = 1 := hp.2.1
  obtain ⟨x, hxS⟩ := Finset.card_eq_one.mp hScard
  have hxmem : x ∈ S := by simp [hxS]
  refine ⟨x, (Finset.mem_filter.mp hxmem).2, ?_⟩
  intro y hy
  have hymem : y ∈ S := Finset.mem_filter.mpr ⟨Finset.mem_univ y, hy⟩
  rw [hxS] at hymem
  simpa using hymem

/-- Geometrically, the canonical double-contact vertex is adjacent to the
entire two-vertex high sector, and it is the unique vertex with this property. -/
theorem orderSixtyFour_existsUnique_neighbor_inter_high_eq_high
    (G : SimpleGraph (Fin 64)) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 (Fin 64) G)
    (hmin : ∀ x : Fin 64, 8 ≤ G.degree x)
    (hcover : ∀ {u v}, G.Adj u v →
      G.degree u = 8 ∨ G.degree v = 8)
    (hh : (squareOrderHighVertices G 8).card = 2) :
    ∃! x : Fin 64,
      G.neighborFinset x ∩ squareOrderHighVertices G 8 =
        squareOrderHighVertices G 8 := by
  obtain ⟨x, hx, hunique⟩ :=
    orderSixtyFour_existsUnique_two_high_contact G hfree hmin hcover hh
  have hxEq : G.neighborFinset x ∩ squareOrderHighVertices G 8 =
      squareOrderHighVertices G 8 :=
    Finset.eq_of_subset_of_card_le Finset.inter_subset_right (by omega)
  refine ⟨x, hxEq, ?_⟩
  intro y hy
  apply hunique y
  rw [hy, hh]

/-- The canonical common neighbor of the two high vertices is low: tight
edge cover forces its degree to be exactly eight.  This identifies the
double-contact pivot inside the low sector, which is the degree direction
needed by slide saturation. -/
theorem orderSixtyFour_existsUnique_low_neighbor_inter_high_eq_high
    (G : SimpleGraph (Fin 64)) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 (Fin 64) G)
    (hmin : ∀ x : Fin 64, 8 ≤ G.degree x)
    (hcover : ∀ {u v}, G.Adj u v →
      G.degree u = 8 ∨ G.degree v = 8)
    (hh : (squareOrderHighVertices G 8).card = 2) :
    ∃! x : Fin 64,
      G.neighborFinset x ∩ squareOrderHighVertices G 8 =
          squareOrderHighVertices G 8 ∧
        G.degree x = 8 := by
  obtain ⟨x, hx, hunique⟩ :=
    orderSixtyFour_existsUnique_neighbor_inter_high_eq_high
      G hfree hmin hcover hh
  have hHne : squareOrderHighVertices G 8 ≠ ∅ := by
    intro hzero
    rw [hzero] at hh
    simp at hh
  obtain ⟨a, ha⟩ := Finset.nonempty_iff_ne_empty.mpr hHne
  have hax : a ∈ G.neighborFinset x := by
    have : a ∈ G.neighborFinset x ∩ squareOrderHighVertices G 8 := by
      rw [hx]
      exact ha
    exact (Finset.mem_inter.mp this).1
  have hAdj : G.Adj x a := by
    simpa [SimpleGraph.mem_neighborFinset] using hax
  have haDegree : G.degree a = 9 := by
    simpa [squareOrderHighVertices] using (Finset.mem_filter.mp ha).2
  have hxDegree : G.degree x = 8 := by
    rcases hcover hAdj with hxLow | haLow
    · exact hxLow
    · omega
  refine ⟨x, ⟨hx, hxDegree⟩, ?_⟩
  intro y hy
  exact hunique y hy.1

/-- Concrete skeleton of the two-high branch: the high sector consists of
two distinct degree-nine vertices, and their common-neighbor set is the
singleton containing the canonical degree-eight pivot. -/
theorem orderSixtyFour_two_high_common_neighbor_skeleton
    (G : SimpleGraph (Fin 64)) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 (Fin 64) G)
    (hmin : ∀ x : Fin 64, 8 ≤ G.degree x)
    (hcover : ∀ {u v}, G.Adj u v →
      G.degree u = 8 ∨ G.degree v = 8)
    (hh : (squareOrderHighVertices G 8).card = 2) :
    ∃ a b x : Fin 64,
      a ≠ b ∧
      squareOrderHighVertices G 8 = {a, b} ∧
      G.degree a = 9 ∧ G.degree b = 9 ∧ ¬ G.Adj a b ∧
      G.degree x = 8 ∧
      G.neighborFinset a ∩ G.neighborFinset b = {x} := by
  obtain ⟨a, b, hab, hH⟩ := Finset.card_eq_two.mp hh
  obtain ⟨x, hx, _⟩ :=
    orderSixtyFour_existsUnique_low_neighbor_inter_high_eq_high
      G hfree hmin hcover hh
  have haH : a ∈ squareOrderHighVertices G 8 := by
    rw [hH]
    simp
  have hbH : b ∈ squareOrderHighVertices G 8 := by
    rw [hH]
    simp
  have haDegree : G.degree a = 9 := by
    simpa [squareOrderHighVertices] using (Finset.mem_filter.mp haH).2
  have hbDegree : G.degree b = 9 := by
    simpa [squareOrderHighVertices] using (Finset.mem_filter.mp hbH).2
  have hnab : ¬ G.Adj a b := by
    intro habAdj
    rcases hcover habAdj with haLow | hbLow <;> omega
  have hxa : G.Adj x a := by
    have haInter : a ∈
        G.neighborFinset x ∩ squareOrderHighVertices G 8 := by
      rw [hx.1]
      exact haH
    simpa [SimpleGraph.mem_neighborFinset] using
      (Finset.mem_inter.mp haInter).1
  have hxb : G.Adj x b := by
    have hbInter : b ∈
        G.neighborFinset x ∩ squareOrderHighVertices G 8 := by
      rw [hx.1]
      exact hbH
    simpa [SimpleGraph.mem_neighborFinset] using
      (Finset.mem_inter.mp hbInter).1
  have hxmem : x ∈ G.neighborFinset a ∩ G.neighborFinset b := by
    rw [Finset.mem_inter, SimpleGraph.mem_neighborFinset,
      SimpleGraph.mem_neighborFinset]
    exact ⟨hxa.symm, hxb.symm⟩
  have hle :
      (G.neighborFinset a ∩ G.neighborFinset b).card ≤ 1 :=
    card_inter_neighborFinset_le_one hfree hab
  have hone :
      (G.neighborFinset a ∩ G.neighborFinset b).card = 1 := by
    have hpos : 0 <
        (G.neighborFinset a ∩ G.neighborFinset b).card :=
      Finset.card_pos.mpr ⟨x, hxmem⟩
    omega
  obtain ⟨w, hw⟩ := Finset.card_eq_one.mp hone
  have hxw : x = w := by
    rw [hw, Finset.mem_singleton] at hxmem
    exact hxmem
  refine ⟨a, b, x, hab, hH, haDegree, hbDegree, hnab, hx.2, ?_⟩
  simpa [hxw] using hw

/-- Removing the common pivot leaves two disjoint eight-vertex wings, one
for each high vertex.  These sixteen vertices are precisely the geometric
source of the numerical single-contact count below. -/
theorem orderSixtyFour_two_high_disjoint_eight_wings
    (G : SimpleGraph (Fin 64)) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 (Fin 64) G)
    (hmin : ∀ x : Fin 64, 8 ≤ G.degree x)
    (hcover : ∀ {u v}, G.Adj u v →
      G.degree u = 8 ∨ G.degree v = 8)
    (hh : (squareOrderHighVertices G 8).card = 2) :
    ∃ a b x : Fin 64,
      a ≠ b ∧
      squareOrderHighVertices G 8 = {a, b} ∧
      G.degree x = 8 ∧
      (G.neighborFinset a \ {x}).card = 8 ∧
      (G.neighborFinset b \ {x}).card = 8 ∧
      Disjoint (G.neighborFinset a \ {x})
        (G.neighborFinset b \ {x}) := by
  obtain ⟨a, b, x, hab, hH, haDegree, hbDegree, _hnab, hxDegree,
      hcommon⟩ :=
    orderSixtyFour_two_high_common_neighbor_skeleton
      G hfree hmin hcover hh
  have hxa : x ∈ G.neighborFinset a := by
    have hxmem : x ∈ G.neighborFinset a ∩ G.neighborFinset b := by
      rw [hcommon]
      simp
    exact (Finset.mem_inter.mp hxmem).1
  have hxb : x ∈ G.neighborFinset b := by
    have hxmem : x ∈ G.neighborFinset a ∩ G.neighborFinset b := by
      rw [hcommon]
      simp
    exact (Finset.mem_inter.mp hxmem).2
  have haWing : (G.neighborFinset a \ {x}).card = 8 := by
    rw [Finset.sdiff_singleton_eq_erase, Finset.card_erase_of_mem hxa,
      G.card_neighborFinset_eq_degree, haDegree]
  have hbWing : (G.neighborFinset b \ {x}).card = 8 := by
    rw [Finset.sdiff_singleton_eq_erase, Finset.card_erase_of_mem hxb,
      G.card_neighborFinset_eq_degree, hbDegree]
  have hwings : Disjoint (G.neighborFinset a \ {x})
      (G.neighborFinset b \ {x}) := by
    rw [Finset.disjoint_left]
    intro y hya hyb
    have hyCommon : y ∈ G.neighborFinset a ∩ G.neighborFinset b :=
      Finset.mem_inter.mpr
        ⟨(Finset.mem_sdiff.mp hya).1, (Finset.mem_sdiff.mp hyb).1⟩
    have hyx : y = x := by
      rw [hcommon, Finset.mem_singleton] at hyCommon
      exact hyCommon
    exact (Finset.mem_sdiff.mp hya).2 (by simp [hyx])
  exact ⟨a, b, x, hab, hH, hxDegree, haWing, hbWing, hwings⟩

/-- The two concrete wings are exactly the vertices with one high neighbor. -/
theorem orderSixtyFour_two_high_single_contact_eq_wings
    (G : SimpleGraph (Fin 64)) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 (Fin 64) G)
    (hmin : ∀ x : Fin 64, 8 ≤ G.degree x)
    (hcover : ∀ {u v}, G.Adj u v →
      G.degree u = 8 ∨ G.degree v = 8)
    (hh : (squareOrderHighVertices G 8).card = 2) :
    ∃ a b x : Fin 64,
      a ≠ b ∧
      squareOrderHighVertices G 8 = {a, b} ∧
      (Finset.univ.filter fun y : Fin 64 =>
          (G.neighborFinset y ∩ squareOrderHighVertices G 8).card = 1) =
        (G.neighborFinset a \ {x}) ∪ (G.neighborFinset b \ {x}) := by
  obtain ⟨a, b, x, hab, hH, _hxDegree, haWing, hbWing, hwings⟩ :=
    orderSixtyFour_two_high_disjoint_eight_wings
      G hfree hmin hcover hh
  let S := Finset.univ.filter fun y : Fin 64 =>
    (G.neighborFinset y ∩ squareOrderHighVertices G 8).card = 1
  let W := (G.neighborFinset a \ {x}) ∪ (G.neighborFinset b \ {x})
  have hWsub : W ⊆ S := by
    intro y hyW
    rw [Finset.mem_union] at hyW
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_univ y, ?_⟩
    rcases hyW with hya | hyb
    · have hyaAdj : G.Adj a y := by
        simpa [SimpleGraph.mem_neighborFinset] using
          (Finset.mem_sdiff.mp hya).1
      have hyx : y ≠ x := by
        simpa using (Finset.mem_sdiff.mp hya).2
      have hnyb : ¬ G.Adj y b := by
        intro hybAdj
        have hybWing : y ∈ G.neighborFinset b \ {x} :=
          Finset.mem_sdiff.mpr
            ⟨by simpa [SimpleGraph.mem_neighborFinset] using hybAdj.symm,
              by simpa⟩
        exact (Finset.disjoint_left.mp hwings hya hybWing)
      simp [hH, SimpleGraph.mem_neighborFinset, hyaAdj.symm, hnyb]
    · have hybAdj : G.Adj b y := by
        simpa [SimpleGraph.mem_neighborFinset] using
          (Finset.mem_sdiff.mp hyb).1
      have hyx : y ≠ x := by
        simpa using (Finset.mem_sdiff.mp hyb).2
      have hnya : ¬ G.Adj y a := by
        intro hyaAdj
        have hyaWing : y ∈ G.neighborFinset a \ {x} :=
          Finset.mem_sdiff.mpr
            ⟨by simpa [SimpleGraph.mem_neighborFinset] using hyaAdj.symm,
              by simpa⟩
        exact (Finset.disjoint_left.mp hwings hyaWing hyb)
      simp [hH, SimpleGraph.mem_neighborFinset, hybAdj.symm, hnya]
  have hWcard : W.card = 16 := by
    dsimp [W]
    rw [Finset.card_union_of_disjoint hwings, haWing, hbWing]
  have hScard : S.card = 16 := by
    have hp := orderSixtyFour_two_high_graph_profile G hfree hmin hcover hh
    exact hp.2.2
  have hSW : S = W :=
    Finset.eq_of_subset_of_card_le hWsub (by omega) |>.symm
  exact ⟨a, b, x, hab, hH, hSW⟩

/-- Same-wing pairs have no additional common neighbor: their unique common
neighbor is the high vertex defining that wing. -/
theorem orderSixtyFour_two_high_wing_pair_rigidity
    (G : SimpleGraph (Fin 64)) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 (Fin 64) G)
    (hmin : ∀ x : Fin 64, 8 ≤ G.degree x)
    (hcover : ∀ {u v}, G.Adj u v →
      G.degree u = 8 ∨ G.degree v = 8)
    (hh : (squareOrderHighVertices G 8).card = 2) :
    ∃ a b x : Fin 64,
      a ≠ b ∧
      squareOrderHighVertices G 8 = {a, b} ∧
      (∀ y ∈ G.neighborFinset a \ {x},
        ∀ z ∈ G.neighborFinset a \ {x}, y ≠ z →
          G.neighborFinset y ∩ G.neighborFinset z = {a}) ∧
      (∀ y ∈ G.neighborFinset b \ {x},
        ∀ z ∈ G.neighborFinset b \ {x}, y ≠ z →
          G.neighborFinset y ∩ G.neighborFinset z = {b}) := by
  obtain ⟨a, b, x, hab, hH, _hxDegree, _haWing, _hbWing, _hwings⟩ :=
    orderSixtyFour_two_high_disjoint_eight_wings
      G hfree hmin hcover hh
  refine ⟨a, b, x, hab, hH, ?_, ?_⟩
  · intro y hy z hz hyz
    have hay : G.Adj a y := by
      simpa [SimpleGraph.mem_neighborFinset] using
        (Finset.mem_sdiff.mp hy).1
    have haz : G.Adj a z := by
      simpa [SimpleGraph.mem_neighborFinset] using
        (Finset.mem_sdiff.mp hz).1
    exact orderSixtyFour_common_neighbor_eq_base G hfree hay haz hyz
  · intro y hy z hz hyz
    have hby : G.Adj b y := by
      simpa [SimpleGraph.mem_neighborFinset] using
        (Finset.mem_sdiff.mp hy).1
    have hbz : G.Adj b z := by
      simpa [SimpleGraph.mem_neighborFinset] using
        (Finset.mem_sdiff.mp hz).1
    exact orderSixtyFour_common_neighbor_eq_base G hfree hby hbz hyz

/-- The same branch has exactly sixteen single-contact vertices. -/
theorem orderSixtyFour_card_one_high_contact_eq_sixteen
    (G : SimpleGraph (Fin 64)) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 (Fin 64) G)
    (hmin : ∀ x : Fin 64, 8 ≤ G.degree x)
    (hcover : ∀ {u v}, G.Adj u v →
      G.degree u = 8 ∨ G.degree v = 8)
    (hh : (squareOrderHighVertices G 8).card = 2) :
    (Finset.univ.filter fun x : Fin 64 =>
      (G.neighborFinset x ∩ squareOrderHighVertices G 8).card = 1).card = 16 := by
  have hp := orderSixtyFour_two_high_graph_profile G hfree hmin hcover hh
  exact hp.2.2

end Erdos85
