import Proofs.Erdos85NearTwinLitePrivateOwnerBudget

/-! # Specializing λ=5 private owner budgets to defect components -/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- On one defect component, filtering complement neighbors by their
canonical owner is exactly the corresponding restricted owner-factor row. -/
theorem filter_complNeighbor_by_owner_eq_restrictedOwner_neighborFinset
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G)
    (d : (secondOrderDefectGraph G).ConnectedComponent)
    (x : d.supp)
    (base owner : (secondOrderDefectGraph G).ConnectedComponent) :
    ((((secondOrderDefectGraph G).induce d.supp)ᶜ.neighborFinset x).filter
      fun z => nondefectPairOwnerOrBase G hfree base x.1 z.1 = owner) =
      (restrictedComponentOwnerGraph G d owner).neighborFinset x := by
  classical
  let D := secondOrderDefectGraph G
  let H := D.induce d.supp
  ext z
  constructor
  · intro hz
    have hzdata := Finset.mem_filter.mp hz
    have hcomp := (Hᶜ.mem_neighborFinset x z).mp hzdata.1
    have hne : x.1 ≠ z.1 := fun h => hcomp.1 (Subtype.ext h)
    have hnotD : ¬ D.Adj x.1 z.1 := by
      intro hD
      exact hcomp.2 (by simpa [H, D] using hD)
    have hcanon : nondefectPairOwner G hfree hne hnotD = owner := by
      rw [nondefectPairOwnerOrBase, dif_pos hne, dif_pos hnotD] at hzdata
      exact hzdata.2
    apply ((restrictedComponentOwnerGraph G d owner).mem_neighborFinset x z).mpr
    change (componentOwnerGraph G D owner).Adj x.1 z.1
    rw [← hcanon]
    exact nondefectPairOwner_adj G hfree hne hnotD
  · intro hz
    have hadj := ((restrictedComponentOwnerGraph G d owner).mem_neighborFinset
      x z).mp hz
    have howner : (componentOwnerGraph G D owner).Adj x.1 z.1 := hadj
    have hne : x.1 ≠ z.1 := howner.ne
    have hnotD : ¬ D.Adj x.1 z.1 := by
      intro hD
      have hdis := componentNeighborFinset_disjoint_of_secondOrderDefect_adj
        G hfree hD owner
      have hdata := (componentOwnerGraph_adj G D owner x.1 z.1).mp howner
      obtain ⟨w, hw⟩ := hdata.2
      exact (Finset.disjoint_left.mp hdis)
        (Finset.mem_inter.mp hw).1 (Finset.mem_inter.mp hw).2
    have hHnot : ¬ H.Adj x z := by simpa [H, D] using hnotD
    have hcomp : Hᶜ.Adj x z := ⟨fun h => hne (congrArg Subtype.val h), hHnot⟩
    apply Finset.mem_filter.mpr
    refine ⟨(Hᶜ.mem_neighborFinset x z).mpr hcomp, ?_⟩
    rw [nondefectPairOwnerOrBase, dif_pos hne, dif_pos hnotD]
    exact (nondefectPairOwner_eq_of_adj
      G hfree hne hnotD owner howner).symm

/-- Removing the base edge from a degree-two owner row leaves one base-color
edge and two edges of every other owner color on the core/private residual. -/
theorem residual_owner_color_counts
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G)
    (d : (secondOrderDefectGraph G).ConnectedComponent)
    (x y : d.supp) (hxy : x ≠ y)
    (hnot : ¬ ((secondOrderDefectGraph G).induce d.supp).Adj x y)
    (base : (secondOrderDefectGraph G).ConnectedComponent)
    (hbase : (restrictedComponentOwnerGraph G d base).Adj x y)
    (hdeg : ∀ owner,
      (restrictedComponentOwnerGraph G d owner).degree x = 2) :
    let H := (secondOrderDefectGraph G).induce d.supp
    let R := Hᶜ.neighborFinset x ∩ Hᶜ.neighborFinset y
    let P := H.neighborFinset y \ H.neighborFinset x
    let color := fun z : d.supp =>
      nondefectPairOwnerOrBase G hfree base x.1 z.1
    ((R ∪ P).filter fun z => color z = base).card = 1 ∧
      ∀ owner, owner ≠ base →
        ((R ∪ P).filter fun z => color z = owner).card = 2 := by
  classical
  let D := secondOrderDefectGraph G
  let H := D.induce d.supp
  let R := Hᶜ.neighborFinset x ∩ Hᶜ.neighborFinset y
  let P := H.neighborFinset y \ H.neighborFinset x
  let color := fun z : d.supp =>
    nondefectPairOwnerOrBase G hfree base x.1 z.1
  have hsplit :=
    compl_neighborFinset_eq_insert_complCommon_union_reversePrivate
      H hxy hnot
  change Hᶜ.neighborFinset x = insert y (R ∪ P) at hsplit
  have hyQ : y ∉ R ∪ P := by
    simp only [R, P, Finset.mem_union, Finset.mem_inter,
      Finset.mem_sdiff, SimpleGraph.mem_neighborFinset]
    rintro (hR | hP)
    · exact Hᶜ.loopless.irrefl y hR.2
    · exact H.loopless.irrefl y hP.1
  have hQ : R ∪ P = (Hᶜ.neighborFinset x).erase y := by
    rw [hsplit, Finset.erase_insert]
    exact hyQ
  have hfilter (owner : D.ConnectedComponent) :
      ((R ∪ P).filter fun z => color z = owner) =
        ((restrictedComponentOwnerGraph G d owner).neighborFinset x).erase y := by
    rw [hQ, Finset.filter_erase]
    rw [show (Hᶜ.neighborFinset x).filter (fun z => color z = owner) =
        (restrictedComponentOwnerGraph G d owner).neighborFinset x by
      simpa [H, D, color] using
        filter_complNeighbor_by_owner_eq_restrictedOwner_neighborFinset
          G hfree d x base owner]
  have hyBase : y ∈
      (restrictedComponentOwnerGraph G d base).neighborFinset x :=
    ((restrictedComponentOwnerGraph G d base).mem_neighborFinset x y).mpr hbase
  constructor
  · rw [hfilter base, Finset.card_erase_of_mem hyBase,
      (restrictedComponentOwnerGraph G d base).card_neighborFinset_eq_degree,
      hdeg base]
  · intro owner hob
    have hyNot : y ∉
        (restrictedComponentOwnerGraph G d owner).neighborFinset x := by
      intro hy
      have howner := ((restrictedComponentOwnerGraph G d owner).mem_neighborFinset
        x y).mp hy
      have hbaseGlobal : (componentOwnerGraph G D base).Adj x.1 y.1 := hbase
      have hownerGlobal : (componentOwnerGraph G D owner).Adj x.1 y.1 := howner
      have hxyval : x.1 ≠ y.1 := fun h => hxy (Subtype.ext h)
      have hnotD : ¬ D.Adj x.1 y.1 := by simpa [D] using hnot
      have hb := nondefectPairOwner_eq_of_adj
        G hfree hxyval hnotD base hbaseGlobal
      have ho := nondefectPairOwner_eq_of_adj
        G hfree hxyval hnotD owner hownerGlobal
      exact hob (ho.trans hb.symm)
    rw [hfilter owner, Finset.erase_eq_of_notMem hyNot,
      (restrictedComponentOwnerGraph G d owner).card_neighborFinset_eq_degree,
      hdeg owner]

/-- The symmetric residual census at the right endpoint of the base edge. -/
theorem residual_owner_color_counts_right
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G)
    (d : (secondOrderDefectGraph G).ConnectedComponent)
    (x y : d.supp) (hxy : x ≠ y)
    (hnot : ¬ ((secondOrderDefectGraph G).induce d.supp).Adj x y)
    (base : (secondOrderDefectGraph G).ConnectedComponent)
    (hbase : (restrictedComponentOwnerGraph G d base).Adj x y)
    (hdeg : ∀ owner,
      (restrictedComponentOwnerGraph G d owner).degree y = 2) :
    let H := (secondOrderDefectGraph G).induce d.supp
    let R := Hᶜ.neighborFinset x ∩ Hᶜ.neighborFinset y
    let P := H.neighborFinset x \ H.neighborFinset y
    let color := fun z : d.supp =>
      nondefectPairOwnerOrBase G hfree base y.1 z.1
    ((R ∪ P).filter fun z => color z = base).card = 1 ∧
      ∀ owner, owner ≠ base →
        ((R ∪ P).filter fun z => color z = owner).card = 2 := by
  have hnot' : ¬ ((secondOrderDefectGraph G).induce d.supp).Adj y x := by
    intro hadj
    exact hnot hadj.symm
  simpa [Finset.inter_comm] using
    residual_owner_color_counts G hfree d y x hxy.symm hnot' base hbase.symm hdeg

end

end Erdos85
