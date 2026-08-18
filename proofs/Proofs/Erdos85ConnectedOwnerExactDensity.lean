import Proofs.Erdos85BinarySquareConnectedOwnerDensity
import Proofs.Erdos85OrderSixtyFourRegularKernel
import Proofs.Erdos85BinarySquareSameOwnerCenterGridCapacity
import Mathlib.Combinatorics.SimpleGraph.StronglyRegular

/-! # Exact owner density in the connected-defect stratum -/

open SimpleGraph

namespace Erdos85

noncomputable section

theorem sixtyFour_sevenRegular_compl_common_card_of_adj
    (D : SimpleGraph (Fin 64)) [DecidableRel D.Adj]
    (hreg : ∀ x, D.degree x = 7) {x y : Fin 64} (hxy : D.Adj x y) :
    (Dᶜ.neighborFinset x ∩ Dᶜ.neighborFinset y).card =
      50 + (D.neighborFinset x ∩ D.neighborFinset y).card := by
  rw [neighborFinset_compl, neighborFinset_compl,
    compl_neighborFinset_sdiff_inter_eq,
    sdiff_compl_neighborFinset_inter_eq hxy,
    ← Finset.compl_union, Finset.card_compl]
  have hx : (D.neighborFinset x).card = 7 := by
    rw [D.card_neighborFinset_eq_degree, hreg]
  have hy : (D.neighborFinset y).card = 7 := by
    rw [D.card_neighborFinset_eq_degree, hreg]
  have hu := Finset.card_union_add_card_inter
    (D.neighborFinset x) (D.neighborFinset y)
  rw [hx, hy] at hu
  norm_num at hu ⊢
  omega

theorem sixtyFour_sevenRegular_compl_common_card_of_not_adj
    (D : SimpleGraph (Fin 64)) [DecidableRel D.Adj]
    (hreg : ∀ x, D.degree x = 7) {x y : Fin 64}
    (hxy : x ≠ y) (hnxy : ¬ D.Adj x y) :
    (Dᶜ.neighborFinset x ∩ Dᶜ.neighborFinset y).card =
      48 + (D.neighborFinset x ∩ D.neighborFinset y).card := by
  rw [neighborFinset_compl, neighborFinset_compl,
    compl_neighborFinset_sdiff_inter_eq]
  let C := (D.neighborFinset x)ᶜ ∩ (D.neighborFinset y)ᶜ
  have hnyx : ¬ D.Adj y x := fun h => hnxy h.symm
  have hsub : {y} ∪ {x} ⊆ C := by
    intro z hz
    simp only [Finset.mem_union, Finset.mem_singleton] at hz
    rcases hz with rfl | rfl
    · simp [C, hnxy]
    · simp [C, hnyx]
  rw [Finset.card_sdiff_of_subset hsub]
  have hC : C.card = 64 - (D.neighborFinset x ∪ D.neighborFinset y).card := by
    rw [show C = (D.neighborFinset x ∪ D.neighborFinset y)ᶜ by
      ext z
      simp [C], Finset.card_compl]
    norm_num
  have htwo : ({y} ∪ {x} : Finset (Fin 64)).card = 2 := by
    simp [hxy.symm]
  have hx : (D.neighborFinset x).card = 7 := by
    rw [D.card_neighborFinset_eq_degree, hreg]
  have hy : (D.neighborFinset y).card = 7 := by
    rw [D.card_neighborFinset_eq_degree, hreg]
  have hu := Finset.card_union_add_card_inter
    (D.neighborFinset x) (D.neighborFinset y)
  rw [hx, hy] at hu
  rw [hC, htwo]
  omega

/-- With one defect component, its owner color is literally the complement
of the defect graph. -/
theorem binarySquare_regular_oneComponent_ownerGraph_eq_compl
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G)
    (hcount : Fintype.card
      (secondOrderDefectGraph G).ConnectedComponent = 1) :
    ∃ a : (secondOrderDefectGraph G).ConnectedComponent,
      componentOwnerGraph G (secondOrderDefectGraph G) a =
        (secondOrderDefectGraph G)ᶜ := by
  obtain ⟨a, ha⟩ := Fintype.card_eq_one_iff.mp hcount
  refine ⟨a, ?_⟩
  apply SimpleGraph.ext
  funext x y
  by_cases hxy : x = y
  · subst y
    simp
  have howner := not_secondOrderDefect_adj_iff_existsUnique_componentOwnerGraph_adj
    G hfree hxy
  rw [SimpleGraph.compl_adj, and_iff_right hxy]
  apply propext
  constructor
  · intro hadj
    exact howner.mpr ⟨a, hadj, fun c _ => ha c⟩
  · intro hnot
    obtain ⟨c, hc, _⟩ := howner.mp hnot
    simpa [ha c] using hc

/-- Exact refinement of the connected-stratum owner-density theorem. -/
theorem orderSixtyFour_regular_oneComponent_owner_common_exact
    (G : SimpleGraph (Fin 64)) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 (Fin 64) G)
    (hreg : ∀ x, G.degree x = 8)
    (hcount : Fintype.card
      (secondOrderDefectGraph G).ConnectedComponent = 1) :
    ∃ a : (secondOrderDefectGraph G).ConnectedComponent,
      componentOwnerGraph G (secondOrderDefectGraph G) a =
          (secondOrderDefectGraph G)ᶜ ∧
      (∀ {x y}, (secondOrderDefectGraph G).Adj x y →
        ((componentOwnerGraph G (secondOrderDefectGraph G) a).neighborFinset x ∩
          (componentOwnerGraph G (secondOrderDefectGraph G) a).neighborFinset y).card =
            50 + (((secondOrderDefectGraph G).neighborFinset x) ∩
              (secondOrderDefectGraph G).neighborFinset y).card) ∧
      (∀ {x y}, x ≠ y → ¬ (secondOrderDefectGraph G).Adj x y →
        ((componentOwnerGraph G (secondOrderDefectGraph G) a).neighborFinset x ∩
          (componentOwnerGraph G (secondOrderDefectGraph G) a).neighborFinset y).card =
            48 + (((secondOrderDefectGraph G).neighborFinset x) ∩
              (secondOrderDefectGraph G).neighborFinset y).card) := by
  obtain ⟨a, ha⟩ := binarySquare_regular_oneComponent_ownerGraph_eq_compl
    G hfree hcount
  have hDreg : ∀ x, (secondOrderDefectGraph G).degree x = 7 :=
    (orderSixtyFour_regular_defect_kernel G hfree
      (fun x => by rw [hreg]) (fun {_ _} _ => Or.inl (hreg _))).2.2.1
  refine ⟨a, ha, ?_, ?_⟩
  · intro x y hxy
    have hnx :
        (componentOwnerGraph G (secondOrderDefectGraph G) a).neighborFinset x =
          ((secondOrderDefectGraph G)ᶜ).neighborFinset x := by
      ext z
      simp only [SimpleGraph.mem_neighborFinset]
      exact iff_of_eq (congrFun (congrFun
        (congrArg SimpleGraph.Adj ha) x) z)
    have hny :
        (componentOwnerGraph G (secondOrderDefectGraph G) a).neighborFinset y =
          ((secondOrderDefectGraph G)ᶜ).neighborFinset y := by
      ext z
      simp only [SimpleGraph.mem_neighborFinset]
      exact iff_of_eq (congrFun (congrFun
        (congrArg SimpleGraph.Adj ha) y) z)
    rw [hnx, hny]
    exact sixtyFour_sevenRegular_compl_common_card_of_adj
      (secondOrderDefectGraph G) hDreg hxy
  · intro x y hne hnot
    have hnx :
        (componentOwnerGraph G (secondOrderDefectGraph G) a).neighborFinset x =
          ((secondOrderDefectGraph G)ᶜ).neighborFinset x := by
      ext z
      simp only [SimpleGraph.mem_neighborFinset]
      exact iff_of_eq (congrFun (congrFun
        (congrArg SimpleGraph.Adj ha) x) z)
    have hny :
        (componentOwnerGraph G (secondOrderDefectGraph G) a).neighborFinset y =
          ((secondOrderDefectGraph G)ᶜ).neighborFinset y := by
      ext z
      simp only [SimpleGraph.mem_neighborFinset]
      exact iff_of_eq (congrFun (congrFun
        (congrArg SimpleGraph.Adj ha) y) z)
    rw [hnx, hny]
    exact sixtyFour_sevenRegular_compl_common_card_of_not_adj
      (secondOrderDefectGraph G) hDreg hne hnot

/-- On a defect edge in the connected stratum, the unique owner route and
the defect cells split the `8×8` selector grid exactly. -/
theorem orderSixtyFour_regular_oneComponent_defectEdge_centerGrid_exact
    (G : SimpleGraph (Fin 64)) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 (Fin 64) G)
    (hreg : ∀ x, G.degree x = 8)
    (hcount : Fintype.card
      (secondOrderDefectGraph G).ConnectedComponent = 1) :
    ∃ a : (secondOrderDefectGraph G).ConnectedComponent,
      ∀ {x y}, (secondOrderDefectGraph G).Adj x y →
        (coloredTwoStepMiddles
          (componentOwnerGraph G (secondOrderDefectGraph G) a)
          (componentOwnerGraph G (secondOrderDefectGraph G) a) x y).card =
            50 + (((secondOrderDefectGraph G).neighborFinset x) ∩
              (secondOrderDefectGraph G).neighborFinset y).card ∧
        (sameOwnerDefectCenterPairs G a x y).card +
            (((secondOrderDefectGraph G).neighborFinset x) ∩
              (secondOrderDefectGraph G).neighborFinset y).card = 14 := by
  obtain ⟨a, _ha, hadjExact, _⟩ :=
    orderSixtyFour_regular_oneComponent_owner_common_exact
      G hfree hreg hcount
  refine ⟨a, ?_⟩
  intro x y hxy
  let O := componentOwnerGraph G (secondOrderDefectGraph G) a
  have hcolored : coloredTwoStepMiddles O O x y =
      O.neighborFinset x ∩ O.neighborFinset y := by
    ext z
    simp only [coloredTwoStepMiddles, Finset.mem_filter, Finset.mem_univ,
      true_and, Finset.mem_inter, SimpleGraph.mem_neighborFinset]
    exact and_congr_right fun _ => O.adj_comm z y
  have hroute : (coloredTwoStepMiddles O O x y).card =
      50 + (((secondOrderDefectGraph G).neighborFinset x) ∩
        (secondOrderDefectGraph G).neighborFinset y).card := by
    rw [hcolored]
    exact hadjExact hxy
  have hownerSize : a.supp.ncard = 8 * 8 := by
    obtain ⟨m, _E, hm, hma⟩ :=
      orderSixtyFour_regular_one_defectComponent_partition_shape
        G hfree hreg hcount
    have haE : a = _E.symm 0 := by
      apply _E.injective
      exact Subsingleton.elim _ _
    rw [hm a, haE, hma]
  have hledger :=
    binarySquare_regular_sameOwner_defectEdge_card_add_defectCells_eq_sq
      G hfree (q := 8) (by norm_num) hreg (by norm_num) a hownerSize hxy
  change (coloredTwoStepMiddles O O x y).card +
    (sameOwnerDefectCenterPairs G a x y).card = 8 * 8 at hledger
  refine ⟨hroute, ?_⟩
  omega

end

end Erdos85
