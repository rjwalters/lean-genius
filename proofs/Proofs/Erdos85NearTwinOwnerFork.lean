import Proofs.Erdos85NearTwinNoRainbowSaturation
import Proofs.Erdos85BinarySquareSizeTwoOwnerFactorization
import Proofs.Erdos85BinarySquareOwnerRainbowSymmetry
import Proofs.Erdos85BinarySquareCenteredComponentLaplacian

/-! # Owner forks forced by defect near-twins -/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- Canonical owner color of a non-defect pair. -/
def nondefectPairOwner
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) {x y : V} (hxy : x ≠ y)
    (hnotD : ¬ (secondOrderDefectGraph G).Adj x y) :
    (secondOrderDefectGraph G).ConnectedComponent :=
  Classical.choose
    ((not_secondOrderDefect_adj_iff_existsUnique_componentOwnerGraph_adj
      G hfree hxy).mp hnotD)

/-- The canonical owner owns its pair. -/
theorem nondefectPairOwner_adj
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) {x y : V} (hxy : x ≠ y)
    (hnotD : ¬ (secondOrderDefectGraph G).Adj x y) :
    (componentOwnerGraph G (secondOrderDefectGraph G)
      (nondefectPairOwner G hfree hxy hnotD)).Adj x y := by
  exact Classical.choose_spec
    ((not_secondOrderDefect_adj_iff_existsUnique_componentOwnerGraph_adj
      G hfree hxy).mp hnotD) |>.1

/-- Any owner of a non-defect pair equals its canonical owner. -/
theorem nondefectPairOwner_eq_of_adj
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) {x y : V} (hxy : x ≠ y)
    (hnotD : ¬ (secondOrderDefectGraph G).Adj x y)
    (owner : (secondOrderDefectGraph G).ConnectedComponent)
    (howner : (componentOwnerGraph G (secondOrderDefectGraph G) owner).Adj x y) :
    owner = nondefectPairOwner G hfree hxy hnotD := by
  exact (Classical.choose_spec
    ((not_secondOrderDefect_adj_iff_existsUnique_componentOwnerGraph_adj
      G hfree hxy).mp hnotD) |>.2) owner howner

/-- Six complement-common closures around a non-defect edge force a repeated
non-base owner fork whenever the four owner colors are 2-factors and the
source component contains no rainbow owner triangle. -/
theorem exists_repeatedOwnerFork_of_sixCore_noRainbow
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (d : (secondOrderDefectGraph G).ConnectedComponent)
    (x y : d.supp) (hxy : x ≠ y)
    (R : Finset d.supp) (hRcard : R.card = 6)
    (left right : d.supp →
      (secondOrderDefectGraph G).ConnectedComponent)
    (base : (secondOrderDefectGraph G).ConnectedComponent)
    (hbase : (restrictedComponentOwnerGraph G d base).Adj x y)
    (hleft : ∀ r ∈ R,
      (restrictedComponentOwnerGraph G d (left r)).Adj x r)
    (hright : ∀ r ∈ R,
      (restrictedComponentOwnerGraph G d (right r)).Adj y r)
    (hrx : ∀ r ∈ R, r ≠ x) (hry : ∀ r ∈ R, r ≠ y)
    (hdeg : ∀ owner z,
      (restrictedComponentOwnerGraph G d owner).degree z = 2)
    (hcount : Fintype.card
      (secondOrderDefectGraph G).ConnectedComponent = 4)
    (hno : ∀ a b c,
      a ≠ b → a ≠ c → b ≠ c → ¬ routingOwnerRainbow G d a b c) :
    ∃ owner r₁ r₂, owner ≠ base ∧ r₁ ≠ r₂ ∧ r₁ ∈ R ∧ r₂ ∈ R ∧
      (restrictedComponentOwnerGraph G d owner).Adj x r₁ ∧
      (restrictedComponentOwnerGraph G d owner).Adj y r₁ ∧
      (restrictedComponentOwnerGraph G d owner).Adj x r₂ ∧
      (restrictedComponentOwnerGraph G d owner).Adj y r₂ := by
  classical
  let B := restrictedComponentOwnerGraph G d base
  have hyB : y ∈ B.neighborFinset x := (B.mem_neighborFinset x y).mpr hbase
  have hxB : x ∈ B.neighborFinset y :=
    (B.mem_neighborFinset y x).mpr hbase.symm
  have hleftBudget : (R.filter fun r => left r = base).card ≤ 1 := by
    have hsub : (R.filter fun r => left r = base) ⊆
        (B.neighborFinset x).erase y := by
      intro r hr
      have hrdata := Finset.mem_filter.mp hr
      have hadj := hleft r hrdata.1
      rw [hrdata.2] at hadj
      exact Finset.mem_erase.mpr
        ⟨hry r hrdata.1, (B.mem_neighborFinset x r).mpr hadj⟩
    calc
      _ ≤ ((B.neighborFinset x).erase y).card := Finset.card_le_card hsub
      _ = 1 := by
        rw [Finset.card_erase_of_mem hyB, B.card_neighborFinset_eq_degree,
          hdeg base x]
  have hrightBudget : (R.filter fun r => right r = base).card ≤ 1 := by
    have hsub : (R.filter fun r => right r = base) ⊆
        (B.neighborFinset y).erase x := by
      intro r hr
      have hrdata := Finset.mem_filter.mp hr
      have hadj := hright r hrdata.1
      rw [hrdata.2] at hadj
      exact Finset.mem_erase.mpr
        ⟨hrx r hrdata.1, (B.mem_neighborFinset y r).mpr hadj⟩
    calc
      _ ≤ ((B.neighborFinset y).erase x).card := Finset.card_le_card hsub
      _ = 1 := by
        rw [Finset.card_erase_of_mem hxB, B.card_neighborFinset_eq_degree,
          hdeg base y]
  have hno' : ∀ r ∈ R,
      left r = right r ∨ left r = base ∨ right r = base := by
    intro r hr
    by_contra hall
    push Not at hall
    exact (hno (left r) (right r) base hall.1 hall.2.1 hall.2.2)
      ⟨x, r, y, (hrx r hr).symm, hry r hr, hxy.symm,
        hleft r hr, (hright r hr).symm, hbase.symm⟩
  let palette : Finset
      (secondOrderDefectGraph G).ConnectedComponent := Finset.univ.erase base
  have hpalette : palette.card = 3 := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ base), Finset.card_univ,
      hcount]
  have hmem : ∀ r ∈ R, left r = right r → left r ≠ base →
      left r ∈ palette := by
    intro r hr he hne
    exact Finset.mem_erase.mpr ⟨hne, Finset.mem_univ _⟩
  obtain ⟨owner, r₁, r₂, hob, hrne, hr₁, hr₂,
      hl₁, hr₁c, hl₂, hr₂c⟩ :=
    exists_two_repeated_same_nonbase_color_of_six_noRainbow
      R left right base palette hpalette hRcard
        hleftBudget hrightBudget hno' hmem
  refine ⟨owner, r₁, r₂, hob, hrne, hr₁, hr₂, ?_, ?_, ?_, ?_⟩
  · simpa [hl₁] using hleft r₁ hr₁
  · simpa [hr₁c] using hright r₁ hr₁
  · simpa [hl₂] using hleft r₂ hr₂
  · simpa [hr₂c] using hright r₂ hr₂

set_option maxHeartbeats 800000 in
/-- Canonical-owner specialization of the preceding theorem.  Only the
six-core's non-defect incidences, the four 2-factor degrees, and the
no-rainbow hypothesis remain as inputs. -/
theorem exists_repeatedOwnerFork_of_sixCore
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G)
    (d : (secondOrderDefectGraph G).ConnectedComponent)
    (x y : d.supp) (hxy : x ≠ y)
    (hnotxy : ¬ (secondOrderDefectGraph G).Adj x.1 y.1)
    (R : Finset d.supp) (hRcard : R.card = 6)
    (hrx : ∀ r ∈ R, r ≠ x) (hry : ∀ r ∈ R, r ≠ y)
    (hnotx : ∀ r ∈ R,
      ¬ (secondOrderDefectGraph G).Adj x.1 r.1)
    (hnoty : ∀ r ∈ R,
      ¬ (secondOrderDefectGraph G).Adj y.1 r.1)
    (hdeg : ∀ owner z,
      (restrictedComponentOwnerGraph G d owner).degree z = 2)
    (hcount : Fintype.card
      (secondOrderDefectGraph G).ConnectedComponent = 4)
    (hno : ∀ a b c,
      a ≠ b → a ≠ c → b ≠ c → ¬ routingOwnerRainbow G d a b c) :
    ∃ owner r₁ r₂,
      owner ≠ nondefectPairOwner G hfree
        (fun h => hxy (Subtype.ext h)) hnotxy ∧
      r₁ ≠ r₂ ∧ r₁ ∈ R ∧ r₂ ∈ R ∧
      (restrictedComponentOwnerGraph G d owner).Adj x r₁ ∧
      (restrictedComponentOwnerGraph G d owner).Adj y r₁ ∧
      (restrictedComponentOwnerGraph G d owner).Adj x r₂ ∧
      (restrictedComponentOwnerGraph G d owner).Adj y r₂ := by
  classical
  have hxyval : x.1 ≠ y.1 := fun h => hxy (Subtype.ext h)
  let base := nondefectPairOwner G hfree hxyval hnotxy
  let left : d.supp → (secondOrderDefectGraph G).ConnectedComponent :=
    fun r => if hr : r ∈ R then
      nondefectPairOwner G hfree (x := x.1) (y := r.1)
        (fun h => hrx r hr (Subtype.ext h.symm)) (hnotx r hr)
    else base
  let right : d.supp → (secondOrderDefectGraph G).ConnectedComponent :=
    fun r => if hr : r ∈ R then
      nondefectPairOwner G hfree (x := y.1) (y := r.1)
        (fun h => hry r hr (Subtype.ext h.symm)) (hnoty r hr)
    else base
  have hbase : (restrictedComponentOwnerGraph G d base).Adj x y := by
    change (componentOwnerGraph G (secondOrderDefectGraph G) base).Adj x.1 y.1
    exact nondefectPairOwner_adj G hfree hxyval hnotxy
  have hleftAdj : ∀ r ∈ R,
      (restrictedComponentOwnerGraph G d (left r)).Adj x r := by
    intro r hr
    change (componentOwnerGraph G (secondOrderDefectGraph G) (left r)).Adj x.1 r.1
    simp only [left, dif_pos hr]
    exact nondefectPairOwner_adj G hfree (x := x.1) (y := r.1)
      (fun h => hrx r hr (Subtype.ext h.symm)) (hnotx r hr)
  have hrightAdj : ∀ r ∈ R,
      (restrictedComponentOwnerGraph G d (right r)).Adj y r := by
    intro r hr
    change (componentOwnerGraph G (secondOrderDefectGraph G) (right r)).Adj y.1 r.1
    simp only [right, dif_pos hr]
    exact nondefectPairOwner_adj G hfree (x := y.1) (y := r.1)
      (fun h => hry r hr (Subtype.ext h.symm)) (hnoty r hr)
  simpa [base] using exists_repeatedOwnerFork_of_sixCore_noRainbow
    G d x y hxy R hRcard left right base hbase hleftAdj hrightAdj
      hrx hry hdeg hcount hno

/-- Order-sixty-four endpoint: every codegree-six nonedge in a defect
component forces a repeated non-base owner fork in the no-rainbow branch. -/
theorem orderSixtyFour_codegreeSix_forces_repeatedOwnerFork
    (G : SimpleGraph (Fin 64)) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 (Fin 64) G)
    (hreg : ∀ z, G.degree z = 8)
    (hcount : Fintype.card
      (secondOrderDefectGraph G).ConnectedComponent = 4)
    (d : (secondOrderDefectGraph G).ConnectedComponent)
    (x y : d.supp) (hxy : x ≠ y)
    (hnot : ¬ ((secondOrderDefectGraph G).induce d.supp).Adj x y)
    (hcode : ((((secondOrderDefectGraph G).induce d.supp).neighborFinset x) ∩
      (((secondOrderDefectGraph G).induce d.supp).neighborFinset y)).card = 6)
    (hno : ∀ a b c,
      a ≠ b → a ≠ c → b ≠ c → ¬ routingOwnerRainbow G d a b c) :
    let base := nondefectPairOwner G hfree
      (fun h => hxy (Subtype.ext h)) (by simpa using hnot)
    let R := ((((secondOrderDefectGraph G).induce d.supp)ᶜ.neighborFinset x) ∩
      (((secondOrderDefectGraph G).induce d.supp)ᶜ.neighborFinset y))
    ∃ owner r₁ r₂, owner ≠ base ∧ r₁ ≠ r₂ ∧ r₁ ∈ R ∧ r₂ ∈ R ∧
      (restrictedComponentOwnerGraph G d owner).Adj x r₁ ∧
      (restrictedComponentOwnerGraph G d owner).Adj y r₁ ∧
      (restrictedComponentOwnerGraph G d owner).Adj x r₂ ∧
      (restrictedComponentOwnerGraph G d owner).Adj y r₂ := by
  classical
  let H := (secondOrderDefectGraph G).induce d.supp
  let R := Hᶜ.neighborFinset x ∩ Hᶜ.neighborFinset y
  have hHreg : ∀ z, H.degree z = 7 := by
    intro z
    simpa [H] using binarySquare_regular_inducedDefectComponent_degree
      G hfree (q := 8) (by norm_num) hreg (by norm_num) d z
  have hRcard : R.card = 6 := by
    have hdcard :=
      orderSixtyFour_regular_four_defectComponents_all_orderSixteen
        G hfree hreg hcount d
    have hHcard : Fintype.card d.supp = 16 := by
      calc
        Fintype.card d.supp = d.supp.ncard := by
          simpa using (Set.ncard_eq_toFinset_card d.supp).symm
        _ = 16 := hdcard
    apply sevenRegular_compl_codegree_eq_six_of_codegree_eq_six
      H hHcard hHreg hxy hnot
    simpa [H] using hcode
  have hrx : ∀ r ∈ R, r ≠ x := by
    intro r hr heq
    subst r
    exact Hᶜ.loopless.irrefl x
      ((Hᶜ.mem_neighborFinset x x).mp (Finset.mem_inter.mp hr).1)
  have hry : ∀ r ∈ R, r ≠ y := by
    intro r hr heq
    subst r
    exact Hᶜ.loopless.irrefl y
      ((Hᶜ.mem_neighborFinset y y).mp (Finset.mem_inter.mp hr).2)
  have hnotx : ∀ r ∈ R,
      ¬ (secondOrderDefectGraph G).Adj x.1 r.1 := by
    intro r hr hD
    have hH : H.Adj x r := by simpa [H] using hD
    exact ((Hᶜ.mem_neighborFinset x r).mp (Finset.mem_inter.mp hr).1).2 hH
  have hnoty : ∀ r ∈ R,
      ¬ (secondOrderDefectGraph G).Adj y.1 r.1 := by
    intro r hr hD
    have hH : H.Adj y r := by simpa [H] using hD
    exact ((Hᶜ.mem_neighborFinset y r).mp (Finset.mem_inter.mp hr).2).2 hH
  have hall := orderSixtyFour_regular_four_defectComponents_all_orderSixteen
    G hfree hreg hcount
  have hdeg : ∀ owner z,
      (restrictedComponentOwnerGraph G d owner).degree z = 2 := by
    intro owner z
    exact binarySquare_regular_twoSizeTwoParts_restrictedOwner_degree_two
      G hfree (q := 8) (by norm_num) hreg (by norm_num) d owner
        (by simpa using hall d) (by simpa using hall owner) z
  simpa [H, R] using exists_repeatedOwnerFork_of_sixCore
    G hfree d x y hxy (by simpa [H] using hnot) R hRcard
      hrx hry hnotx hnoty hdeg hcount hno

end

end Erdos85
