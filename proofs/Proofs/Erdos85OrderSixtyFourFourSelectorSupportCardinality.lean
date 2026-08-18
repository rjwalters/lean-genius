import Proofs.Erdos85BinarySquareFourSelectorHyperCube

/-!
# Cardinality of the four-selector support at order 64

The CUBE-PLANE/4 law makes the four-coordinate support an index-four
orthogonal array: every fixed pair in two distinct coordinates has four
completions, and the full support has cardinality `1024`.
-/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- Finite form of the four-selector hypercube support. -/
def fourSelectorHyperCubeSupportFinset
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (c d e f : (secondOrderDefectGraph G).ConnectedComponent) :
    Finset (c.supp × (d.supp × (e.supp × f.supp))) := by
  classical
  exact Finset.univ.filter fun p => p ∈ fourSelectorHyperCubeSupport G c d e f

/-- A fixed two-coordinate fiber of the four-selector support. -/
def fourSelectorHyperCubeTwoFiberFinset
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (c d e f : (secondOrderDefectGraph G).ConnectedComponent)
    (a : c.supp) (b : d.supp) : Finset (e.supp × f.supp) := by
  classical
  exact Finset.univ.filter fun zw =>
    (a, (b, zw)) ∈ fourSelectorHyperCubeSupport G c d e f

/-- Every fixed `(c,d)` pair has exactly four completions in the `(e,f)`
plane. -/
theorem binarySquare_regular_fourSelectorHyperCubeSupport_twoFiber_card_four
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) {q : ℕ} (hq : 3 ≤ q)
    (hreg : ∀ x, G.degree x = q)
    (hcard : Fintype.card V = q * q)
    (c d e f : (secondOrderDefectGraph G).ConnectedComponent)
    (hcd : c ≠ d)
    (he : e.supp.ncard = q * 2) (hf : f.supp.ncard = q * 2)
    (a : c.supp) (b : d.supp) :
    (fourSelectorHyperCubeTwoFiberFinset G c d e f a b).card = 4 := by
  classical
  obtain ⟨u₀, u₁, hu, v₀, v₁, hv, hrect⟩ :=
    binarySquare_regular_fourSelectorHyperCubeSupport_twoFiber_exact_rectangle
      G hfree hq hreg hcard c d e f hcd he hf a b
  have heq : fourSelectorHyperCubeTwoFiberFinset G c d e f a b =
      ({u₀, u₁} : Finset e.supp) ×ˢ ({v₀, v₁} : Finset f.supp) := by
    ext zw
    simp [fourSelectorHyperCubeTwoFiberFinset, hrect zw.1 zw.2]
  rw [heq, Finset.card_product]
  simp [hu, hv]

/-- At order 64, four size-16 component coordinates have a four-selector
support of cardinality `1024 = 16²·4 = 64·2⁴`. -/
theorem orderSixtyFour_fourSizeSixteen_selectorHyperCubeSupport_card
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G)
    (hreg : ∀ x, G.degree x = 8)
    (hcard : Fintype.card V = 64)
    (c d e f : (secondOrderDefectGraph G).ConnectedComponent)
    (hcd : c ≠ d)
    (hc : c.supp.ncard = 16) (hd : d.supp.ncard = 16)
    (he : e.supp.ncard = 16) (hf : f.supp.ncard = 16) :
    (fourSelectorHyperCubeSupportFinset G c d e f).card = 1024 := by
  classical
  have hplaneCard : ∀ a : c.supp, ∀ b : d.supp,
      (fourSelectorHyperCubeTwoFiberFinset G c d e f a b).card = 4 := by
    intro a b
    exact binarySquare_regular_fourSelectorHyperCubeSupport_twoFiber_card_four
      G hfree (q := 8) (by omega) hreg (by simpa using hcard)
        c d e f hcd (by simpa using he) (by simpa using hf) a b
  have hplaneSum : ∀ a : c.supp, ∀ b : d.supp,
      (∑ z : e.supp, ∑ w : f.supp,
        if (a, (b, (z, w))) ∈ fourSelectorHyperCubeSupport G c d e f
          then 1 else 0) = 4 := by
    intro a b
    have hab := hplaneCard a b
    simp only [fourSelectorHyperCubeTwoFiberFinset] at hab
    rw [Finset.card_eq_sum_ones, Finset.sum_filter] at hab
    simp only [Fintype.sum_prod_type] at hab
    exact hab
  have hcs : Fintype.card c.supp = 16 := by
    rw [Set.fintypeCard_eq_ncard]; exact hc
  have hds : Fintype.card d.supp = 16 := by
    rw [Set.fintypeCard_eq_ncard]; exact hd
  simp only [fourSelectorHyperCubeSupportFinset]
  rw [Finset.card_eq_sum_ones, Finset.sum_filter]
  simp only [Fintype.sum_prod_type]
  simp_rw [hplaneSum]
  simp [hcs, hds]

end

end Erdos85
