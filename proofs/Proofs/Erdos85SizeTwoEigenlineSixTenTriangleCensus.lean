import Proofs.Erdos85SizeTwoEigenlineSixTenAntipodalTriangle

/-!
# Antipodal-triangle census in the q=8 six-plus-ten stratum

Node: `SIZE-TWO-EIGENLINE(8)` beneath outline F.3.

The long shore has ten vertices, and the signed diagonal ledger gives exactly
two same-sign defect neighbors at each one.  Consequently it has twenty
directed same-sign diagonal defect edges.  Together with the three-triangle
local theorem, this is the finite base count for the antipodal cube moment.
-/

open Finset SimpleGraph

namespace Erdos85

noncomputable section

/-- The ten-cycle has exactly twenty directed same-sign diagonal defect
edges, represented as a sigma finset over its vertices. -/
theorem binarySquare_regular_sizeTwoPart_eight_sixTen_sameSignDiagonalPairs_card
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G)
    (hreg : ∀ x, G.degree x = 8)
    (hcard : Fintype.card V = 8 * 8)
    (c : (secondOrderDefectGraph G).ConnectedComponent)
    [DecidableEq (G.induce c.supp).ConnectedComponent]
    (hc : c.supp.ncard = 8 * 2)
    (s : V → ℤ)
    (hs_in : ∀ x ∈ c.supp, s x = -1 ∨ s x = 1)
    (hs_out : ∀ x ∉ c.supp, s x = 0)
    (hA_in : ∀ x ∈ c.supp,
      ∑ y ∈ G.neighborFinset x, s y = -2 * s x)
    (hDs : ∀ x, ∑ y ∈ (secondOrderDefectGraph G).neighborFinset x, s y =
      3 * s x)
    (a b : (G.induce c.supp).ConnectedComponent)
    (ha : a.supp.ncard = 6) (hb : b.supp.ncard = 10) :
    let H := G.induce c.supp
    let K := (secondOrderDefectGraph G).induce c.supp
    let B := (Finset.univ : Finset c.supp).filter fun y => y ∈ b.supp
    let E := B.sigma fun y =>
      (componentNeighborFinset K H b y).filter fun z => s z.1 = s y.1
    E.card = 20 := by
  classical
  dsimp only
  rw [Finset.card_sigma]
  have hrow : ∀ y : c.supp, y ∈ b.supp →
      (((componentNeighborFinset
          ((secondOrderDefectGraph G).induce c.supp) (G.induce c.supp) b y).filter
        fun z => s z.1 = s y.1).card = 2) := by
    intro y hy
    exact (binarySquare_regular_sizeTwoPart_eight_sixTen_longDiagonal_signSplit
      G hfree hreg hcard c hc s hs_in hs_out hA_in hDs a b ha hb y hy).1
  have hBcard : ((Finset.univ : Finset c.supp).filter
      fun y => y ∈ b.supp).card = 10 := by
    rw [show ((Finset.univ : Finset c.supp).filter fun y => y ∈ b.supp).card =
        b.supp.ncard by
      have heq : ((Finset.univ : Finset c.supp).filter fun y => y ∈ b.supp) =
          b.supp.toFinite.toFinset := by
        ext y
        simp
      rw [heq, Set.ncard_eq_toFinset_card]]
    exact hb
  calc
    (∑ y with y ∈ b.supp,
        ((componentNeighborFinset
          ((secondOrderDefectGraph G).induce c.supp) (G.induce c.supp) b y).filter
            fun z => s z.1 = s y.1).card) =
        ∑ y with y ∈ b.supp, 2 := by
      apply Finset.sum_congr rfl
      intro y hy
      exact hrow y (Finset.mem_filter.mp hy).2
    _ = 20 := by
      rw [Finset.sum_const]
      change ((Finset.univ.filter fun y : c.supp => y ∈ b.supp).card) * 2 = 20
      omega

/-- Summing the three common antipodal six-cycle neighbors over the twenty
directed same-sign diagonal bases gives sixty certified rooted antipodal
triangle triples. -/
theorem binarySquare_regular_sizeTwoPart_eight_sixTen_rootedAntipodalTriangles_card
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G)
    (hreg : ∀ x, G.degree x = 8)
    (hcard : Fintype.card V = 8 * 8)
    (c : (secondOrderDefectGraph G).ConnectedComponent)
    [DecidableEq (G.induce c.supp).ConnectedComponent]
    (hc : c.supp.ncard = 8 * 2)
    (s : V → ℤ)
    (hs_in : ∀ x ∈ c.supp, s x = -1 ∨ s x = 1)
    (hs_out : ∀ x ∉ c.supp, s x = 0)
    (hA_in : ∀ x ∈ c.supp,
      ∑ y ∈ G.neighborFinset x, s y = -2 * s x)
    (hDs : ∀ x, ∑ y ∈ (secondOrderDefectGraph G).neighborFinset x, s y =
      3 * s x)
    (a b : (G.induce c.supp).ConnectedComponent)
    (ha : a.supp.ncard = 6) (hb : b.supp.ncard = 10)
    (u : ZMod 6 → c.supp) (v : ZMod 10 → c.supp)
    (huinj : Function.Injective u) (hvinj : Function.Injective v)
    (hurange : Set.range u = a.supp) (hvrange : Set.range v = b.supp)
    (hu : ∀ z, (G.induce c.supp).neighborFinset (u z) =
      {u (z - 1), u (z + 1)})
    (hv : ∀ z, (G.induce c.supp).neighborFinset (v z) =
      {v (z - 1), v (z + 1)}) :
    let H := G.induce c.supp
    let K := (secondOrderDefectGraph G).induce c.supp
    let B := (Finset.univ : Finset c.supp).filter fun y => y ∈ b.supp
    let E := B.sigma fun y =>
      (componentNeighborFinset K H b y).filter fun z => s z.1 = s y.1
    let T := E.sigma fun p =>
      (componentNeighborFinset K H a p.1).filter fun x =>
        (antipodalGraph G).Adj x.1 p.1.1 ∧
          (antipodalGraph G).Adj x.1 p.2.1
    T.card = 60 := by
  classical
  dsimp only
  rw [Finset.card_sigma]
  have hEcard :=
    binarySquare_regular_sizeTwoPart_eight_sixTen_sameSignDiagonalPairs_card
      G hfree hreg hcard c hc s hs_in hs_out hA_in hDs a b ha hb
  dsimp only at hEcard
  have hrow : ∀ p ∈
      (((Finset.univ : Finset c.supp).filter fun y => y ∈ b.supp).sigma fun y =>
        (componentNeighborFinset
          ((secondOrderDefectGraph G).induce c.supp) (G.induce c.supp) b y).filter
            fun z => s z.1 = s y.1),
      (((componentNeighborFinset
          ((secondOrderDefectGraph G).induce c.supp) (G.induce c.supp) a p.1).filter
        fun x => (antipodalGraph G).Adj x.1 p.1.1 ∧
          (antipodalGraph G).Adj x.1 p.2.1).card = 3) := by
    rintro ⟨y, z⟩ hp
    have hp' := Finset.mem_sigma.mp hp
    have hp1 : y ∈ b.supp := (Finset.mem_filter.mp hp'.1).2
    have hp2 := Finset.mem_filter.mp hp'.2
    have hp2b : z ∈ b.supp :=
      (ConnectedComponent.mem_supp_iff b z).mpr
        (Finset.mem_filter.mp hp2.1).2
    have hpK : ((secondOrderDefectGraph G).induce c.supp).Adj y z :=
      (((secondOrderDefectGraph G).induce c.supp).mem_neighborFinset y z).mp
        (Finset.mem_filter.mp hp2.1).1
    have hprange1 : y ∈ Set.range v := by
      rw [hvrange]
      exact hp1
    have hprange2 : z ∈ Set.range v := by
      rw [hvrange]
      exact hp2b
    obtain ⟨i, hi⟩ := hprange1
    obtain ⟨j, hj⟩ := hprange2
    subst y
    subst z
    exact (binarySquare_regular_sizeTwoPart_eight_sixTen_sameSignDiagonal_three_antipodalTriangles
      G hfree hreg hcard c hc s hs_in hs_out hA_in hDs a b ha hb
        u v huinj hvinj hurange hvrange hu hv i j hpK hp2.2).2
  calc
    (∑ p ∈ (((Finset.univ : Finset c.supp).filter fun y => y ∈ b.supp).sigma fun y =>
        (componentNeighborFinset
          ((secondOrderDefectGraph G).induce c.supp) (G.induce c.supp) b y).filter
            fun z => s z.1 = s y.1),
      ((componentNeighborFinset
        ((secondOrderDefectGraph G).induce c.supp) (G.induce c.supp) a p.1).filter
          fun x => (antipodalGraph G).Adj x.1 p.1.1 ∧
            (antipodalGraph G).Adj x.1 p.2.1).card) =
        ∑ _p ∈ (((Finset.univ : Finset c.supp).filter fun y => y ∈ b.supp).sigma fun y =>
          (componentNeighborFinset
            ((secondOrderDefectGraph G).induce c.supp) (G.induce c.supp) b y).filter
              fun z => s z.1 = s y.1), 3 := by
      apply Finset.sum_congr rfl
      intro p hp
      exact hrow p hp
    _ = 60 := by
      rw [Finset.sum_const]
      rw [hEcard]
      norm_num

end

end Erdos85

#print axioms Erdos85.binarySquare_regular_sizeTwoPart_eight_sixTen_sameSignDiagonalPairs_card
#print axioms Erdos85.binarySquare_regular_sizeTwoPart_eight_sixTen_rootedAntipodalTriangles_card
