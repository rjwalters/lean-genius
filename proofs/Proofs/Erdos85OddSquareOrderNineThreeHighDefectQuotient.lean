import Proofs.Erdos85OddSquareOrderNineSmallHighIncidenceCensus
import Proofs.Erdos85OddSquareOrderNineIncidenceQuotientArithmetic
import Proofs.Erdos85SquareOrderTwoHighTerminal

/-! # Exact defect quotients for the q = 9 three-high profiles

Node: B.3 / GAP B-CLASSIFY.  Symmetry, the two quotient rows, and internal
edge parity determine the complete inter-bin defect edge census for both
scalar profiles surviving at `h = 3`.
-/

open Finset SimpleGraph

namespace Erdos85

noncomputable section

/-- Internal directed edge mass of every defect-incidence bin is even. -/
theorem even_squareOrderNineDefectBinEdgeCount_self
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (i : ℕ) :
    Even (squareOrderNineDefectBinEdgeCount G i i) := by
  classical
  let D := secondOrderDefectGraph G
  let B := squareOrderNineLowIncidenceBin G i
  let K := D.induce (↑B : Set V)
  have hsum : squareOrderNineDefectBinEdgeCount G i i =
      ∑ x : ↥(↑B : Set V), K.degree x := by
    simp only [squareOrderNineDefectBinEdgeCount]
    change (∑ x ∈ B, (D.neighborFinset x ∩ B).card) = _
    rw [← Finset.sum_attach]
    apply Finset.sum_congr rfl
    intro x _hx
    exact (degree_induce_finset_eq_card_inter D B x).symm
  rw [hsum, K.sum_degrees_eq_twice_card_edges]
  exact ⟨K.edgeFinset.card, by omega⟩

/-- Arithmetic terminal for the first h=3 low-bin profile `(51,24,3,0,0)`.
The symmetric quotient is uniquely determined. -/
theorem squareOrderNine_hThree_51_24_3_0_0_quotient_unique
    (b : ℕ → ℕ) (e : ℕ → ℕ → ℕ)
    (hb0 : b 0 = 51) (hb1 : b 1 = 24) (hb2 : b 2 = 3)
    (hb3 : b 3 = 0) (hb4 : b 4 = 0)
    (hsymm : ∀ i j, e i j = e j i)
    (heven22 : Even (e 2 2))
    (hrow : ∀ i,
      (∑ j ∈ Finset.range 5, e i j) = (8 - i) * b i ∧
        (∑ j ∈ Finset.range 5, j * e i j) = (3 - i) * b i) :
    e 0 0 = 270 ∧ e 0 1 = 123 ∧ e 0 2 = 15 ∧
      e 1 1 = 42 ∧ e 1 2 = 3 ∧ e 2 2 = 0 := by
  obtain ⟨t, ht⟩ := heven22
  have h0a := (hrow 0).1
  have h0b := (hrow 0).2
  have h1a := (hrow 1).1
  have h1b := (hrow 1).2
  have h2a := (hrow 2).1
  have h2b := (hrow 2).2
  have h3a := (hrow 3).1
  have h4a := (hrow 4).1
  rw [hb0] at h0a h0b
  rw [hb1] at h1a h1b
  rw [hb2] at h2a h2b
  rw [hb3] at h3a
  rw [hb4] at h4a
  norm_num [Finset.sum_range_succ] at h0a h0b h1a h1b h2a h2b h3a h4a
  have hs01 := hsymm 0 1
  have hs02 := hsymm 0 2
  have hs03 := hsymm 0 3
  have hs04 := hsymm 0 4
  have hs12 := hsymm 1 2
  have hs13 := hsymm 1 3
  have hs14 := hsymm 1 4
  have hs23 := hsymm 2 3
  have hs24 := hsymm 2 4
  omega

/-- Arithmetic terminal for the second h=3 low-bin profile `(50,27,0,1,0)`.
Its supported symmetric quotient is also uniquely determined. -/
theorem squareOrderNine_hThree_50_27_0_1_0_quotient_unique
    (b : ℕ → ℕ) (e : ℕ → ℕ → ℕ)
    (hb0 : b 0 = 50) (hb1 : b 1 = 27) (hb2 : b 2 = 0)
    (hb3 : b 3 = 1) (hb4 : b 4 = 0)
    (hsymm : ∀ i j, e i j = e j i)
    (hrow : ∀ i,
      (∑ j ∈ Finset.range 5, e i j) = (8 - i) * b i ∧
        (∑ j ∈ Finset.range 5, j * e i j) = (3 - i) * b i) :
    e 0 0 = 260 ∧ e 0 1 = 135 ∧ e 0 3 = 5 ∧
      e 1 1 = 54 ∧ e 1 3 = 0 ∧ e 3 3 = 0 := by
  have h0a := (hrow 0).1
  have h0b := (hrow 0).2
  have h1a := (hrow 1).1
  have h1b := (hrow 1).2
  have h2a := (hrow 2).1
  have h3a := (hrow 3).1
  have h3b := (hrow 3).2
  have h4a := (hrow 4).1
  rw [hb0] at h0a h0b
  rw [hb1] at h1a h1b
  rw [hb2] at h2a
  rw [hb3] at h3a h3b
  rw [hb4] at h4a
  norm_num [Finset.sum_range_succ] at h0a h0b h1a h1b h2a h3a h3b h4a
  have hs01 := hsymm 0 1
  have hs02 := hsymm 0 2
  have hs03 := hsymm 0 3
  have hs04 := hsymm 0 4
  have hs12 := hsymm 1 2
  have hs13 := hsymm 1 3
  have hs14 := hsymm 1 4
  have hs23 := hsymm 2 3
  have hs24 := hsymm 2 4
  have hs34 := hsymm 3 4
  omega

/-- Graph-level three-high quotient census: the two scalar histograms lift to
two exact symmetric defect edge-count systems. -/
theorem squareOrderNine_threeHigh_defectQuotient_census
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G)
    (hmin : ∀ z : V, 9 ≤ G.degree z)
    (hcover : ∀ {u v}, G.Adj u v → G.degree u = 9 ∨ G.degree v = 9)
    (hcard : Fintype.card V = 81)
    (hp : SquareOrderNonregularSectorProfile G 9)
    (hhigh : (squareOrderHighVertices G 9).card = 3) :
    let e := squareOrderNineDefectBinEdgeCount G
    (e 0 0 = 270 ∧ e 0 1 = 123 ∧ e 0 2 = 15 ∧
      e 1 1 = 42 ∧ e 1 2 = 3 ∧ e 2 2 = 0) ∨
    (e 0 0 = 260 ∧ e 0 1 = 135 ∧ e 0 3 = 5 ∧
      e 1 1 = 54 ∧ e 1 3 = 0 ∧ e 3 3 = 0) := by
  dsimp only
  let c := squareOrderNineHighIncidenceHistogram G
  let b := fun i => (squareOrderNineLowIncidenceBin G i).card
  let e := squareOrderNineDefectBinEdgeCount G
  have hzero := squareOrderNine_lowIncidenceBin_zero_card_add_high_card G hp
  have hrow (i : ℕ) := squareOrderNine_lowIncidenceBin_finite_quotient_system
    G hfree hmin hcover hcard hp i
  dsimp only at hrow
  have hrow' : ∀ i,
      (∑ j ∈ Finset.range 5, e i j) = (8 - i) * b i ∧
        (∑ j ∈ Finset.range 5, j * e i j) = (3 - i) * b i := by
    intro i
    simpa [e, b, hhigh] using hrow i
  rcases squareOrderNine_highIncidence_profile_of_three_high
      G hcard hp hhigh with hpA | hpB
  · left
    have hb0 : b 0 = 51 := by
      dsimp [b]
      rw [hhigh, hpA.1] at hzero
      omega
    have hb1 : b 1 = 24 := by
      dsimp [b]
      simpa [c] using
        (squareOrderNine_lowIncidenceBin_card_eq_histogram_of_ne_zero
          G hp (i := 1) (by omega)).trans hpA.2.1
    have hb2 : b 2 = 3 := by
      dsimp [b]
      simpa [c] using
        (squareOrderNine_lowIncidenceBin_card_eq_histogram_of_ne_zero
          G hp (i := 2) (by omega)).trans hpA.2.2.1
    have hb3 : b 3 = 0 := by
      dsimp [b]
      simpa [c] using
        (squareOrderNine_lowIncidenceBin_card_eq_histogram_of_ne_zero
          G hp (i := 3) (by omega)).trans hpA.2.2.2.1
    have hb4 : b 4 = 0 := by
      dsimp [b]
      simpa [c] using
        (squareOrderNine_lowIncidenceBin_card_eq_histogram_of_ne_zero
          G hp (i := 4) (by omega)).trans hpA.2.2.2.2
    exact squareOrderNine_hThree_51_24_3_0_0_quotient_unique
      b e hb0 hb1 hb2 hb3 hb4
      (fun i j => squareOrderNineDefectBinEdgeCount_comm G i j)
      (even_squareOrderNineDefectBinEdgeCount_self G 2) hrow'
  · right
    have hb0 : b 0 = 50 := by
      dsimp [b]
      rw [hhigh, hpB.1] at hzero
      omega
    have hb1 : b 1 = 27 := by
      dsimp [b]
      simpa [c] using
        (squareOrderNine_lowIncidenceBin_card_eq_histogram_of_ne_zero
          G hp (i := 1) (by omega)).trans hpB.2.1
    have hb2 : b 2 = 0 := by
      dsimp [b]
      simpa [c] using
        (squareOrderNine_lowIncidenceBin_card_eq_histogram_of_ne_zero
          G hp (i := 2) (by omega)).trans hpB.2.2.1
    have hb3 : b 3 = 1 := by
      dsimp [b]
      simpa [c] using
        (squareOrderNine_lowIncidenceBin_card_eq_histogram_of_ne_zero
          G hp (i := 3) (by omega)).trans hpB.2.2.2.1
    have hb4 : b 4 = 0 := by
      dsimp [b]
      simpa [c] using
        (squareOrderNine_lowIncidenceBin_card_eq_histogram_of_ne_zero
          G hp (i := 4) (by omega)).trans hpB.2.2.2.2
    exact squareOrderNine_hThree_50_27_0_1_0_quotient_unique
      b e hb0 hb1 hb2 hb3 hb4
      (fun i j => squareOrderNineDefectBinEdgeCount_comm G i j) hrow'

end


end Erdos85

#print axioms Erdos85.even_squareOrderNineDefectBinEdgeCount_self
#print axioms Erdos85.squareOrderNine_hThree_51_24_3_0_0_quotient_unique
#print axioms Erdos85.squareOrderNine_hThree_50_27_0_1_0_quotient_unique
#print axioms Erdos85.squareOrderNine_threeHigh_defectQuotient_census
