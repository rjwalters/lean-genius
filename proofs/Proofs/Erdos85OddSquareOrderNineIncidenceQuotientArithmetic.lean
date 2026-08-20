import Proofs.Erdos85OddSquareOrderNineIncidenceQuotientSystem

/-! # Arithmetic exclusions from the q = 9 quotient system

Node: B.3 / GAP B-CLASSIFY.  These are graph-independent integer terminals
for scalar incidence profiles that cannot support the symmetric five-bin
defect quotient equations.
-/

open Finset

namespace Erdos85

noncomputable section

/-- The scalar h=11 profile `(26,0,55,0,0)` is incompatible with the
symmetric quotient equations.  Its low-bin sizes are `(15,0,55,0,0)`.
The empty odd bins force all their cross-edge counts to vanish, while the
bin-zero weighted row would require twice an integer to equal 165. -/
theorem squareOrderNine_no_hEleven_26_0_55_0_0_quotient
    (b : ℕ → ℕ) (e : ℕ → ℕ → ℕ)
    (hb0 : b 0 = 15) (hb1 : b 1 = 0)
    (hb3 : b 3 = 0) (_hb4 : b 4 = 0)
    (hsymm : ∀ i j, e i j = e j i)
    (hrow : ∀ i,
      (∑ j ∈ Finset.range 5, e i j) =
          (8 - i) * b i ∧
        (∑ j ∈ Finset.range 5, j * e i j) =
          (11 - i) * b i) : False := by
  have h0 := (hrow 0).2
  have h1 := (hrow 1).1
  have h3 := (hrow 3).1
  have h4 := (hrow 4).1
  rw [hb0] at h0
  rw [hb1] at h1
  rw [hb3] at h3
  rw [_hb4] at h4
  norm_num [Finset.sum_range_succ] at h0 h1 h3 h4
  rw [hsymm 0 1] at h0
  rw [hsymm 0 3] at h0
  rw [hsymm 0 4] at h0
  omega

/-- A nonzero incidence bin contains no high vertices, so its low-bin card is
the corresponding full histogram card. -/
theorem squareOrderNine_lowIncidenceBin_card_eq_histogram_of_ne_zero
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hp : SquareOrderNonregularSectorProfile G 9)
    {i : ℕ} (hi : i ≠ 0) :
    (squareOrderNineLowIncidenceBin G i).card =
      squareOrderNineHighIncidenceHistogram G i := by
  classical
  let H := squareOrderHighVertices G 9
  let k := squareOrderHighIncidenceCount G 9
  have hkzero {x : V} (hx : x ∈ H) : k x = 0 := by
    have hinter : G.neighborFinset x ∩ H = ∅ := by
      ext y
      constructor
      · intro hy
        have hy' := Finset.mem_inter.mp hy
        have hadj : G.Adj x y := (G.mem_neighborFinset x y).mp hy'.1
        exact (hp.high_independent hx hy'.2 hadj).elim
      · simp
    simp [k, squareOrderHighIncidenceCount, H, hinter]
  congr 1
  ext x
  simp only [squareOrderNineLowIncidenceBin,
    Finset.mem_filter, Finset.mem_sdiff, Finset.mem_univ, true_and]
  constructor
  · exact fun hx => hx.2
  · intro hki
    refine ⟨?_, hki⟩
    intro hxH
    have := hkzero hxH
    exact hi (hki.symm.trans this)

/-- The zero low-bin card is the full zero-bin histogram card minus the high
sector, since every high vertex has incidence zero. -/
theorem squareOrderNine_lowIncidenceBin_zero_card_add_high_card
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hp : SquareOrderNonregularSectorProfile G 9) :
    (squareOrderNineLowIncidenceBin G 0).card +
        (squareOrderHighVertices G 9).card =
      squareOrderNineHighIncidenceHistogram G 0 := by
  classical
  let H := squareOrderHighVertices G 9
  let k := squareOrderHighIncidenceCount G 9
  let Z := (Finset.univ : Finset V).filter fun x => k x = 0
  have hkzero {x : V} (hx : x ∈ H) : k x = 0 := by
    have hinter : G.neighborFinset x ∩ H = ∅ := by
      ext y
      constructor
      · intro hy
        have hy' := Finset.mem_inter.mp hy
        have hadj : G.Adj x y := (G.mem_neighborFinset x y).mp hy'.1
        exact (hp.high_independent hx hy'.2 hadj).elim
      · simp
    simp [k, squareOrderHighIncidenceCount, H, hinter]
  have hsub : H ⊆ Z := by
    intro x hx
    exact Finset.mem_filter.mpr ⟨by simp, hkzero hx⟩
  have hbin : squareOrderNineLowIncidenceBin G 0 = Z \ H := by
    ext x
    simp [squareOrderNineLowIncidenceBin, Z, k, H, and_comm]
  rw [hbin]
  change #(Z \ H) + #H = #Z
  rw [Finset.card_sdiff_of_subset hsub]
  have hle := Finset.card_le_card hsub
  rw [Nat.sub_add_cancel hle]

/-- The h=11 scalar histogram `(26,0,55,0,0)` cannot occur in a q=9
nonregular square-order core. -/
theorem squareOrderNine_not_highIncidence_profile_26_0_55_0_0_of_eleven_high
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G)
    (hmin : ∀ z : V, 9 ≤ G.degree z)
    (hcover : ∀ {u v}, G.Adj u v → G.degree u = 9 ∨ G.degree v = 9)
    (hcard : Fintype.card V = 81)
    (hp : SquareOrderNonregularSectorProfile G 9)
    (hhigh : (squareOrderHighVertices G 9).card = 11)
    (hc0 : squareOrderNineHighIncidenceHistogram G 0 = 26)
    (hc1 : squareOrderNineHighIncidenceHistogram G 1 = 0)
    (_hc2 : squareOrderNineHighIncidenceHistogram G 2 = 55)
    (hc3 : squareOrderNineHighIncidenceHistogram G 3 = 0)
    (hc4 : squareOrderNineHighIncidenceHistogram G 4 = 0) : False := by
  let b := fun i => (squareOrderNineLowIncidenceBin G i).card
  let e := squareOrderNineDefectBinEdgeCount G
  have hbzero := squareOrderNine_lowIncidenceBin_zero_card_add_high_card G hp
  have hb0 : b 0 = 15 := by
    dsimp [b]
    rw [hhigh, hc0] at hbzero
    omega
  have hb1 : b 1 = 0 := by
    dsimp [b]
    rw [squareOrderNine_lowIncidenceBin_card_eq_histogram_of_ne_zero G hp (by omega), hc1]
  have hb3 : b 3 = 0 := by
    dsimp [b]
    rw [squareOrderNine_lowIncidenceBin_card_eq_histogram_of_ne_zero G hp (by omega), hc3]
  have hb4 : b 4 = 0 := by
    dsimp [b]
    rw [squareOrderNine_lowIncidenceBin_card_eq_histogram_of_ne_zero G hp (by omega), hc4]
  have hrow (i : ℕ) := squareOrderNine_lowIncidenceBin_finite_quotient_system
    G hfree hmin hcover hcard hp i
  dsimp only at hrow
  have hrow' : ∀ i,
      (∑ j ∈ Finset.range 5, e i j) = (8 - i) * b i ∧
        (∑ j ∈ Finset.range 5, j * e i j) = (11 - i) * b i := by
    intro i
    simpa [e, b, hhigh] using hrow i
  exact squareOrderNine_no_hEleven_26_0_55_0_0_quotient
    b e hb0 hb1 hb3 hb4
    (fun i j => squareOrderNineDefectBinEdgeCount_comm G i j) hrow'

end

end Erdos85

#print axioms Erdos85.squareOrderNine_no_hEleven_26_0_55_0_0_quotient
#print axioms Erdos85.squareOrderNine_not_highIncidence_profile_26_0_55_0_0_of_eleven_high
