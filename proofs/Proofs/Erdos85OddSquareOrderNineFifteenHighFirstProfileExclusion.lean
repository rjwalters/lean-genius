import Proofs.Erdos85OddSquareOrderNineFifteenHighIncidenceCensus
import Proofs.Erdos85OddSquareOrderNineIncidenceQuotient

/-! # Excluding the first fifteen-high q=9 incidence profile

Node: B.3 / GAP B-CLASSIFY.  The scalar profile `(16,0,45,20,0)` is
incompatible with the defect-neighbor quotient equation at incidence zero.
-/

open Finset SimpleGraph

namespace Erdos85

noncomputable section

/-- If there are at most fifteen high vertices, there cannot be exactly one
low zero-incidence vertex and no one-incidence vertices.  The unique low
zero-incidence vertex would have eight defect neighbors, each of incidence at
least two, while its exact weighted-neighbor sum is the number of high
vertices. -/
theorem squareOrderNine_not_unique_low_zero_no_one_incidence
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G)
    (hmin : ∀ z : V, 9 ≤ G.degree z)
    (hcover : ∀ {u v}, G.Adj u v → G.degree u = 9 ∨ G.degree v = 9)
    (hcard : Fintype.card V = 81)
    (hp : SquareOrderNonregularSectorProfile G 9)
    (hhighle : (squareOrderHighVertices G 9).card ≤ 15) :
    let c := squareOrderNineHighIncidenceHistogram G
    ¬ (c 0 = (squareOrderHighVertices G 9).card + 1 ∧ c 1 = 0) := by
  classical
  dsimp only
  intro hprofile
  let H := squareOrderHighVertices G 9
  let D := secondOrderDefectGraph G
  let k := squareOrderHighIncidenceCount G 9
  let B := squareOrderNineLowIncidenceBin G 0
  let Z := (Finset.univ : Finset V).filter fun x => k x = 0
  change H.card ≤ 15 at hhighle
  have hHsubsetZ : H ⊆ Z := by
    intro x hx
    have hinter : G.neighborFinset x ∩ H = ∅ := by
      ext y
      constructor
      · intro hy
        have hy' := Finset.mem_inter.mp hy
        exact (hp.high_independent hx hy'.2
          ((G.mem_neighborFinset x y).mp hy'.1)).elim
      · intro hy
        simp at hy
    have hkx : k x = 0 := by
      simp [k, squareOrderHighIncidenceCount, H, hinter]
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ x, hkx⟩
  have hB : B = Z \ H := by
    ext x
    simp only [B, Z, squareOrderNineLowIncidenceBin, Finset.mem_filter,
      Finset.mem_sdiff, Finset.mem_univ, true_and]
    tauto
  have hZcard : Z.card = H.card + 1 := by
    simpa [Z, k, squareOrderNineHighIncidenceHistogram, boundedHistogram]
      using hprofile.1
  have hBcard : B.card = 1 := by
    rw [hB, Finset.card_sdiff, Finset.inter_eq_left.mpr hHsubsetZ, hZcard]
    omega
  have hledger := squareOrderNine_lowIncidenceBin_quotient_ledger
    G hfree hmin hcover hcard 0
  dsimp only at hledger
  change (∑ x ∈ B, D.degree x) = 8 * B.card ∧
    (∑ x ∈ B, ∑ y ∈ D.neighborFinset x, k y) = H.card * B.card at hledger
  rw [hBcard] at hledger
  obtain ⟨x, hBsingleton⟩ := Finset.card_eq_one.mp hBcard
  rw [hBsingleton] at hledger
  simp only [Finset.sum_singleton, Nat.mul_one] at hledger
  have hxdegree : D.degree x = 8 := hledger.1
  have hxweight : (∑ y ∈ D.neighborFinset x, k y) = H.card := hledger.2
  have hneighborLower {y : V} (hy : y ∈ D.neighborFinset x) : 2 ≤ k y := by
    have hadj : D.Adj x y := (D.mem_neighborFinset x y).mp hy
    have hyNotHigh : y ∉ H := by
      intro hyH
      have hydeg : D.degree y = 0 :=
        (squareOrder_degree_succ_highRoot_structure G hfree (by norm_num)
          hmin hcard (Finset.mem_filter.mp hyH).2).1
      have hxmem : x ∈ D.neighborFinset y :=
        (D.mem_neighborFinset y x).mpr hadj.symm
      have hempty : D.neighborFinset y = ∅ := by
        apply Finset.card_eq_zero.mp
        simpa [D.card_neighborFinset_eq_degree] using hydeg
      rw [hempty] at hxmem
      simp at hxmem
    have hkNotZero : k y ≠ 0 := by
      intro hky
      have hyB : y ∈ B := by
        exact Finset.mem_filter.mpr ⟨Finset.mem_sdiff.mpr ⟨Finset.mem_univ y, hyNotHigh⟩, hky⟩
      rw [hBsingleton] at hyB
      have hyx : y = x := by simpa using hyB
      subst y
      exact D.loopless.irrefl x hadj
    have hkNotOne : k y ≠ 1 := by
      intro hky
      have hyC : y ∈ (Finset.univ.filter fun z : V => k z = 1) :=
        Finset.mem_filter.mpr ⟨Finset.mem_univ y, hky⟩
      have hc1zero : ((Finset.univ.filter fun z : V => k z = 1)).card = 0 := by
        simpa [k, squareOrderNineHighIncidenceHistogram, boundedHistogram]
          using hprofile.2
      rw [Finset.card_eq_zero.mp hc1zero] at hyC
      simp at hyC
    omega
  have hlower : 2 * D.degree x ≤ ∑ y ∈ D.neighborFinset x, k y := by
    rw [← D.card_neighborFinset_eq_degree]
    calc
      2 * (D.neighborFinset x).card = ∑ y ∈ D.neighborFinset x, 2 := by
        simp [Nat.mul_comm]
      _ ≤ ∑ y ∈ D.neighborFinset x, k y := by
        exact Finset.sum_le_sum fun y hy => hneighborLower hy
  omega

/-- At fifteen high vertices, the first scalar endpoint profile is excluded
by the generic unique-zero-bin obstruction. -/
theorem squareOrderNine_not_first_fifteenHigh_incidence_profile
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G)
    (hmin : ∀ z : V, 9 ≤ G.degree z)
    (hcover : ∀ {u v}, G.Adj u v → G.degree u = 9 ∨ G.degree v = 9)
    (hcard : Fintype.card V = 81)
    (hp : SquareOrderNonregularSectorProfile G 9)
    (hhigh : (squareOrderHighVertices G 9).card = 15) :
    let c := squareOrderNineHighIncidenceHistogram G
    ¬ (c 0 = 16 ∧ c 1 = 0 ∧ c 2 = 45 ∧ c 3 = 20 ∧ c 4 = 0) := by
  dsimp only
  intro hprofile
  have hnot := squareOrderNine_not_unique_low_zero_no_one_incidence
    G hfree hmin hcover hcard hp (by omega)
  dsimp only at hnot
  apply hnot
  constructor
  · simpa [hhigh] using hprofile.1
  · exact hprofile.2.1

/-- The quotient obstruction sharpens the scalar fifteen-high census from
five candidates to the four profiles with exactly fifteen zero-incidence
vertices. -/
theorem squareOrderNine_highIncidence_profile_of_fifteen_high_refined
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G)
    (hmin : ∀ z : V, 9 ≤ G.degree z)
    (hcover : ∀ {u v}, G.Adj u v → G.degree u = 9 ∨ G.degree v = 9)
    (hcard : Fintype.card V = 81)
    (hp : SquareOrderNonregularSectorProfile G 9)
    (hhigh : (squareOrderHighVertices G 9).card = 15) :
    let c := squareOrderNineHighIncidenceHistogram G
    (c 0 = 15 ∧ c 1 = 3 ∧ c 2 = 42 ∧ c 3 = 21 ∧ c 4 = 0) ∨
    (c 0 = 15 ∧ c 1 = 2 ∧ c 2 = 45 ∧ c 3 = 18 ∧ c 4 = 1) ∨
    (c 0 = 15 ∧ c 1 = 1 ∧ c 2 = 48 ∧ c 3 = 15 ∧ c 4 = 2) ∨
    (c 0 = 15 ∧ c 1 = 0 ∧ c 2 = 51 ∧ c 3 = 12 ∧ c 4 = 3) := by
  dsimp only
  have hcases := squareOrderNine_highIncidence_profile_of_fifteen_high
    G hcard hp hhigh
  have hnot := squareOrderNine_not_first_fifteenHigh_incidence_profile
    G hfree hmin hcover hcard hp hhigh
  dsimp only at hcases hnot
  rcases hcases with hfirst | hsecond | hthird | hfourth | hfifth
  · exact (hnot hfirst).elim
  · exact Or.inl hsecond
  · exact Or.inr (Or.inl hthird)
  · exact Or.inr (Or.inr (Or.inl hfourth))
  · exact Or.inr (Or.inr (Or.inr hfifth))

end

end Erdos85

#print axioms Erdos85.squareOrderNine_not_first_fifteenHigh_incidence_profile
#print axioms Erdos85.squareOrderNine_not_unique_low_zero_no_one_incidence
#print axioms Erdos85.squareOrderNine_highIncidence_profile_of_fifteen_high_refined
