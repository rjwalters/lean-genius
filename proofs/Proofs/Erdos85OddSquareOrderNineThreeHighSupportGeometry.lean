import Proofs.Erdos85OddSquareOrderNineThreeHighDefectDecomposition

/-! # High-pair support geometry in the q = 9 three-high profiles

Node: B.3 / GAP B-CLASSIFY.  Every pair of high roots has a unique common
witness.  At three highs, the scalar profile decides whether these witnesses
are the three distinct bin-two points or the unique bin-three point.
-/

open Finset SimpleGraph

namespace Erdos85

noncomputable section

/-- Every distinct pair of q=9 high roots has a unique common low witness,
whose high-incidence count is 2, 3, or 4. -/
theorem squareOrderNine_existsUnique_common_high_with_incidence_two_three_four
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G)
    (hmin : ∀ z : V, 9 ≤ G.degree z)
    (hcard : Fintype.card V = 81)
    (hp : SquareOrderNonregularSectorProfile G 9)
    {a b : V}
    (ha : a ∈ squareOrderHighVertices G 9)
    (hb : b ∈ squareOrderHighVertices G 9)
    (hab : a ≠ b) :
    ∃! x, G.Adj a x ∧ G.Adj b x ∧
      (squareOrderHighIncidenceCount G 9 x = 2 ∨
       squareOrderHighIncidenceCount G 9 x = 3 ∨
       squareOrderHighIncidenceCount G 9 x = 4) := by
  classical
  let H := squareOrderHighVertices G 9
  let k := squareOrderHighIncidenceCount G 9
  have ha10 : G.degree a = 10 := (Finset.mem_filter.mp ha).2
  have hcommon := squareOrder_card_common_highRoot_eq_one
    G hfree (by norm_num) hmin hcard ha10 hab
  rcases Finset.card_eq_one.mp hcommon with ⟨x, hxset⟩
  have hxmem : x ∈ G.neighborFinset a ∩ G.neighborFinset b := by simp [hxset]
  have hax : G.Adj a x :=
    (G.mem_neighborFinset a x).mp (Finset.mem_inter.mp hxmem).1
  have hbx : G.Adj b x :=
    (G.mem_neighborFinset b x).mp (Finset.mem_inter.mp hxmem).2
  have hnotHigh : x ∉ H := by
    intro hxH
    exact hp.high_independent ha hxH hax
  have hxlow : G.degree x = 9 := by
    rcases hp.degree_dichotomy x with hlo | hhi
    · exact hlo
    · exact (hnotHigh (Finset.mem_filter.mpr ⟨by simp, hhi⟩)).elim
  have hkle : k x ≤ 4 := by
    have h := hp.low_incidence_bound hxlow
    change 2 * k x ≤ 9 at h
    omega
  have haK : a ∈ G.neighborFinset x ∩ H := by
    exact Finset.mem_inter.mpr
      ⟨(G.mem_neighborFinset x a).mpr ((G.adj_comm a x).mp hax), ha⟩
  have hbK : b ∈ G.neighborFinset x ∩ H := by
    exact Finset.mem_inter.mpr
      ⟨(G.mem_neighborFinset x b).mpr ((G.adj_comm b x).mp hbx), hb⟩
  have htwo : 2 ≤ k x := by
    change 2 ≤ (G.neighborFinset x ∩ H).card
    have hsub : ({a, b} : Finset V) ⊆ G.neighborFinset x ∩ H := by
      intro z hz
      simp only [Finset.mem_insert, Finset.mem_singleton] at hz
      rcases hz with rfl | rfl
      · exact haK
      · exact hbK
    calc
      2 = ({a, b} : Finset V).card := by simp [hab]
      _ ≤ (G.neighborFinset x ∩ H).card := Finset.card_le_card hsub
  have hkcases : k x = 2 ∨ k x = 3 ∨ k x = 4 := by omega
  refine ⟨x, ⟨hax, hbx, ?_⟩, ?_⟩
  · exact hkcases
  intro y hy
  have hymem : y ∈ G.neighborFinset a ∩ G.neighborFinset b := by
    exact Finset.mem_inter.mpr
      ⟨(G.mem_neighborFinset a y).mpr hy.1,
       (G.mem_neighborFinset b y).mpr hy.2.1⟩
  simpa [hxset] using hymem

/-- In the first h=3 profile, each high pair has a unique bin-two witness. -/
theorem squareOrderNine_threeHigh_firstProfile_existsUnique_pairWitness
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G)
    (hmin : ∀ z : V, 9 ≤ G.degree z)
    (hcard : Fintype.card V = 81)
    (hp : SquareOrderNonregularSectorProfile G 9)
    (hc3 : squareOrderNineHighIncidenceHistogram G 3 = 0)
    (hc4 : squareOrderNineHighIncidenceHistogram G 4 = 0)
    {a b : V}
    (ha : a ∈ squareOrderHighVertices G 9)
    (hb : b ∈ squareOrderHighVertices G 9)
    (hab : a ≠ b) :
    ∃! x, x ∈ squareOrderNineLowIncidenceBin G 2 ∧
      G.Adj a x ∧ G.Adj b x := by
  classical
  let k := squareOrderHighIncidenceCount G 9
  let Z3 := (Finset.univ : Finset V).filter fun x => k x = 3
  let Z4 := (Finset.univ : Finset V).filter fun x => k x = 4
  have hZ3 : Z3 = ∅ := by
    rw [← Finset.card_eq_zero]
    simpa [Z3, k, squareOrderNineHighIncidenceHistogram,
      boundedHistogram] using hc3
  have hZ4 : Z4 = ∅ := by
    rw [← Finset.card_eq_zero]
    simpa [Z4, k, squareOrderNineHighIncidenceHistogram,
      boundedHistogram] using hc4
  rcases squareOrderNine_existsUnique_common_high_with_incidence_two_three_four
      G hfree hmin hcard hp ha hb hab with ⟨x, hx, huniq⟩
  have hk2 : k x = 2 := by
    rcases hx.2.2 with hk2 | hk3 | hk4
    · exact hk2
    · have : x ∈ Z3 := Finset.mem_filter.mpr ⟨by simp, hk3⟩
      rw [hZ3] at this
      exact (Finset.notMem_empty x this).elim
    · have : x ∈ Z4 := Finset.mem_filter.mpr ⟨by simp, hk4⟩
      rw [hZ4] at this
      exact (Finset.notMem_empty x this).elim
  have hxnot : x ∉ squareOrderHighVertices G 9 := by
    intro hxH
    exact hp.high_independent ha hxH hx.1
  have hxB : x ∈ squareOrderNineLowIncidenceBin G 2 :=
    Finset.mem_filter.mpr
      ⟨Finset.mem_sdiff.mpr ⟨by simp, hxnot⟩, hk2⟩
  refine ⟨x, ⟨hxB, hx.1, hx.2.1⟩, ?_⟩
  intro y hy
  apply huniq y
  exact ⟨hy.2.1, hy.2.2, Or.inl (Finset.mem_filter.mp hy.1).2⟩

/-- In the second h=3 profile, every high pair has the same unique bin-three
witness; in particular that point is adjacent to all three high roots. -/
theorem squareOrderNine_threeHigh_secondProfile_existsUnique_pairWitness
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G)
    (hmin : ∀ z : V, 9 ≤ G.degree z)
    (hcard : Fintype.card V = 81)
    (hp : SquareOrderNonregularSectorProfile G 9)
    (hc2 : squareOrderNineHighIncidenceHistogram G 2 = 0)
    (hc4 : squareOrderNineHighIncidenceHistogram G 4 = 0)
    {a b : V}
    (ha : a ∈ squareOrderHighVertices G 9)
    (hb : b ∈ squareOrderHighVertices G 9)
    (hab : a ≠ b) :
    ∃! x, x ∈ squareOrderNineLowIncidenceBin G 3 ∧
      G.Adj a x ∧ G.Adj b x := by
  classical
  let k := squareOrderHighIncidenceCount G 9
  let Z2 := (Finset.univ : Finset V).filter fun x => k x = 2
  let Z4 := (Finset.univ : Finset V).filter fun x => k x = 4
  have hZ2 : Z2 = ∅ := by
    rw [← Finset.card_eq_zero]
    simpa [Z2, k, squareOrderNineHighIncidenceHistogram,
      boundedHistogram] using hc2
  have hZ4 : Z4 = ∅ := by
    rw [← Finset.card_eq_zero]
    simpa [Z4, k, squareOrderNineHighIncidenceHistogram,
      boundedHistogram] using hc4
  rcases squareOrderNine_existsUnique_common_high_with_incidence_two_three_four
      G hfree hmin hcard hp ha hb hab with ⟨x, hx, huniq⟩
  have hk3 : k x = 3 := by
    rcases hx.2.2 with hk2 | hk3 | hk4
    · have : x ∈ Z2 := Finset.mem_filter.mpr ⟨by simp, hk2⟩
      rw [hZ2] at this
      exact (Finset.notMem_empty x this).elim
    · exact hk3
    · have : x ∈ Z4 := Finset.mem_filter.mpr ⟨by simp, hk4⟩
      rw [hZ4] at this
      exact (Finset.notMem_empty x this).elim
  have hxnot : x ∉ squareOrderHighVertices G 9 := by
    intro hxH
    exact hp.high_independent ha hxH hx.1
  have hxB : x ∈ squareOrderNineLowIncidenceBin G 3 :=
    Finset.mem_filter.mpr
      ⟨Finset.mem_sdiff.mpr ⟨by simp, hxnot⟩, hk3⟩
  refine ⟨x, ⟨hxB, hx.1, hx.2.1⟩, ?_⟩
  intro y hy
  apply huniq y
  exact ⟨hy.2.1, hy.2.2, Or.inr (Or.inl (Finset.mem_filter.mp hy.1).2)⟩

end


end Erdos85

#print axioms
  Erdos85.squareOrderNine_existsUnique_common_high_with_incidence_two_three_four
#print axioms
  Erdos85.squareOrderNine_threeHigh_firstProfile_existsUnique_pairWitness
#print axioms
  Erdos85.squareOrderNine_threeHigh_secondProfile_existsUnique_pairWitness
