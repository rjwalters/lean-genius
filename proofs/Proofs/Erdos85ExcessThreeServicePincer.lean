import Proofs.Erdos85ExcessThreeServiceMoment

/-!
# The excess-three service pincer

This file runs the excess-one service accounting on the odd excess-three
stratum.  Write `B = A T` for the matching-incidence operator and
`S = A C` for the antipodal-service operator.  Off the diagonal both
mixed counts `B u X` and `B X u` lie in `{0,1}`, so the ordered pairs
with `B X u = 1` split into

* **negative commutator slots** (`B u X = 0`): these demand at least one
  unit of antipodal service, and at odd excess three there are exactly
  `(d-1)|V| + (2d-8)a` of them by the pinned commutator support count;
* **symmetric service pairs** (`B u X = 1` as well): these are exactly
  the ordered pairs of legs of a common triangle-free claw center.

Feeding the two families into the excess-three service-moment identity
`tr(A T A C) + tr(T C²) = |V|(d+3) + (2d-6)a` yields the demand-side
pincer inequality

`Σ_sym S + tr(T C²) ≤ 4|V| + 2a`,

the excess-three analogue of the excess-one bound `δ = 2(n - q)`.
-/

open SimpleGraph

namespace Erdos85

set_option maxHeartbeats 1600000

noncomputable section

/-- Off the diagonal, matching-incidence entries are zero or one in a
`C₄`-free graph. -/
theorem adj_mul_triangleFree_entry_eq_zero_or_one
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) {x y : V} (hxy : x ≠ y) :
    (G.adjMatrix ℤ * (triangleFreeEdgeGraph G).adjMatrix ℤ) x y = 0 ∨
      (G.adjMatrix ℤ * (triangleFreeEdgeGraph G).adjMatrix ℤ) x y = 1 := by
  have hnn : 0 ≤
      (G.adjMatrix ℤ * (triangleFreeEdgeGraph G).adjMatrix ℤ) x y := by
    rw [adjMatrix_mul_subgraph_apply_eq_card_mixed]
    exact Int.natCast_nonneg _
  have hle := adj_mul_triangleFree_entry_le_one G hfree hxy
  omega

/-- Reversing a mixed matching-incidence walk swaps the entry indices. -/
theorem triangleFree_mul_adj_apply_eq_flip
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj] (u X : V) :
    ((triangleFreeEdgeGraph G).adjMatrix ℤ * G.adjMatrix ℤ) u X =
      (G.adjMatrix ℤ * (triangleFreeEdgeGraph G).adjMatrix ℤ) X u := by
  simp only [Matrix.mul_apply]
  apply Finset.sum_congr rfl
  intro z _
  simp [SimpleGraph.adjMatrix_apply, adj_comm, mul_comm]

/-- The antipodal commutator entry is the flip difference of
matching-incidence entries. -/
theorem antipodal_commutator_apply_eq_flip_sub
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) {d : ℕ}
    (hreg : ∀ x, G.degree x = d) (u X : V) :
    (G.adjMatrix ℤ * (antipodalGraph G).adjMatrix ℤ -
        (antipodalGraph G).adjMatrix ℤ * G.adjMatrix ℤ) u X =
      (G.adjMatrix ℤ * (triangleFreeEdgeGraph G).adjMatrix ℤ) X u -
        (G.adjMatrix ℤ * (triangleFreeEdgeGraph G).adjMatrix ℤ) u X := by
  let A := G.adjMatrix ℤ
  let C := (antipodalGraph G).adjMatrix ℤ
  let T := (triangleFreeEdgeGraph G).adjMatrix ℤ
  have hcomm : A * (C + T) = (C + T) * A := by
    dsimp [A, C, T]
    rw [← secondOrderDefectGraph_adjMatrix_eq_antipodal_add_triangleFree G]
    exact adjMatrix_comm_secondOrderDefect_of_regular G hfree hreg
  have hneg := commutator_eq_neg_of_commutes_add A C T hcomm
  have hentry := congrFun (congrFun hneg u) X
  simp only [Matrix.sub_apply, Matrix.neg_apply] at hentry
  change (A * C) u X - (C * A) u X =
    (A * T) X u - (A * T) u X
  rw [hentry, ← triangleFree_mul_adj_apply_eq_flip G u X]
  change -((A * T) u X - (T * A) u X) = (T * A) u X - (A * T) u X
  ring

/-- A pair is a negative matching-commutator slot exactly when the
antipodal commutator equals one there. -/
theorem mem_matchingNegativeSlots_iff_commutator_eq_one
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) {d : ℕ}
    (hreg : ∀ x, G.degree x = d) (p : V × V) :
    p ∈ matchingNegativeSlots G ↔
      (G.adjMatrix ℤ * (antipodalGraph G).adjMatrix ℤ -
        (antipodalGraph G).adjMatrix ℤ * G.adjMatrix ℤ) p.1 p.2 = 1 := by
  have h := antipodal_commutator_apply_eq_flip_sub G hfree hreg p.1 p.2
  rw [mem_matchingNegativeSlots_iff]
  dsimp only
  omega

/-- **Negative-slot count at odd excess three.**  The number of negative
matching-commutator slots is exactly half the pinned commutator support:
`(d-1)|V| + (2d-8)a`. -/
theorem card_matchingNegativeSlots_excessThree
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) {d : ℕ} (hd : 7 ≤ d) (hodd : Odd d)
    (hreg : ∀ z, G.degree z = d)
    (hcard : Fintype.card V = d * (d - 1) + 6) :
    ((matchingNegativeSlots G).card : ℤ) =
      ((d : ℤ) - 1) * (Fintype.card V : ℤ) +
        (2 * (d : ℤ) - 8) *
          ((Finset.univ.filter fun x : V =>
            (triangleFreeEdgeGraph G).degree x = 3).card : ℤ) := by
  classical
  let A := G.adjMatrix ℤ
  let C := (antipodalGraph G).adjMatrix ℤ
  let K := A * C - C * A
  have hvals : ∀ p : V × V,
      K p.1 p.2 = -1 ∨ K p.1 p.2 = 0 ∨ K p.1 p.2 = 1 := fun p =>
    antipodal_commutator_entry_mem_neg_one_zero_one_all
      G hfree hreg p.1 p.2
  have hskew : ∀ u X : V, K X u = -(K u X) := by
    intro u X
    have h1 := antipodal_commutator_apply_eq_flip_sub G hfree hreg u X
    have h2 := antipodal_commutator_apply_eq_flip_sub G hfree hreg X u
    change K u X = _ at h1
    change K X u = _ at h2
    omega
  have hmass : (∑ p : V × V, (K p.1 p.2) ^ 2) =
      2 * (((d : ℤ) - 1) * (Fintype.card V : ℤ) +
        (2 * (d : ℤ) - 8) *
          ((Finset.univ.filter fun x : V =>
            (triangleFreeEdgeGraph G).degree x = 3).card : ℤ)) := by
    have h := sum_antipodal_commutator_entry_sq_excessThree
      G hfree hd hodd hreg hcard
    dsimp only at h
    rw [Fintype.sum_prod_type]
    exact h
  have hzero : (∑ p : V × V, K p.1 p.2) = 0 := by
    have hflip : (∑ p : V × V, K p.1 p.2) =
        ∑ p : V × V, -(K p.1 p.2) := by
      calc
        (∑ p : V × V, K p.1 p.2) = ∑ x : V, ∑ y : V, K x y :=
          Fintype.sum_prod_type _
        _ = ∑ y : V, ∑ x : V, K x y := Finset.sum_comm
        _ = ∑ y : V, ∑ x : V, -(K y x) := by
          apply Finset.sum_congr rfl
          intro y _
          apply Finset.sum_congr rfl
          intro x _
          exact hskew y x
        _ = ∑ p : V × V, -(K p.1 p.2) :=
          (Fintype.sum_prod_type (f := fun p : V × V => -(K p.1 p.2))).symm
    have hsum := hflip
    rw [Finset.sum_neg_distrib] at hsum
    omega
  have hpoint : ∀ p : V × V,
      (if p ∈ matchingNegativeSlots G then (2 : ℤ) else 0) =
        (K p.1 p.2) ^ 2 + K p.1 p.2 := by
    intro p
    have hiff := mem_matchingNegativeSlots_iff_commutator_eq_one
      G hfree hreg p
    by_cases hp : p ∈ matchingNegativeSlots G
    · have hK : K p.1 p.2 = 1 := hiff.mp hp
      rw [if_pos hp, hK]
      norm_num
    · have hK : K p.1 p.2 ≠ 1 := fun h => hp (hiff.mpr h)
      rw [if_neg hp]
      rcases hvals p with h | h | h
      · rw [h]; norm_num
      · rw [h]; norm_num
      · exact (hK h).elim
  have hdouble : 2 * ((matchingNegativeSlots G).card : ℤ) =
      ∑ p : V × V, ((K p.1 p.2) ^ 2 + K p.1 p.2) := by
    calc
      2 * ((matchingNegativeSlots G).card : ℤ) =
          ∑ p ∈ matchingNegativeSlots G, (2 : ℤ) := by
        rw [Finset.sum_const, nsmul_eq_mul]
        ring
      _ = ∑ p : V × V,
            (if p ∈ matchingNegativeSlots G then (2 : ℤ) else 0) := by
        rw [Finset.sum_ite_mem]
        congr 1
        exact (Finset.univ_inter _).symm
      _ = ∑ p : V × V, ((K p.1 p.2) ^ 2 + K p.1 p.2) := by
        apply Finset.sum_congr rfl
        intro p _
        exact hpoint p
  rw [Finset.sum_add_distrib, hmass, hzero, add_zero] at hdouble
  omega

/-- Ordered pairs served symmetrically through the matching incidence:
both mixed counts equal one.  These are exactly the leg pairs of the
triangle-free claws. -/
def symmetricServicePairs
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj] : Finset (V × V) := by
  classical
  exact (Finset.univ.product Finset.univ).filter fun p =>
    p.1 ≠ p.2 ∧
      (G.adjMatrix ℤ * (triangleFreeEdgeGraph G).adjMatrix ℤ)
        p.1 p.2 = 1 ∧
      (G.adjMatrix ℤ * (triangleFreeEdgeGraph G).adjMatrix ℤ)
        p.2 p.1 = 1

@[simp] theorem mem_symmetricServicePairs_iff
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj] (p : V × V) :
    p ∈ symmetricServicePairs G ↔
      p.1 ≠ p.2 ∧
        (G.adjMatrix ℤ * (triangleFreeEdgeGraph G).adjMatrix ℤ)
          p.1 p.2 = 1 ∧
        (G.adjMatrix ℤ * (triangleFreeEdgeGraph G).adjMatrix ℤ)
          p.2 p.1 = 1 := by
  classical
  simp only [symmetricServicePairs, Finset.mem_filter]
  constructor
  · exact fun h => h.2
  · intro h
    exact ⟨by simp, h⟩

/-- **Claw characterization of symmetric service pairs.**  Two distinct
vertices form a symmetric service pair exactly when they are the far legs
of two triangle-free edges through a common center. -/
theorem mem_symmetricServicePairs_iff_exists_center
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) (p : V × V) :
    p ∈ symmetricServicePairs G ↔
      p.1 ≠ p.2 ∧ ∃ z : V,
        (triangleFreeEdgeGraph G).Adj z p.1 ∧
          (triangleFreeEdgeGraph G).Adj z p.2 := by
  rw [mem_symmetricServicePairs_iff]
  constructor
  · rintro ⟨hne, h12, h21⟩
    refine ⟨hne, ?_⟩
    rw [adjMatrix_mul_subgraph_apply_eq_card_mixed] at h12 h21
    have h12' : (G.neighborFinset p.1 ∩
        (triangleFreeEdgeGraph G).neighborFinset p.2).card = 1 := by
      exact_mod_cast h12
    have h21' : (G.neighborFinset p.2 ∩
        (triangleFreeEdgeGraph G).neighborFinset p.1).card = 1 := by
      exact_mod_cast h21
    obtain ⟨z, hz⟩ := Finset.card_eq_one.mp h12'
    obtain ⟨w, hw⟩ := Finset.card_eq_one.mp h21'
    have hzmem : z ∈ G.neighborFinset p.1 ∩
        (triangleFreeEdgeGraph G).neighborFinset p.2 := by
      rw [hz]
      exact Finset.mem_singleton_self z
    have hwmem : w ∈ G.neighborFinset p.2 ∩
        (triangleFreeEdgeGraph G).neighborFinset p.1 := by
      rw [hw]
      exact Finset.mem_singleton_self w
    have hz1 : G.Adj p.1 z :=
      (G.mem_neighborFinset p.1 z).mp (Finset.mem_inter.mp hzmem).1
    have hz2T : (triangleFreeEdgeGraph G).Adj p.2 z :=
      ((triangleFreeEdgeGraph G).mem_neighborFinset p.2 z).mp
        (Finset.mem_inter.mp hzmem).2
    have hw2 : G.Adj p.2 w :=
      (G.mem_neighborFinset p.2 w).mp (Finset.mem_inter.mp hwmem).1
    have hw1T : (triangleFreeEdgeGraph G).Adj p.1 w :=
      ((triangleFreeEdgeGraph G).mem_neighborFinset p.1 w).mp
        (Finset.mem_inter.mp hwmem).2
    have hz2 : G.Adj p.2 z :=
      ((mem_triangleFreeNeighbors G p.2 z).mp
        ((triangleFreeEdgeGraph_adj G p.2 z).mp hz2T)).1
    have hw1 : G.Adj p.1 w :=
      ((mem_triangleFreeNeighbors G p.1 w).mp
        ((triangleFreeEdgeGraph_adj G p.1 w).mp hw1T)).1
    have hcommon : ({z, w} : Finset V) ⊆
        G.neighborFinset p.1 ∩ G.neighborFinset p.2 := by
      intro v hv
      simp only [Finset.mem_insert, Finset.mem_singleton] at hv
      rcases hv with rfl | rfl
      · exact Finset.mem_inter.mpr
          ⟨(G.mem_neighborFinset p.1 v).mpr hz1,
            (G.mem_neighborFinset p.2 v).mpr hz2⟩
      · exact Finset.mem_inter.mpr
          ⟨(G.mem_neighborFinset p.1 v).mpr hw1,
            (G.mem_neighborFinset p.2 v).mpr hw2⟩
    have hzw : z = w := by
      by_contra hzw
      have hpair : ({z, w} : Finset V).card = 2 := by
        simp [hzw]
      have hle := Finset.card_le_card hcommon
      rw [hpair] at hle
      have hone := common_le_one_of_not_containsC4 hfree p.1 p.2 hne
      omega
    subst hzw
    exact ⟨z, hw1T.symm, hz2T.symm⟩
  · rintro ⟨hne, z, hz1, hz2⟩
    refine ⟨hne, ?_, ?_⟩
    · have hle := adj_mul_triangleFree_entry_le_one G hfree hne
      have hmem : z ∈ G.neighborFinset p.1 ∩
          (triangleFreeEdgeGraph G).neighborFinset p.2 := by
        refine Finset.mem_inter.mpr ⟨?_, ?_⟩
        · exact (G.mem_neighborFinset p.1 z).mpr
            (((mem_triangleFreeNeighbors G z p.1).mp
              ((triangleFreeEdgeGraph_adj G z p.1).mp hz1)).1).symm
        · exact ((triangleFreeEdgeGraph G).mem_neighborFinset p.2 z).mpr
            hz2.symm
      have hpos : 0 <
          (G.neighborFinset p.1 ∩
            (triangleFreeEdgeGraph G).neighborFinset p.2).card :=
        Finset.card_pos.mpr ⟨z, hmem⟩
      rw [adjMatrix_mul_subgraph_apply_eq_card_mixed] at hle ⊢
      have hle' : (G.neighborFinset p.1 ∩
          (triangleFreeEdgeGraph G).neighborFinset p.2).card ≤ 1 := by
        exact_mod_cast hle
      have hone : (G.neighborFinset p.1 ∩
          (triangleFreeEdgeGraph G).neighborFinset p.2).card = 1 := by
        omega
      exact_mod_cast hone
    · have hle := adj_mul_triangleFree_entry_le_one G hfree hne.symm
      have hmem : z ∈ G.neighborFinset p.2 ∩
          (triangleFreeEdgeGraph G).neighborFinset p.1 := by
        refine Finset.mem_inter.mpr ⟨?_, ?_⟩
        · exact (G.mem_neighborFinset p.2 z).mpr
            (((mem_triangleFreeNeighbors G z p.2).mp
              ((triangleFreeEdgeGraph_adj G z p.2).mp hz2)).1).symm
        · exact ((triangleFreeEdgeGraph G).mem_neighborFinset p.1 z).mpr
            hz1.symm
      have hpos : 0 <
          (G.neighborFinset p.2 ∩
            (triangleFreeEdgeGraph G).neighborFinset p.1).card :=
        Finset.card_pos.mpr ⟨z, hmem⟩
      rw [adjMatrix_mul_subgraph_apply_eq_card_mixed] at hle ⊢
      have hle' : (G.neighborFinset p.2 ∩
          (triangleFreeEdgeGraph G).neighborFinset p.1).card ≤ 1 := by
        exact_mod_cast hle
      have hone : (G.neighborFinset p.2 ∩
          (triangleFreeEdgeGraph G).neighborFinset p.1).card = 1 := by
        omega
      exact_mod_cast hone

/-- **Pointwise service selector.**  A matching-incidence weight selects
exactly the negative slots and the symmetric pairs. -/
theorem matchingIncidence_mul_service_eq_indicator_add_symmetric
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) (u X : V) :
    let B := G.adjMatrix ℤ * (triangleFreeEdgeGraph G).adjMatrix ℤ
    let S := G.adjMatrix ℤ * (antipodalGraph G).adjMatrix ℤ
    B X u * S u X =
      (if (u, X) ∈ matchingNegativeSlots G then S u X else 0) +
        (if (u, X) ∈ symmetricServicePairs G then S u X else 0) := by
  classical
  dsimp only
  let B := G.adjMatrix ℤ * (triangleFreeEdgeGraph G).adjMatrix ℤ
  let S := G.adjMatrix ℤ * (antipodalGraph G).adjMatrix ℤ
  change B X u * S u X =
    (if (u, X) ∈ matchingNegativeSlots G then S u X else 0) +
      (if (u, X) ∈ symmetricServicePairs G then S u X else 0)
  by_cases hux : u = X
  · subst X
    have hS : S u u = 0 := by
      simpa [S] using adjMatrix_mul_antipodal_apply_self_eq_zero G u
    have hneg : (u, u) ∉ matchingNegativeSlots G := by
      rw [mem_matchingNegativeSlots_iff]
      dsimp only
      change ¬(B u u - B u u = -1)
      omega
    have hsym : (u, u) ∉ symmetricServicePairs G := by
      rw [mem_symmetricServicePairs_iff]
      simp
    rw [if_neg hneg, if_neg hsym, hS]
    ring
  · have hBux := adj_mul_triangleFree_entry_eq_zero_or_one G hfree hux
    have hBXu := adj_mul_triangleFree_entry_eq_zero_or_one G hfree
      (Ne.symm hux)
    change B u X = 0 ∨ B u X = 1 at hBux
    change B X u = 0 ∨ B X u = 1 at hBXu
    rcases hBXu with hBXu | hBXu
    · have hneg : (u, X) ∉ matchingNegativeSlots G := by
        rw [mem_matchingNegativeSlots_iff]
        dsimp only
        change ¬(B u X - B X u = -1)
        rcases hBux with h | h <;> omega
      have hsym : (u, X) ∉ symmetricServicePairs G := by
        rw [mem_symmetricServicePairs_iff]
        push_neg
        intro _ _
        change ¬(B X u = 1)
        omega
      rw [if_neg hneg, if_neg hsym, hBXu]
      ring
    · rcases hBux with hBux | hBux
      · have hneg : (u, X) ∈ matchingNegativeSlots G := by
          rw [mem_matchingNegativeSlots_iff]
          dsimp only
          change B u X - B X u = -1
          omega
        have hsym : (u, X) ∉ symmetricServicePairs G := by
          rw [mem_symmetricServicePairs_iff]
          push_neg
          intro _ h
          change B u X = 1 at h
          omega
        rw [if_pos hneg, if_neg hsym, hBXu]
        ring
      · have hneg : (u, X) ∉ matchingNegativeSlots G := by
          rw [mem_matchingNegativeSlots_iff]
          dsimp only
          change ¬(B u X - B X u = -1)
          omega
        have hsym : (u, X) ∈ symmetricServicePairs G := by
          rw [mem_symmetricServicePairs_iff]
          exact ⟨hux, hBux, hBXu⟩
        rw [if_neg hneg, if_pos hsym, hBXu]
        ring

/-- **Service trace split.**  The mixed fourth moment is the total
antipodal service over negative slots plus symmetric pairs. -/
theorem trace_serviceMoment_eq_sum_negative_add_symmetric
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) :
    let A := G.adjMatrix ℤ
    let T := (triangleFreeEdgeGraph G).adjMatrix ℤ
    let C := (antipodalGraph G).adjMatrix ℤ
    Matrix.trace (A * T * A * C) =
      (∑ p ∈ matchingNegativeSlots G, (A * C) p.1 p.2) +
        ∑ p ∈ symmetricServicePairs G, (A * C) p.1 p.2 := by
  classical
  dsimp only
  let A := G.adjMatrix ℤ
  let T := (triangleFreeEdgeGraph G).adjMatrix ℤ
  let C := (antipodalGraph G).adjMatrix ℤ
  let B := A * T
  let S := A * C
  have hpoint : ∀ u X : V,
      B X u * S u X =
        (if (u, X) ∈ matchingNegativeSlots G then S u X else 0) +
          (if (u, X) ∈ symmetricServicePairs G then S u X else 0) := by
    intro u X
    simpa [A, T, C, B, S] using
      matchingIncidence_mul_service_eq_indicator_add_symmetric
        G hfree u X
  have hfactor : A * T * A * C = B * S := by
    simp [B, S, Matrix.mul_assoc]
  rw [hfactor]
  change Matrix.trace (B * S) =
    (∑ p ∈ matchingNegativeSlots G, S p.1 p.2) +
      ∑ p ∈ symmetricServicePairs G, S p.1 p.2
  have hsplitsum : ∀ F : Finset (V × V),
      (∑ p ∈ F, S p.1 p.2) =
        ∑ u : V, ∑ X : V, if (u, X) ∈ F then S u X else 0 := by
    intro F
    calc
      (∑ p ∈ F, S p.1 p.2) =
          ∑ p ∈ (Finset.univ.product Finset.univ).filter (fun p => p ∈ F),
            S p.1 p.2 := by
        congr 1
        apply Finset.ext
        intro p
        rw [Finset.mem_filter]
        constructor
        · exact fun h => ⟨by simp, h⟩
        · exact fun h => h.2
      _ = ∑ p ∈ Finset.univ.product Finset.univ,
            if p ∈ F then S p.1 p.2 else 0 := by
        rw [Finset.sum_filter]
      _ = ∑ u : V, ∑ X : V, if (u, X) ∈ F then S u X else 0 := by
        exact Finset.sum_product
          (Finset.univ : Finset V) (Finset.univ : Finset V)
          (fun p : V × V => if p ∈ F then S p.1 p.2 else 0)
  rw [Matrix.trace]
  calc
    (∑ X : V, (B * S) X X) =
        ∑ X : V, ∑ u : V, B X u * S u X := by
      apply Finset.sum_congr rfl
      intro X _
      rw [Matrix.mul_apply]
    _ = ∑ u : V, ∑ X : V, B X u * S u X := Finset.sum_comm
    _ = ∑ u : V, ∑ X : V,
          ((if (u, X) ∈ matchingNegativeSlots G then S u X else 0) +
            (if (u, X) ∈ symmetricServicePairs G then S u X else 0)) := by
      apply Finset.sum_congr rfl
      intro u _
      apply Finset.sum_congr rfl
      intro X _
      exact hpoint u X
    _ = (∑ u : V, ∑ X : V,
          if (u, X) ∈ matchingNegativeSlots G then S u X else 0) +
        ∑ u : V, ∑ X : V,
          if (u, X) ∈ symmetricServicePairs G then S u X else 0 := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro u _
      rw [← Finset.sum_add_distrib]
    _ = (∑ p ∈ matchingNegativeSlots G, S p.1 p.2) +
        ∑ p ∈ symmetricServicePairs G, S p.1 p.2 := by
      rw [hsplitsum (matchingNegativeSlots G),
        hsplitsum (symmetricServicePairs G)]

/-- Every negative slot demands at least one unit of antipodal service. -/
theorem one_le_service_of_matchingNegativeSlot
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) {d : ℕ}
    (hreg : ∀ x, G.degree x = d) {p : V × V}
    (hp : p ∈ matchingNegativeSlots G) :
    1 ≤ (G.adjMatrix ℤ * (antipodalGraph G).adjMatrix ℤ) p.1 p.2 := by
  have hK := (mem_matchingNegativeSlots_iff_commutator_eq_one
    G hfree hreg p).mp hp
  simp only [Matrix.sub_apply] at hK
  have hCA : 0 ≤
      ((antipodalGraph G).adjMatrix ℤ * G.adjMatrix ℤ) p.1 p.2 := by
    rw [adjMatrix_mul_subgraph_apply_eq_card_mixed]
    exact Int.natCast_nonneg _
  omega

/-- Antipodal service is a count, hence nonnegative. -/
theorem service_nonneg
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj] (u X : V) :
    0 ≤ (G.adjMatrix ℤ * (antipodalGraph G).adjMatrix ℤ) u X := by
  rw [adjMatrix_mul_subgraph_apply_eq_card_mixed]
  exact Int.natCast_nonneg _

/-- The mixed chord moment `tr(T C²)` is a walk count, hence nonnegative. -/
theorem trace_triangleFree_antipodal_sq_nonneg
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj] :
    0 ≤ Matrix.trace ((triangleFreeEdgeGraph G).adjMatrix ℤ *
        (antipodalGraph G).adjMatrix ℤ *
        (antipodalGraph G).adjMatrix ℤ) := by
  rw [Matrix.trace]
  apply Finset.sum_nonneg
  intro x _
  simp only [Matrix.diag_apply]
  rw [Matrix.mul_apply]
  apply Finset.sum_nonneg
  intro z _
  apply mul_nonneg
  · rw [adjMatrix_mul_subgraph_apply_eq_card_mixed]
    exact Int.natCast_nonneg _
  · by_cases h : (antipodalGraph G).Adj z x <;>
      simp only [SimpleGraph.adjMatrix_apply, h, if_true, if_false] <;>
      first
        | (split_ifs <;> norm_num)
        | norm_num

/-- **Demand jaw of the excess-three pincer.**  Discharging one service
unit per negative slot leaves the symmetric service and the chord moment
bounded by `4|V| + 2a`. -/
theorem excessThree_symmetricService_add_chord_le
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) {d : ℕ} (hd : 7 ≤ d) (hodd : Odd d)
    (hreg : ∀ z, G.degree z = d)
    (hcard : Fintype.card V = d * (d - 1) + 6) :
    (∑ p ∈ symmetricServicePairs G,
        (G.adjMatrix ℤ * (antipodalGraph G).adjMatrix ℤ) p.1 p.2) +
      Matrix.trace ((triangleFreeEdgeGraph G).adjMatrix ℤ *
        (antipodalGraph G).adjMatrix ℤ *
        (antipodalGraph G).adjMatrix ℤ) ≤
      4 * (Fintype.card V : ℤ) + 2 *
        ((Finset.univ.filter fun x : V =>
          (triangleFreeEdgeGraph G).degree x = 3).card : ℤ) := by
  classical
  have hmoment := excessThree_trace_serviceMoment_add_triangleFree_antipodal_sq
    G hfree hd hodd hreg hcard
  dsimp only at hmoment
  have hsplit := trace_serviceMoment_eq_sum_negative_add_symmetric G hfree
  dsimp only at hsplit
  have hcount := card_matchingNegativeSlots_excessThree
    G hfree hd hodd hreg hcard
  have hlow : ((matchingNegativeSlots G).card : ℤ) ≤
      ∑ p ∈ matchingNegativeSlots G,
        (G.adjMatrix ℤ * (antipodalGraph G).adjMatrix ℤ) p.1 p.2 := by
    calc
      ((matchingNegativeSlots G).card : ℤ) =
          ∑ _p ∈ matchingNegativeSlots G, (1 : ℤ) := by
        rw [Finset.sum_const, nsmul_eq_mul, mul_one]
      _ ≤ ∑ p ∈ matchingNegativeSlots G,
            (G.adjMatrix ℤ * (antipodalGraph G).adjMatrix ℤ) p.1 p.2 := by
        apply Finset.sum_le_sum
        intro p hp
        exact one_le_service_of_matchingNegativeSlot G hfree hreg hp
  rw [hcount] at hlow
  rw [hsplit] at hmoment
  linarith

/-- The chord moment alone is bounded by `4|V| + 2a` at odd excess three:
the excess-three analogue of the excess-one collapse of `tr(M C²)`. -/
theorem excessThree_trace_triangleFree_antipodal_sq_le
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) {d : ℕ} (hd : 7 ≤ d) (hodd : Odd d)
    (hreg : ∀ z, G.degree z = d)
    (hcard : Fintype.card V = d * (d - 1) + 6) :
    Matrix.trace ((triangleFreeEdgeGraph G).adjMatrix ℤ *
        (antipodalGraph G).adjMatrix ℤ *
        (antipodalGraph G).adjMatrix ℤ) ≤
      4 * (Fintype.card V : ℤ) + 2 *
        ((Finset.univ.filter fun x : V =>
          (triangleFreeEdgeGraph G).degree x = 3).card : ℤ) := by
  have h := excessThree_symmetricService_add_chord_le
    G hfree hd hodd hreg hcard
  have hnn : 0 ≤ ∑ p ∈ symmetricServicePairs G,
      (G.adjMatrix ℤ * (antipodalGraph G).adjMatrix ℤ) p.1 p.2 :=
    Finset.sum_nonneg fun p _ => service_nonneg G p.1 p.2
  linarith

/-- The symmetric (claw) service alone is bounded by `4|V| + 2a`. -/
theorem excessThree_symmetricService_le
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) {d : ℕ} (hd : 7 ≤ d) (hodd : Odd d)
    (hreg : ∀ z, G.degree z = d)
    (hcard : Fintype.card V = d * (d - 1) + 6) :
    (∑ p ∈ symmetricServicePairs G,
        (G.adjMatrix ℤ * (antipodalGraph G).adjMatrix ℤ) p.1 p.2) ≤
      4 * (Fintype.card V : ℤ) + 2 *
        ((Finset.univ.filter fun x : V =>
          (triangleFreeEdgeGraph G).degree x = 3).card : ℤ) := by
  have h := excessThree_symmetricService_add_chord_le
    G hfree hd hodd hreg hcard
  have hnn := trace_triangleFree_antipodal_sq_nonneg G
  linarith

end

end Erdos85
