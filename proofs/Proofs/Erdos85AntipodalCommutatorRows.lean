import Proofs.Erdos85AntipodalCommutatorRigidity

/-!
# Row rigidity for the antipodal commutator

The global support count becomes useful only after localization.  This file
computes the signed sum of each commutator row and identifies the two color
degrees in the odd excess-three case.
-/

open SimpleGraph

namespace Erdos85

noncomputable section

theorem sum_adjMatrix_row_eq_degree_int
    {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) [DecidableRel H.Adj] (x : V) :
    ∑ y, H.adjMatrix ℤ x y = (H.degree x : ℤ) := by
  simp [SimpleGraph.adjMatrix_apply, degree, neighborFinset_eq_filter,
    Finset.sum_boole]

/-- For a finite `{-1,0,1}`-valued function, its support dominates the
absolute value of its signed sum. -/
theorem abs_sum_le_card_support_of_mem_neg_one_zero_one
    {ι : Type*} [Fintype ι] [DecidableEq ι] (f : ι → ℤ)
    (hf : ∀ x, f x = -1 ∨ f x = 0 ∨ f x = 1) :
    |∑ x, f x| ≤ ((Finset.univ.filter fun x => f x ≠ 0).card : ℤ) := by
  calc
    |∑ x, f x| ≤ ∑ x, |f x| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ x, (f x) ^ 2 := by
      apply Finset.sum_congr rfl
      intro x _
      rcases hf x with hx | hx | hx <;> simp [hx]
    _ = ((Finset.univ.filter fun x => f x ≠ 0).card : ℤ) :=
      (int_card_filter_ne_zero_eq_sum_sq f hf).symm

/-- Row sum of a graph commutator: adjacency averages the color degree,
whereas the reversed product sees the regular degree of the ambient graph. -/
theorem sum_adjMatrix_commutator_row_eq_neighborDegreeSum_sub
    {V : Type*} [Fintype V] [DecidableEq V]
    (G H : SimpleGraph V) [DecidableRel G.Adj] [DecidableRel H.Adj]
    {d : ℕ} (hreg : ∀ x, G.degree x = d) (x : V) :
    ∑ y, ((G.adjMatrix ℤ * H.adjMatrix ℤ -
      H.adjMatrix ℤ * G.adjMatrix ℤ) x y) =
      (∑ z ∈ G.neighborFinset x, (H.degree z : ℤ)) -
        (d : ℤ) * (H.degree x : ℤ) := by
  simp only [Matrix.sub_apply]
  rw [Finset.sum_sub_distrib]
  congr 1
  · simp only [Matrix.mul_apply]
    calc
      (∑ y, ∑ z, G.adjMatrix ℤ x z * H.adjMatrix ℤ z y) =
          ∑ z, G.adjMatrix ℤ x z * ∑ y, H.adjMatrix ℤ z y := by
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro z _
        rw [Finset.mul_sum]
      _ = ∑ z, G.adjMatrix ℤ x z * (H.degree z : ℤ) := by
        apply Finset.sum_congr rfl
        intro z _
        rw [sum_adjMatrix_row_eq_degree_int]
      _ = ∑ z ∈ G.neighborFinset x, (H.degree z : ℤ) := by
        simp [SimpleGraph.adjMatrix_apply, neighborFinset_eq_filter,
          Finset.sum_filter]
  · simp only [Matrix.mul_apply]
    calc
      (∑ y, ∑ z, H.adjMatrix ℤ x z * G.adjMatrix ℤ z y) =
          ∑ z, H.adjMatrix ℤ x z * ∑ y, G.adjMatrix ℤ z y := by
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro z _
        rw [Finset.mul_sum]
      _ = ∑ z, H.adjMatrix ℤ x z * (d : ℤ) := by
        apply Finset.sum_congr rfl
        intro z _
        rw [sum_adjMatrix_row_eq_degree_int, hreg]
      _ = (d : ℤ) * (H.degree x : ℤ) := by
        rw [← Finset.sum_mul, sum_adjMatrix_row_eq_degree_int]
        ring

/-- In odd excess three the triangle-free degree is `1` or `3`, and the
complementary antipodal degree is respectively `4` or `2`. -/
theorem excessThree_antipodal_degree_eq_four_or_two
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) {d : ℕ} (hd : 7 ≤ d) (hodd : Odd d)
    (hreg : ∀ z, G.degree z = d)
    (hcard : Fintype.card V = d * (d - 1) + 6) (x : V) :
    ((triangleFreeEdgeGraph G).degree x = 1 ∧
        (antipodalGraph G).degree x = 4) ∨
      ((triangleFreeEdgeGraph G).degree x = 3 ∧
        (antipodalGraph G).degree x = 2) := by
  have hD : (secondOrderDefectGraph G).degree x = 5 := by
    simpa using secondOrderDefectGraph_degree_eq_excess_add_two
      G hfree hreg (e := 3) (by omega) x
  have hsum : (antipodalGraph G).degree x +
      (triangleFreeEdgeGraph G).degree x = 5 := by
    rw [← (antipodalGraph G).card_neighborFinset_eq_degree,
      antipodalGraph_neighborFinset,
      ← (triangleFreeEdgeGraph G).card_neighborFinset_eq_degree,
      triangleFreeEdgeGraph_neighborFinset,
      ← hD, ← (secondOrderDefectGraph G).card_neighborFinset_eq_degree,
      secondOrderDefectGraph_neighborFinset,
      Finset.card_union_of_disjoint
        (disjoint_antipodal_triangleFreeNeighbors G x)]
  have hTdeg : (triangleFreeEdgeGraph G).degree x = 1 ∨
      (triangleFreeEdgeGraph G).degree x = 3 := by
    rw [← (triangleFreeEdgeGraph G).card_neighborFinset_eq_degree,
      triangleFreeEdgeGraph_neighborFinset]
    exact excessThree_triangleFreeNeighbors_card_eq_one_or_three_of_odd
      G hfree hd hodd hreg hcard x
  rcases hTdeg with hx | hx
  · left
    exact ⟨hx, by omega⟩
  · right
    exact ⟨hx, by omega⟩

/-- **Signed row imbalance.**  Let `ℓ(x)` count the neighbors of `x` in the
triangle-free-degree-one sector.  A low-sector row has signed sum
`2(ℓ(x)-d)`, while a high-sector row has signed sum `2ℓ(x)`. -/
theorem excessThree_antipodal_commutator_row_sum
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) {d : ℕ} (hd : 7 ≤ d) (hodd : Odd d)
    (hreg : ∀ z, G.degree z = d)
    (hcard : Fintype.card V = d * (d - 1) + 6) (x : V) :
    let A := G.adjMatrix ℤ
    let C := (antipodalGraph G).adjMatrix ℤ
    let ℓ := ((G.neighborFinset x).filter fun z =>
      (triangleFreeEdgeGraph G).degree z = 1).card
    ((triangleFreeEdgeGraph G).degree x = 1 ∧
        ∑ y, (A * C - C * A) x y = 2 * ((ℓ : ℤ) - d)) ∨
      ((triangleFreeEdgeGraph G).degree x = 3 ∧
        ∑ y, (A * C - C * A) x y = 2 * (ℓ : ℤ)) := by
  dsimp only
  let T := triangleFreeEdgeGraph G
  let Cg := antipodalGraph G
  let ℓ := ((G.neighborFinset x).filter fun z => T.degree z = 1).card
  have hCform : ∀ z : V, (Cg.degree z : ℤ) =
      2 + 2 * (if T.degree z = 1 then 1 else 0) := by
    intro z
    rcases excessThree_antipodal_degree_eq_four_or_two
        G hfree hd hodd hreg hcard z with hz | hz
    · simp [T, Cg, hz.1, hz.2]
    · simp [T, Cg, hz.1, hz.2]
  have hsum : (∑ z ∈ G.neighborFinset x, (Cg.degree z : ℤ)) =
      2 * (d : ℤ) + 2 * (ℓ : ℤ) := by
    calc
      (∑ z ∈ G.neighborFinset x, (Cg.degree z : ℤ)) =
          ∑ z ∈ G.neighborFinset x,
            (2 + 2 * (if T.degree z = 1 then 1 else 0) : ℤ) := by
        apply Finset.sum_congr rfl
        intro z _
        rw [hCform]
      _ = 2 * (d : ℤ) + 2 * (ℓ : ℤ) := by
        dsimp [ℓ]
        rw [Finset.sum_add_distrib]
        simp only [Finset.sum_const, nsmul_eq_mul]
        rw [G.card_neighborFinset_eq_degree, hreg x]
        push_cast
        rw [← Finset.mul_sum]
        rw [Finset.sum_boole]
        push_cast
        ring
  have hrow := sum_adjMatrix_commutator_row_eq_neighborDegreeSum_sub
    G Cg hreg x
  rw [hsum] at hrow
  rcases excessThree_antipodal_degree_eq_four_or_two
      G hfree hd hodd hreg hcard x with hx | hx
  · left
    refine ⟨hx.1, ?_⟩
    change ∑ y, (G.adjMatrix ℤ * Cg.adjMatrix ℤ -
      Cg.adjMatrix ℤ * G.adjMatrix ℤ) x y = _
    rw [hrow, hx.2]
    ring
  · right
    refine ⟨hx.1, ?_⟩
    change ∑ y, (G.adjMatrix ℤ * Cg.adjMatrix ℤ -
      Cg.adjMatrix ℤ * G.adjMatrix ℤ) x y = _
    rw [hrow, hx.2]
    ring

/-- **Per-row support lower bound.**  The signed imbalance forces at least
twice the number of cross-sector ambient neighbors into the commutator
support of every row. -/
theorem excessThree_antipodal_commutator_row_support_lower
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) {d : ℕ} (hd : 7 ≤ d) (hodd : Odd d)
    (hreg : ∀ z, G.degree z = d)
    (hcard : Fintype.card V = d * (d - 1) + 6) (x : V) :
    let A := G.adjMatrix ℤ
    let C := (antipodalGraph G).adjMatrix ℤ
    let ℓ := ((G.neighborFinset x).filter fun z =>
      (triangleFreeEdgeGraph G).degree z = 1).card
    ((triangleFreeEdgeGraph G).degree x = 1 ∧
        2 * ((d : ℤ) - ℓ) ≤
          ((Finset.univ.filter fun y =>
            (A * C - C * A) x y ≠ 0).card : ℤ)) ∨
      ((triangleFreeEdgeGraph G).degree x = 3 ∧
        2 * (ℓ : ℤ) ≤
          ((Finset.univ.filter fun y =>
            (A * C - C * A) x y ≠ 0).card : ℤ)) := by
  dsimp only
  let A := G.adjMatrix ℤ
  let C := (antipodalGraph G).adjMatrix ℤ
  let ℓ := ((G.neighborFinset x).filter fun z =>
    (triangleFreeEdgeGraph G).degree z = 1).card
  have habs := abs_sum_le_card_support_of_mem_neg_one_zero_one
    (fun y => (A * C - C * A) x y) (fun y =>
      antipodal_commutator_entry_mem_neg_one_zero_one_all
        G hfree hreg x y)
  have hℓ : ℓ ≤ d := by
    dsimp [ℓ]
    calc
      ((G.neighborFinset x).filter fun z =>
          (triangleFreeEdgeGraph G).degree z = 1).card ≤
          (G.neighborFinset x).card := Finset.card_filter_le _ _
      _ = G.degree x := G.card_neighborFinset_eq_degree x
      _ = d := hreg x
  rcases excessThree_antipodal_commutator_row_sum
      G hfree hd hodd hreg hcard x with hx | hx
  · left
    refine ⟨hx.1, ?_⟩
    rw [hx.2, abs_of_nonpos (by push_cast; omega)] at habs
    dsimp [A, C, ℓ] at habs ⊢
    omega
  · right
    refine ⟨hx.1, ?_⟩
    rw [hx.2, abs_of_nonneg (by positivity)] at habs
    dsimp [A, C, ℓ] at habs ⊢
    exact habs

end

end Erdos85
