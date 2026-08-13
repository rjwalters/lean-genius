import Proofs.Erdos85OrderFortyNineOneHighOverlap
import Proofs.Erdos85OneHighDeterminantReduction

/-!
# The reduced one-high defect matrix

After deleting the isolated high vertex from the second-order defect graph,
the determinant reduction uses `H = 6I - D'` and the vector which is `6` on
the eight centers and `7` on the forty leaves.  This file begins the exact
graph-to-block-matrix wiring.
-/

open SimpleGraph

namespace Erdos85

noncomputable section

abbrev oneHighReducedVertex {V : Type*} (v : V) := {z : V // z ≠ v}

def oneHighResolventWeight {V : Type*} [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (v : V) : oneHighReducedVertex v → ℚ :=
  fun z => if G.Adj v z.1 then 6 else 7

noncomputable def oneHighReducedDefectMatrix
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (v : V) : Matrix (oneHighReducedVertex v) (oneHighReducedVertex v) ℚ :=
  (6 : ℚ) • 1 - ((secondOrderDefectGraph G).adjMatrix ℚ).submatrix
    Subtype.val Subtype.val

def oneHighSplitEquiv {V : Type*} [DecidableEq V] (v : V) :
    V ≃ Unit ⊕ oneHighReducedVertex v where
  toFun x := if h : x = v then Sum.inl () else Sum.inr ⟨x, h⟩
  invFun
    | Sum.inl _ => v
    | Sum.inr x => x.1
  left_inv x := by
    by_cases h : x = v
    · simp [h]
    · simp [h]
  right_inv x := by
    rcases x with u | x
    · rcases u with ⟨⟩
      simp
    · simp [x.2]

theorem sum_oneHighResolventWeight_eq_328
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hcard : Fintype.card V = 49) {v : V} (hv : G.degree v = 8) :
    ∑ z : oneHighReducedVertex v, oneHighResolventWeight G v z = 328 := by
  classical
  rw [show (∑ z : oneHighReducedVertex v, oneHighResolventWeight G v z) =
      6 * (Finset.univ.filter fun z : oneHighReducedVertex v => G.Adj v z.1).card +
      7 * (Finset.univ.filter fun z : oneHighReducedVertex v => ¬ G.Adj v z.1).card by
    simp only [oneHighResolventWeight]
    rw [← Finset.sum_filter_add_sum_filter_not
      (s := Finset.univ) (p := fun z : oneHighReducedVertex v => G.Adj v z.1)]
    have hpos :
        (∑ z ∈ (Finset.univ.filter fun z : oneHighReducedVertex v => G.Adj v z.1),
          if G.Adj v z.1 then (6 : ℚ) else 7) =
          6 * (Finset.univ.filter fun z : oneHighReducedVertex v => G.Adj v z.1).card := by
      calc
        _ = ∑ _z ∈ (Finset.univ.filter fun z : oneHighReducedVertex v => G.Adj v z.1),
            (6 : ℚ) := by
          apply Finset.sum_congr rfl
          intro z hz
          simp [(Finset.mem_filter.mp hz).2]
        _ = _ := by simp [mul_comm]
    have hneg :
        (∑ z ∈ (Finset.univ.filter fun z : oneHighReducedVertex v => ¬ G.Adj v z.1),
          if G.Adj v z.1 then (6 : ℚ) else 7) =
          7 * (Finset.univ.filter fun z : oneHighReducedVertex v => ¬ G.Adj v z.1).card := by
      calc
        _ = ∑ _z ∈ (Finset.univ.filter fun z : oneHighReducedVertex v => ¬ G.Adj v z.1),
            (7 : ℚ) := by
          apply Finset.sum_congr rfl
          intro z hz
          simp [(Finset.mem_filter.mp hz).2]
        _ = _ := by simp [mul_comm]
    exact congrArg₂ (· + ·) hpos hneg]
  have hadjcard :
      (Finset.univ.filter fun z : oneHighReducedVertex v => G.Adj v z.1).card = 8 := by
    rw [← hv, ← G.card_neighborFinset_eq_degree]
    apply Finset.card_bij (fun z _ => z.1)
    · intro z hz
      simpa [SimpleGraph.mem_neighborFinset] using (Finset.mem_filter.mp hz).2
    · intro a ha b hb hab
      exact Subtype.ext hab
    · intro y hy
      have hyv : y ≠ v := by
        intro h
        subst y
        exact G.loopless.irrefl v ((G.mem_neighborFinset v v).mp hy)
      refine ⟨⟨y, hyv⟩, by simp [(G.mem_neighborFinset v y).mp hy], rfl⟩
  have htotal : Fintype.card (oneHighReducedVertex v) = 48 := by
    simp [oneHighReducedVertex, hcard]
  have hnotcard :
      (Finset.univ.filter fun z : oneHighReducedVertex v => ¬ G.Adj v z.1).card = 40 := by
    have hpartition := Finset.card_filter_add_card_filter_not
      (s := (Finset.univ : Finset (oneHighReducedVertex v)))
      (p := fun z : oneHighReducedVertex v => G.Adj v z.1)
    rw [hadjcard, Finset.card_univ, htotal] at hpartition
    omega
  rw [hadjcard, hnotcard]
  norm_num

theorem sum_oneHighResolventWeight_over_defectNeighbors
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G)
    (hmin : ∀ x : V, 7 ≤ G.degree x)
    (hcard : Fintype.card V = 49)
    (hHigh : (orderFortyNineHighVertices G).card = 1)
    {v z : V} (hv : G.degree v = 8) (hzv : z ≠ v) :
    (∑ y ∈ (secondOrderDefectGraph G).neighborFinset z,
      if G.Adj v y then (6 : ℚ) else 7) =
        if G.Adj v z then 35 else 41 := by
  classical
  let D := secondOrderDefectGraph G
  have hvHigh : v ∈ orderFortyNineHighVertices G := by
    simp [orderFortyNineHighVertices, hv]
  obtain ⟨u, hu⟩ := Finset.card_eq_one.mp hHigh
  have hvu : v = u := by simpa [hu] using hvHigh
  have hzdeg : G.degree z = 7 := by
    rcases orderFortyNine_degree_eq_seven_or_eight
        G hfree hmin hcard z with hz7 | hz8
    · exact hz7
    · have hzHigh : z ∈ orderFortyNineHighVertices G := by
        simp [orderFortyNineHighVertices, hz8]
      have hzu : z = u := by simpa [hu] using hzHigh
      exact (hzv (hzu.trans hvu.symm)).elim
  have hinter :
      (D.neighborFinset z).filter (fun y => G.Adj v y) =
        G.neighborFinset v ∩ D.neighborFinset z := by
    ext y
    simp [D, SimpleGraph.mem_neighborFinset, and_comm]
  have hinterCard :
      ((D.neighborFinset z).filter fun y => G.Adj v y).card =
        if G.Adj v z then 0 else 1 := by
    rw [hinter]
    exact orderFortyNine_card_highNeighbors_inter_defectNeighbors
      G hfree hmin hcard hv hzdeg
  have hDdegree : D.degree z = if G.Adj v z then 5 else 6 := by
    by_cases hvz : G.Adj v z
    · rw [if_pos hvz]
      have hzmem : z ∈ G.neighborFinset v := by
        simpa [SimpleGraph.mem_neighborFinset] using hvz
      have hclosed := orderFortyNine_card_closedDefectNeighborhood_eq_six_of_one_high
        G hfree hmin hcard hHigh hv hzmem
      have hznot : z ∉ D.neighborFinset z := by simp [D]
      rw [Finset.card_insert_of_notMem hznot,
        D.card_neighborFinset_eq_degree] at hclosed
      omega
    · rw [if_neg hvz]
      exact orderFortyNine_defectDegree_eq_six_of_one_high_of_not_adj
        G hfree hmin hcard hHigh hv hzdeg hvz
  rw [← Finset.sum_filter_add_sum_filter_not
    (s := D.neighborFinset z) (p := fun y => G.Adj v y)]
  have hpos :
      (∑ y ∈ (D.neighborFinset z).filter (fun y => G.Adj v y),
        if G.Adj v y then (6 : ℚ) else 7) =
      6 * ((D.neighborFinset z).filter fun y => G.Adj v y).card := by
    calc
      _ = ∑ _y ∈ (D.neighborFinset z).filter (fun y => G.Adj v y),
          (6 : ℚ) := by
        apply Finset.sum_congr rfl
        intro y hy
        simp [(Finset.mem_filter.mp hy).2]
      _ = _ := by simp [mul_comm]
  have hneg :
      (∑ y ∈ (D.neighborFinset z).filter (fun y => ¬ G.Adj v y),
        if G.Adj v y then (6 : ℚ) else 7) =
      7 * ((D.neighborFinset z).filter fun y => ¬ G.Adj v y).card := by
    calc
      _ = ∑ _y ∈ (D.neighborFinset z).filter (fun y => ¬ G.Adj v y),
          (7 : ℚ) := by
        apply Finset.sum_congr rfl
        intro y hy
        simp [(Finset.mem_filter.mp hy).2]
      _ = _ := by simp [mul_comm]
  rw [hpos, hneg]
  have hpartition := Finset.card_filter_add_card_filter_not
    (s := D.neighborFinset z) (p := fun y => G.Adj v y)
  rw [hinterCard, D.card_neighborFinset_eq_degree, hDdegree] at hpartition
  by_cases hvz : G.Adj v z
  · rw [if_pos hvz] at hinterCard hDdegree hpartition ⊢
    simp only [hvz, if_true] at hpartition
    have hnegcard :
        ((D.neighborFinset z).filter fun y => ¬ G.Adj v y).card = 5 := by omega
    rw [hinterCard, hnegcard]
    norm_num
  · rw [if_neg hvz] at hinterCard hDdegree hpartition ⊢
    simp only [hvz, if_false] at hpartition
    have hnegcard :
        ((D.neighborFinset z).filter fun y => ¬ G.Adj v y).card = 5 := by omega
    rw [hinterCard, hnegcard]
    norm_num

theorem oneHighReducedDefectMatrix_mulVec_resolventWeight
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G)
    (hmin : ∀ x : V, 7 ≤ G.degree x)
    (hcard : Fintype.card V = 49)
    (hHigh : (orderFortyNineHighVertices G).card = 1)
    {v : V} (hv : G.degree v = 8) :
    (oneHighReducedDefectMatrix G v).mulVec
      (oneHighResolventWeight G v) = 1 := by
  classical
  funext z
  simp only [oneHighReducedDefectMatrix, Matrix.sub_mulVec,
    Matrix.smul_mulVec, Matrix.one_mulVec, Pi.sub_apply, Pi.smul_apply,
    Pi.one_apply, smul_eq_mul]
  let D := secondOrderDefectGraph G
  let W : V → ℚ := fun y => if y = v then 0 else if G.Adj v y then 6 else 7
  have hvDzero : D.degree v = 0 :=
    (orderFortyNine_degreeEight_defectDegree_and_neighborExcess_zero
      G hfree hmin hcard hv).1
  have hvDempty : D.neighborFinset v = ∅ := by
    rw [← Finset.card_eq_zero, D.card_neighborFinset_eq_degree, hvDzero]
  have hvDnot : ∀ x : V, ¬ D.Adj v x := by
    intro x hvx
    have hxmem : x ∈ D.neighborFinset v := (D.mem_neighborFinset v x).mpr hvx
    rw [hvDempty] at hxmem
    exact Finset.notMem_empty x hxmem
  have hsub :
      ((D.adjMatrix ℚ).submatrix Subtype.val Subtype.val).mulVec
      (oneHighResolventWeight G v) z =
      (D.adjMatrix ℚ).mulVec W z.1 := by
    simp [Matrix.mulVec, dotProduct, Matrix.submatrix_apply, W,
      oneHighResolventWeight, SimpleGraph.adjMatrix_apply]
    let f : V → ℚ := fun x =>
      if x = v then 0
      else if G.Adj v x then if D.Adj z.1 x then 6 else 0
      else if D.Adj z.1 x then 7 else 0
    have hall := Fintype.sum_subtype_add_sum_subtype
      (fun x : V => x ≠ v) f
    have hcomp : (∑ x : {x : V // ¬ x ≠ v}, f x.1) = 0 := by
      apply Finset.sum_eq_zero
      intro x _hx
      have hxv : x.1 = v := not_ne_iff.mp x.2
      simp [f, hxv]
    rw [hcomp, add_zero] at hall
    rw [← hall]
    apply Finset.sum_congr rfl
    intro x _hx
    simp [f, x.2]
  rw [hsub, SimpleGraph.adjMatrix_mulVec_apply]
  have hsum := sum_oneHighResolventWeight_over_defectNeighbors
    G hfree hmin hcard hHigh hv z.2
  simp only [W]
  rw [show (∑ y ∈ D.neighborFinset z.1,
      if y = v then (0 : ℚ) else if G.Adj v y then 6 else 7) =
      ∑ y ∈ D.neighborFinset z.1, if G.Adj v y then 6 else 7 by
    apply Finset.sum_congr rfl
    intro y hy
    have hyv : y ≠ v := by
      intro hyv
      subst y
      have hzvD : D.Adj z.1 v := (D.mem_neighborFinset z.1 v).mp hy
      have hvzD : D.Adj v z.1 := (D.adj_comm z.1 v).mp hzvD
      have : z.1 ∈ D.neighborFinset v := (D.mem_neighborFinset v z.1).mpr hvzD
      rw [hvDempty] at this
      exact Finset.notMem_empty _ this
    rw [if_neg hyv]]
  rw [hsum]
  by_cases hvz : G.Adj v z.1 <;>
    simp [oneHighResolventWeight, hvz] <;> norm_num

theorem oneHighSquareCandidate_reindex_eq_fromBlocks
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G)
    (hmin : ∀ x : V, 7 ≤ G.degree x)
    (hcard : Fintype.card V = 49)
    (hHigh : (orderFortyNineHighVertices G).card = 1)
    {v : V} (hv : G.degree v = 8) :
    ((Int.castRingHom ℚ).mapMatrix (orderFortyNineSquareCandidate G)).submatrix
      (oneHighSplitEquiv v).symm (oneHighSplitEquiv v).symm =
      Matrix.fromBlocks
        (fun _ : Unit => fun _ : Unit => (8 : ℚ))
        (fun _ : Unit => fun _ : oneHighReducedVertex v => (1 : ℚ))
        (fun _ : oneHighReducedVertex v => fun _ : Unit => (1 : ℚ))
        (oneHighReducedDefectMatrix G v +
          Matrix.vecMulVec (fun _ : oneHighReducedVertex v => (1 : ℚ))
            (fun _ : oneHighReducedVertex v => (1 : ℚ))) := by
  classical
  let D := secondOrderDefectGraph G
  have hvDzero : D.degree v = 0 :=
    (orderFortyNine_degreeEight_defectDegree_and_neighborExcess_zero
      G hfree hmin hcard hv).1
  have hvDempty : D.neighborFinset v = ∅ := by
    rw [← Finset.card_eq_zero, D.card_neighborFinset_eq_degree, hvDzero]
  have hvDnot_block : ∀ x : V, ¬ D.Adj v x := by
    intro x hvx
    have hxmem : x ∈ D.neighborFinset v := (D.mem_neighborFinset v x).mpr hvx
    rw [hvDempty] at hxmem
    exact Finset.notMem_empty x hxmem
  have hvHigh : v ∈ orderFortyNineHighVertices G := by
    simp [orderFortyNineHighVertices, hv]
  obtain ⟨u, hu⟩ := Finset.card_eq_one.mp hHigh
  have hvu : v = u := by simpa [hu] using hvHigh
  have hnotHigh : ∀ z : oneHighReducedVertex v,
      z.1 ∉ orderFortyNineHighVertices G := by
    intro z hz
    have hzu : z.1 = u := by simpa [hu] using hz
    exact z.2 (hzu.trans hvu.symm)
  ext i j
  rcases i with i | i <;> rcases j with j | j
  · rcases i with ⟨⟩
    rcases j with ⟨⟩
    simp [oneHighSplitEquiv, orderFortyNineSquareCandidate,
      orderFortyNineHighDiagonal, FriendshipTheoremOQ01.onesMatrix,
      SimpleGraph.adjMatrix_apply, D, Matrix.map_apply, Matrix.smul_apply,
      Matrix.one_apply, Matrix.diagonal_apply, Pi.smul_apply, smul_eq_mul,
      Matrix.ofNat_apply, hvHigh]
  · rcases i with ⟨⟩
    simp [oneHighSplitEquiv, orderFortyNineSquareCandidate,
      orderFortyNineHighDiagonal, FriendshipTheoremOQ01.onesMatrix,
      SimpleGraph.adjMatrix_apply, D, Matrix.map_apply, Matrix.smul_apply,
      Matrix.one_apply, Matrix.diagonal_apply, Pi.smul_apply, smul_eq_mul,
      Matrix.ofNat_apply, j.2, Ne.symm j.2, hvDnot_block]
  · rcases j with ⟨⟩
    simp [oneHighSplitEquiv, orderFortyNineSquareCandidate,
      orderFortyNineHighDiagonal, FriendshipTheoremOQ01.onesMatrix,
      SimpleGraph.adjMatrix_apply, D, Matrix.map_apply, Matrix.smul_apply,
      Matrix.one_apply, Matrix.diagonal_apply, Pi.smul_apply, smul_eq_mul,
      Matrix.ofNat_apply, i.2, hvDnot_block,
      (D.adj_comm i.1 v)]
  · simp [oneHighSplitEquiv, orderFortyNineSquareCandidate,
      oneHighReducedDefectMatrix, orderFortyNineHighDiagonal,
      FriendshipTheoremOQ01.onesMatrix, SimpleGraph.adjMatrix_apply,
      D, Matrix.map_apply, Matrix.vecMulVec, Matrix.smul_apply,
      Matrix.one_apply, Matrix.diagonal_apply, Pi.smul_apply, smul_eq_mul,
      Matrix.ofNat_apply, hnotHigh]
    by_cases hij : i = j
    · subst j
      simp [hnotHigh]
    · have hijv : i.1 ≠ j.1 := fun h => hij (Subtype.ext h)
      simp [hij, hijv]
      ring

/-- In the one-high stratum, the determinant of the reduced defect matrix
`6I - D'` is a rational square.  This is the graph-facing form of the
square-candidate obstruction. -/
theorem orderFortyNine_reducedDefectMatrix_det_isSquare_of_one_high
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G)
    (hmin : ∀ x : V, 7 ≤ G.degree x)
    (hcard : Fintype.card V = 49)
    (hHigh : (orderFortyNineHighVertices G).card = 1)
    {v : V} (hv : G.degree v = 8) :
    IsSquare (oneHighReducedDefectMatrix G v).det := by
  classical
  let H := oneHighReducedDefectMatrix G v
  by_cases hHdet : H.det = 0
  · refine ⟨0, ?_⟩
    change H.det = 0 * 0
    simp [hHdet]
  obtain ⟨k, hk⟩ :=
    orderFortyNine_squareCandidate_det_eq_2304_mul_sq_of_one_high
      G hfree hmin hcard hHigh hv
  have hblock := det_oneHighBlock_eq_2304_mul_det H
    (oneHighResolventWeight G v)
    (oneHighReducedDefectMatrix_mulVec_resolventWeight
      G hfree hmin hcard hHigh hv)
    (sum_oneHighResolventWeight_eq_328 G hcard hv) hHdet
  have hreindex := congrArg Matrix.det
    (oneHighSquareCandidate_reindex_eq_fromBlocks
      G hfree hmin hcard hHigh hv)
  have hcandidate :
      ((Int.castRingHom ℚ).mapMatrix
        (orderFortyNineSquareCandidate G)).det = 2304 * H.det := by
    simpa [H] using hreindex.trans hblock
  have hcast :
      ((Int.castRingHom ℚ).mapMatrix
        (orderFortyNineSquareCandidate G)).det =
        2304 * (k : ℚ) ^ 2 := by
    rw [← (Int.castRingHom ℚ).map_det]
    calc
      ((orderFortyNineSquareCandidate G).det : ℚ) =
          ((2304 * k ^ 2 : ℤ) : ℚ) := congrArg (fun z : ℤ => (z : ℚ)) hk
      _ = 2304 * (k : ℚ) ^ 2 := by norm_num
  refine ⟨(k : ℚ), ?_⟩
  change H.det = (k : ℚ) * (k : ℚ)
  rw [pow_two] at hcast
  linarith

end


end Erdos85
