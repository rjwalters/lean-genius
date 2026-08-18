import Proofs.Erdos85BinarySquareCenteredGlobalRank
import Proofs.Erdos85BinarySquareCenteredOwnerTrace
import Proofs.Erdos85BinarySquareUnitOwnerRank

/-! # Exact rank of every centered owner sector -/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- The row Gram of a centered component-incidence block is the corresponding
centered owner Gram, up to the positive scalar `q`.  This is the missing bridge
between the exact rectangular incidence rank and the owner-sector algebra. -/
theorem centeredDefectComponentNeighborIncidenceMatrix_mul_transpose_eq_centeredOwnerGram
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) {q : ℕ} (hq : 3 ≤ q)
    (hreg : ∀ x, G.degree x = q)
    (hcard : Fintype.card V = q * q)
    (c : (secondOrderDefectGraph G).ConnectedComponent) {m_c : ℕ}
    (hc : c.supp.ncard = q * m_c) :
    centeredDefectComponentNeighborIncidenceMatrix G q c *
        (centeredDefectComponentNeighborIncidenceMatrix G q c).transpose =
      (q : ℤ) •
        ((q : ℤ) •
            ((componentOwnerGraph G (secondOrderDefectGraph G) c).adjMatrix ℤ +
              (m_c : ℤ) • (1 : Matrix V V ℤ)) -
          (m_c : ℤ) • FriendshipTheoremOQ01.onesMatrix V) := by
  let D := secondOrderDefectGraph G
  let I := defectComponentNeighborIncidenceMatrix (K := ℤ) G c
  let R := rectangularOnesMatrix V c.supp ℤ
  let O := componentOwnerGraph G D c
  let J := FriendshipTheoremOQ01.onesMatrix V
  have hIIt : I * I.transpose = O.adjMatrix ℤ +
      (m_c : ℤ) • (1 : Matrix V V ℤ) := by
    have howner := binarySquare_regular_componentOwnerGraph_adjMatrix_eq
      G hfree hq hreg hcard c hc
    have hgram : I * I.transpose =
        G.adjMatrix ℤ * defectComponentDiagonalMatrix D c * G.adjMatrix ℤ := by
      ext x y
      rw [Matrix.mul_apply,
        adjMatrix_mul_defectComponentDiagonalMatrix_mul_adjMatrix_apply]
      simp only [I, Matrix.transpose_apply,
        defectComponentNeighborIncidenceMatrix, ite_mul, one_mul, zero_mul]
      calc
        (∑ z : c.supp,
            if G.Adj x z.1 then if G.Adj y z.1 then (1 : ℤ) else 0 else 0) =
            ∑ z ∈ (Finset.univ : Finset V).filter
              (fun z => D.connectedComponentMk z = c),
                if G.Adj x z then if G.Adj y z then (1 : ℤ) else 0 else 0 := by
          symm
          apply Finset.sum_subtype
          intro z
          simp [D, SimpleGraph.ConnectedComponent.mem_supp_iff]
        _ = ((componentNeighborFinset G D c x ∩
              componentNeighborFinset G D c y).card : ℤ) := by
          rw [Finset.sum_filter]
          have hcollapse (z : V) :
              (if D.connectedComponentMk z = c then
                  if G.Adj x z then if G.Adj y z then (1 : ℤ) else 0 else 0
                else 0) =
                if D.connectedComponentMk z = c ∧ G.Adj x z ∧ G.Adj y z
                  then 1 else 0 := by
            by_cases hc' : D.connectedComponentMk z = c <;>
              by_cases hx : G.Adj x z <;> by_cases hy : G.Adj y z <;>
                simp [hc', hx, hy]
          simp_rw [hcollapse]
          rw [Finset.sum_boole]
          have hfilter : (Finset.univ : Finset V).filter
              (fun z => D.connectedComponentMk z = c ∧
                (G.Adj x z ∧ G.Adj y z)) =
              componentNeighborFinset G D c x ∩
                componentNeighborFinset G D c y := by
            dsimp only [D]
            ext z
            simp only [Finset.mem_filter, Finset.mem_univ, true_and,
              Finset.mem_inter, componentNeighborFinset,
              SimpleGraph.mem_neighborFinset]
            constructor
            · rintro ⟨hzc, hxz, hyz⟩
              exact ⟨⟨hxz, hzc⟩, hyz, hzc⟩
            · rintro ⟨⟨hxz, hzc⟩, hyz, _⟩
              exact ⟨hzc, hxz, hyz⟩
          rw [hfilter]
    dsimp only [D, O] at hgram ⊢
    rw [hgram, howner]
    module
  have hcardNeighbor (x : V) :
      (componentNeighborFinset G D c x).card = m_c := by
    have hmul := binarySquare_regular_mul_componentNeighborCard_eq_componentCard
      G hfree hq hreg hcard (D.connectedComponentMk x) c (x := x) rfl
    rw [hc] at hmul
    exact Nat.eq_of_mul_eq_mul_left (by omega : 0 < q) hmul
  have hIRt : I * R.transpose = (m_c : ℤ) • J := by
    ext x y
    rw [Matrix.mul_apply]
    simp only [I, R, J, Matrix.transpose_apply,
      defectComponentNeighborIncidenceMatrix, rectangularOnesMatrix,
      FriendshipTheoremOQ01.onesMatrix, Matrix.of_apply, mul_one,
      Matrix.smul_apply, smul_eq_mul]
    calc
      (∑ z : c.supp, if G.Adj x z.1 then (1 : ℤ) else 0) =
          ∑ z ∈ (Finset.univ : Finset V).filter
            (fun z => D.connectedComponentMk z = c),
              if G.Adj x z then (1 : ℤ) else 0 := by
        symm
        apply Finset.sum_subtype
        intro z
        simp [D, SimpleGraph.ConnectedComponent.mem_supp_iff]
      _ = ((componentNeighborFinset G D c x).card : ℤ) := by
        rw [Finset.sum_filter]
        have hcollapse (z : V) :
            (if D.connectedComponentMk z = c then
                if G.Adj x z then (1 : ℤ) else 0 else 0) =
              if D.connectedComponentMk z = c ∧ G.Adj x z then 1 else 0 := by
          by_cases hc' : D.connectedComponentMk z = c <;>
            by_cases hx : G.Adj x z <;> simp [hc', hx]
        simp_rw [hcollapse]
        rw [Finset.sum_boole]
        have hfilter : (Finset.univ : Finset V).filter
            (fun z => D.connectedComponentMk z = c ∧ G.Adj x z) =
            componentNeighborFinset G D c x := by
          ext z
          simp [componentNeighborFinset, SimpleGraph.mem_neighborFinset,
            and_comm]
        rw [hfilter]
      _ = m_c := by rw [hcardNeighbor]
  have hRIt : R * I.transpose = (m_c : ℤ) • J := by
    have ht := congrArg Matrix.transpose hIRt
    have hJt : J.transpose = J := by ext x y; rfl
    simpa only [Matrix.transpose_mul, Matrix.transpose_transpose,
      Matrix.transpose_smul, hJt]
      using ht
  have hRRt : R * R.transpose = ((q * m_c : ℕ) : ℤ) • J := by
    ext x y
    rw [Matrix.mul_apply]
    simp only [R, J, Matrix.transpose_apply, rectangularOnesMatrix,
      FriendshipTheoremOQ01.onesMatrix, Matrix.of_apply, mul_one,
      Matrix.smul_apply, smul_eq_mul]
    rw [Finset.sum_const, nsmul_eq_mul]
    rw [Finset.card_univ, mul_one]
    change ((Fintype.card c.supp : ℕ) : ℤ) = ((q * m_c : ℕ) : ℤ)
    rw [Set.fintypeCard_eq_ncard, hc]
  change ((q : ℤ) • I - R) * ((q : ℤ) • I - R).transpose = _
  rw [Matrix.transpose_sub, Matrix.transpose_smul]
  simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.smul_mul,
    Matrix.mul_smul, smul_sub, smul_smul]
  rw [hIIt, hIRt, hRIt, hRRt]
  push_cast
  module

/-- **Exact centered-owner rank.**  A component of order `q m_c` contributes
an owner sector of rank exactly `q m_c - 1`; its only missing incidence
direction is the constant vector on that defect component. -/
theorem binarySquare_regular_real_centeredOwnerGram_rank
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) {q : ℕ} (hq : 3 ≤ q)
    (hreg : ∀ x, G.degree x = q)
    (hcard : Fintype.card V = q * q)
    (c : (secondOrderDefectGraph G).ConnectedComponent) {m_c : ℕ}
    (hc : c.supp.ncard = q * m_c) :
    (((q : ℤ) •
          ((componentOwnerGraph G (secondOrderDefectGraph G) c).adjMatrix ℤ +
            (m_c : ℤ) • (1 : Matrix V V ℤ)) -
        (m_c : ℤ) • FriendshipTheoremOQ01.onesMatrix V).map
          (Int.castRingHom ℝ)).rank = q * m_c - 1 := by
  let B := realCenteredDefectComponentNeighborIncidenceMatrix G q c
  let CZ : Matrix V V ℤ := ((q : ℤ) •
          ((componentOwnerGraph G (secondOrderDefectGraph G) c).adjMatrix ℤ +
            (m_c : ℤ) • (1 : Matrix V V ℤ)) -
        (m_c : ℤ) • FriendshipTheoremOQ01.onesMatrix V)
  let C := CZ.map (Int.castRingHom ℝ)
  have hz := centeredDefectComponentNeighborIncidenceMatrix_mul_transpose_eq_centeredOwnerGram
    G hfree hq hreg hcard c hc
  have hr := congrArg (fun M : Matrix V V ℤ => M.map (Int.castRingHom ℝ)) hz
  have hgram : B * B.transpose = (q : ℝ) • C := by
    have hleft :
        (centeredDefectComponentNeighborIncidenceMatrix G q c *
          (centeredDefectComponentNeighborIncidenceMatrix G q c).transpose).map
            (Int.castRingHom ℝ) = B * B.transpose := by
      rw [Matrix.map_mul, Matrix.transpose_map]
      rfl
    have hright :
        ((q : ℤ) • CZ).map (Int.castRingHom ℝ) = (q : ℝ) • C := by
      ext x y
      change (((q : ℤ) * CZ x y : ℤ) : ℝ) =
        (q : ℝ) * ((CZ x y : ℤ) : ℝ)
      norm_num
    exact hleft.symm.trans (hr.trans hright)
  have hq0 : (q : ℝ) ≠ 0 := by positivity
  calc
    C.rank = ((q : ℝ) • C).rank := by
      exact (rank_smul_real_of_ne_zero C (q : ℝ) hq0).symm
    _ = (B * B.transpose).rank := by rw [hgram]
    _ = B.rank := Matrix.rank_self_mul_transpose B
    _ = Fintype.card c.supp - 1 :=
      realCenteredDefectComponentNeighborIncidenceMatrix_rank
        G hfree hq hreg hcard c
    _ = q * m_c - 1 := by rw [Set.fintypeCard_eq_ncard, hc]

/-- The mutually annihilating centered owner sectors saturate the full
nonconstant component-incidence dimension: their ranks sum to `q²` minus the
number of defect components. -/
theorem binarySquare_regular_sum_real_centeredOwnerGram_rank
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) {q : ℕ} (hq : 3 ≤ q)
    (hreg : ∀ x, G.degree x = q)
    (hcard : Fintype.card V = q * q)
    (m : (secondOrderDefectGraph G).ConnectedComponent → ℕ)
    (hm : ∀ c, c.supp.ncard = q * m c) :
    (∑ c : (secondOrderDefectGraph G).ConnectedComponent,
      (((q : ℤ) •
            ((componentOwnerGraph G (secondOrderDefectGraph G) c).adjMatrix ℤ +
              (m c : ℤ) • (1 : Matrix V V ℤ)) -
          (m c : ℤ) • FriendshipTheoremOQ01.onesMatrix V).map
            (Int.castRingHom ℝ)).rank) =
      q * q - Fintype.card
        (secondOrderDefectGraph G).ConnectedComponent := by
  calc
    _ = ∑ c : (secondOrderDefectGraph G).ConnectedComponent,
        (realCenteredDefectComponentNeighborIncidenceMatrix G q c).rank := by
      apply Finset.sum_congr rfl
      intro c _
      rw [binarySquare_regular_real_centeredOwnerGram_rank
        G hfree hq hreg hcard c (hm c),
        realCenteredDefectComponentNeighborIncidenceMatrix_rank
          G hfree hq hreg hcard c,
        Set.fintypeCard_eq_ncard, hm c]
    _ = q * q - Fintype.card
        (secondOrderDefectGraph G).ConnectedComponent :=
      sum_realCenteredDefectComponentNeighborIncidenceMatrix_rank
        G hfree hq hreg hcard

end

end Erdos85
