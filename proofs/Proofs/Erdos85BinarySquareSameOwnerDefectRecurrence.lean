import Proofs.Erdos85BinarySquareSameOwnerCenterGridCapacity
import Proofs.Erdos85BinarySquareCenteredOwnerResolution

/-! # Individual-owner recurrence on defect edges -/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- On a defect edge, one owner's same-color two-step middles and its
owner-then-defect two-step walks have the fixed total `m(m-1)`. -/
theorem binarySquare_regular_sameOwner_defectEdge_card_add_ownerDefect
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) {q : ℕ} (hq : 3 ≤ q)
    (hreg : ∀ x, G.degree x = q)
    (hcard : Fintype.card V = q * q)
    (m : (secondOrderDefectGraph G).ConnectedComponent → ℕ)
    (hm : ∀ c, c.supp.ncard = q * m c)
    (hsum : ∑ c, m c = q)
    (c : (secondOrderDefectGraph G).ConnectedComponent)
    {x y : V} (hxyD : (secondOrderDefectGraph G).Adj x y) :
    ((coloredTwoStepMiddles
      (componentOwnerGraph G (secondOrderDefectGraph G) c)
      (componentOwnerGraph G (secondOrderDefectGraph G) c) x y).card : ℤ) +
      (((componentOwnerGraph G
          (secondOrderDefectGraph G) c).adjMatrix ℤ *
        (secondOrderDefectGraph G).adjMatrix ℤ) x y) =
      (m c : ℤ) * ((m c : ℤ) - 1) := by
  let D := secondOrderDefectGraph G
  let O := componentOwnerGraph G D c
  let A := O.adjMatrix ℤ
  let E := D.adjMatrix ℤ
  let I : Matrix V V ℤ := 1
  let J := FriendshipTheoremOQ01.onesMatrix V
  let M := A + (m c : ℤ) • I
  let C := (q : ℤ) • M - (m c : ℤ) • J
  let R := (q : ℤ) • (((q - 1 : ℕ) : ℤ) • I - E)
  have hcensus : Fintype.card V = q * (q - 1) + 3 + (q - 3) := by
    rw [hcard]
    calc
      q * q = q * ((q - 1) + 1) := by
        rw [Nat.sub_add_cancel (by omega : 1 ≤ q)]
      _ = q * (q - 1) + q := by ring
      _ = q * (q - 1) + 3 + (q - 3) := by omega
  have hDreg : ∀ z, D.degree z = q - 1 := by
    intro z
    have h := secondOrderDefectGraph_degree_eq_excess_add_two
      G hfree hreg hcensus z
    change D.degree z = (q - 3) + 2 at h
    omega
  have hOreg : ∀ z, O.degree z = m c * (q - 1) :=
    binarySquare_regular_componentOwnerGraph_degree
      G hfree hq hreg hcard c (hm c)
  have hAJ : A * J = ((m c * (q - 1) : ℕ) : ℤ) • J := by
    simpa using FriendshipTheoremOQ01.adjMatrix_mul_ones O _ hOreg
  have hJA : J * A = ((m c * (q - 1) : ℕ) : ℤ) • J := by
    simpa using FriendshipTheoremOQ01.onesMatrix_mul_adjMatrix O _ hOreg
  have hEJ : E * J = (((q - 1 : ℕ) : ℤ)) • J := by
    simpa using FriendshipTheoremOQ01.adjMatrix_mul_ones D _ hDreg
  have hJE : J * E = (((q - 1 : ℕ) : ℤ)) • J := by
    simpa using FriendshipTheoremOQ01.onesMatrix_mul_adjMatrix D _ hDreg
  have hJJ : J * J = (Fintype.card V : ℤ) • J :=
    FriendshipTheoremOQ01.onesMatrix_sq
  have hqcast : (((q - 1 : ℕ) : ℤ)) = (q : ℤ) - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ q)]
    norm_num
  have hsel : C * R = C * C := by
    simpa [C, R, M, A, E, I, J, O, D] using
      (binarySquare_regular_centeredOwnerGram_mul_defectResolution
        G hfree hq hreg hcard m hm hsum c)
  have hJzero : J * (((q - 1 : ℕ) : ℤ) • I - E) = 0 := by
    rw [Matrix.mul_sub, Matrix.mul_smul, Matrix.mul_one, hJE, hqcast]
    module
  have hleft : C * R =
      ((q : ℤ) ^ 2) • (M * (((q - 1 : ℕ) : ℤ) • I - E)) := by
    dsimp [C, R]
    simp only [sub_mul, Matrix.smul_mul, Matrix.mul_smul, smul_smul]
    rw [hJzero, smul_zero, sub_zero]
    module
  have hright : C * C =
      ((q : ℤ) ^ 2) • (M * M - ((m c : ℤ) ^ 2) • J) := by
    have hMJ : M * J = (q * m c : ℕ) • J := by
      dsimp [M, I]
      rw [Matrix.add_mul, hAJ, Matrix.smul_mul, Matrix.one_mul]
      push_cast
      rw [hqcast]
      module
    have hJM : J * M = (q * m c : ℕ) • J := by
      dsimp [M, I]
      rw [Matrix.mul_add, hJA, Matrix.mul_smul, Matrix.mul_one]
      push_cast
      rw [hqcast]
      module
    dsimp [C]
    calc
      ((q : ℤ) • M - (m c : ℤ) • J) *
          ((q : ℤ) • M - (m c : ℤ) • J) =
          ((q : ℤ) ^ 2) • (M * M) -
            ((q : ℤ) * (m c : ℤ)) • (M * J) -
            ((q : ℤ) * (m c : ℤ)) • (J * M) +
            ((m c : ℤ) ^ 2) • (J * J) := by
        simp only [sub_mul, mul_sub, Matrix.smul_mul, Matrix.mul_smul, smul_smul]
        module
      _ = ((q : ℤ) ^ 2) •
          (M * M - ((m c : ℤ) ^ 2) • J) := by
        rw [hMJ, hJM, hJJ, hcard]
        push_cast
        module
  rw [hleft, hright] at hsel
  have hmatrix : M * (((q - 1 : ℕ) : ℤ) • I - E) =
      M * M - ((m c : ℤ) ^ 2) • J := by
    ext u v
    have huv := congrArg (fun N : Matrix V V ℤ => N u v) hsel
    simp only [Matrix.smul_apply, smul_eq_mul] at huv
    have hqne : (q : ℤ) ^ 2 ≠ 0 := pow_ne_zero 2 (by exact_mod_cast (show q ≠ 0 by omega))
    exact mul_left_cancel₀ hqne huv
  have hentry := congrArg (fun N : Matrix V V ℤ => N x y) hmatrix
  have hnotO : ¬ O.Adj x y := by
    exact fun h => (componentOwnerGraph_adj_not_secondOrderDefect_adj
      G hfree c h) hxyD
  have hxy : x ≠ y := hxyD.ne
  have hAxy : A x y = 0 := by simp [A, SimpleGraph.adjMatrix_apply, hnotO]
  have hxyD' : D.Adj x y := hxyD
  have hExy : E x y = 1 := by simp [E, SimpleGraph.adjMatrix_apply, hxyD']
  have hIxy : I x y = 0 := by simp [I, Matrix.one_apply, hxy]
  have hJxy : J x y = 1 := by simp [J, FriendshipTheoremOQ01.onesMatrix]
  have hA2 : (A * A) x y =
      ((coloredTwoStepMiddles O O x y).card : ℤ) :=
    mul_two_adjMatrices_apply_eq_card_coloredTwoStepMiddles O O x y
  have hMxy : M x y = 0 := by
    change (A + (m c : ℤ) • I) x y = 0
    rw [Matrix.add_apply, Matrix.smul_apply, hAxy, hIxy]
    ring
  have hME : (M * E) x y = (A * E) x y + (m c : ℤ) := by
    dsimp [M]
    rw [Matrix.add_mul, Matrix.add_apply, Matrix.smul_mul, Matrix.one_mul,
      Matrix.smul_apply, hExy]
    ring
  have hMM : (M * M) x y = (A * A) x y := by
    have hIA : I * A = A := by simp [I]
    have hAI : A * I = A := by simp [I]
    have hII : I * I = I := by simp [I]
    change ((A + (m c : ℤ) • I) * (A + (m c : ℤ) • I)) x y = _
    simp only [Matrix.add_mul, Matrix.mul_add, Matrix.mul_smul,
      Matrix.smul_mul, Matrix.add_apply, Matrix.smul_apply]
    rw [hIA, hAI, hII, hAxy, hIxy]
    ring_nf
  rw [Matrix.mul_sub, Matrix.mul_smul, Matrix.mul_one, Matrix.sub_apply,
    Matrix.smul_apply, hMxy, hME, Matrix.sub_apply, hMM,
    Matrix.smul_apply, hJxy, hA2] at hentry
  simp only [smul_eq_mul, mul_zero, mul_one, zero_sub] at hentry
  change ((coloredTwoStepMiddles O O x y).card : ℤ) +
      (A * E) x y = (m c : ℤ) * ((m c : ℤ) - 1)
  nlinarith

/-- Equivalent center-grid form: an owner's defect cells consist, in
cardinality, of its `m` diagonal contribution plus its owner-then-defect
two-step walks between the roots. -/
theorem binarySquare_regular_sameOwner_defectCenterPairs_card_eq_ownerDefect_add
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) {q : ℕ} (hq : 3 ≤ q)
    (hreg : ∀ x, G.degree x = q)
    (hcard : Fintype.card V = q * q)
    (m : (secondOrderDefectGraph G).ConnectedComponent → ℕ)
    (hm : ∀ c, c.supp.ncard = q * m c)
    (hsum : ∑ c, m c = q)
    (c : (secondOrderDefectGraph G).ConnectedComponent)
    {x y : V} (hxyD : (secondOrderDefectGraph G).Adj x y) :
    ((sameOwnerDefectCenterPairs G c x y).card : ℤ) =
      (((componentOwnerGraph G
          (secondOrderDefectGraph G) c).adjMatrix ℤ *
        (secondOrderDefectGraph G).adjMatrix ℤ) x y) + m c := by
  have hgrid :=
    binarySquare_regular_sameOwner_defectEdge_card_add_defectCells_eq_sq
      G hfree hq hreg hcard c (hm c) hxyD
  have hroute :=
    binarySquare_regular_sameOwner_defectEdge_card_add_ownerDefect
      G hfree hq hreg hcard m hm hsum c hxyD
  have hgridZ :
      ((coloredTwoStepMiddles
        (componentOwnerGraph G (secondOrderDefectGraph G) c)
        (componentOwnerGraph G (secondOrderDefectGraph G) c) x y).card : ℤ) +
      ((sameOwnerDefectCenterPairs G c x y).card : ℤ) =
        ((m c * m c : ℕ) : ℤ) := by
    exact_mod_cast hgrid
  push_cast at hgridZ
  nlinarith

/-- In a two-owner stratum, residue pressure recovers the pointwise bound
`(O_c D)_{xy} ≤ q-2` on a defect edge.  This corollary is useful as a checked
consistency test for the recurrence, but the inequality itself is elementary:
`N_D(y)` has `q-1` vertices, contains `x`, and looplessness excludes `x` from
`N_{O_c}(x)`. -/
theorem binarySquare_regular_twoComponents_defectEdge_ownerDefect_card_le
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) {q : ℕ} (hq : 3 ≤ q)
    (hreg : ∀ x, G.degree x = q)
    (hcard : Fintype.card V = q * q)
    (hcount : Fintype.card
      (secondOrderDefectGraph G).ConnectedComponent = 2)
    (m : (secondOrderDefectGraph G).ConnectedComponent → ℕ)
    (hm : ∀ c, c.supp.ncard = q * m c)
    (hsum : ∑ c, m c = q)
    (a b : (secondOrderDefectGraph G).ConnectedComponent) (hab : a ≠ b)
    {x y : V} (hxyD : (secondOrderDefectGraph G).Adj x y) :
    (coloredTwoStepMiddles
      (componentOwnerGraph G (secondOrderDefectGraph G) a)
      (secondOrderDefectGraph G) x y).card ≤ q - 2 := by
  let D := secondOrderDefectGraph G
  let A := componentOwnerGraph G D a
  let B := componentOwnerGraph G D b
  let AA := coloredTwoStepMiddles A A x y
  let BB := coloredTwoStepMiddles B B x y
  let AD := coloredTwoStepMiddles A D x y
  let BD := coloredTwoStepMiddles B D x y
  have huniv : (Finset.univ : Finset D.ConnectedComponent) = {a, b} := by
    ext c
    simp only [Finset.mem_univ, Finset.mem_insert, Finset.mem_singleton,
      true_iff]
    exact eq_or_eq_of_fintype_card_eq_two a b hab hcount c
  have habSum : m a + m b = q := by
    calc
      m a + m b = ∑ c ∈ ({a, b} : Finset D.ConnectedComponent), m c := by
        simp [hab]
      _ = ∑ c : D.ConnectedComponent, m c := by rw [← huniv]
      _ = q := hsum
  have hma : 1 ≤ m a := by
    have hpos := a.nonempty_supp.ncard_pos
    rw [hm a] at hpos
    have hmne : m a ≠ 0 := by
      intro hm0
      rw [hm0, mul_zero] at hpos
      omega
    omega
  have hmb : 1 ≤ m b := by
    have hpos := b.nonempty_supp.ncard_pos
    rw [hm b] at hpos
    have hmne : m b ≠ 0 := by
      intro hm0
      rw [hm0, mul_zero] at hpos
      omega
    omega
  have hlo := binarySquare_regular_twoComponents_defectEdge_sameOwner_card_lower
    G hfree hq hreg hcard hcount a b hab (hm a) (hm b) hxyD
  have hdis : Disjoint AA BB := by
    exact coloredTwoStepMiddles_disjoint_of_orderedOwners_ne
      G hfree a a b b (by simpa using hab) x y
  change _ ≤ (AA ∪ BB).card at hlo
  rw [Finset.card_union_of_disjoint hdis] at hlo
  have hrecA := binarySquare_regular_sameOwner_defectEdge_card_add_ownerDefect
    G hfree hq hreg hcard m hm hsum a hxyD
  have hrecB := binarySquare_regular_sameOwner_defectEdge_card_add_ownerDefect
    G hfree hq hreg hcard m hm hsum b hxyD
  rw [mul_two_adjMatrices_apply_eq_card_coloredTwoStepMiddles A D x y] at hrecA
  rw [mul_two_adjMatrices_apply_eq_card_coloredTwoStepMiddles B D x y] at hrecB
  change (AA.card : ℤ) + (AD.card : ℤ) = _ at hrecA
  change (BB.card : ℤ) + (BD.card : ℤ) = _ at hrecB
  have hfirst : 2 * (q - 1) ≤ q * q := by
    have htwoq : 2 * q ≤ q * q := Nat.mul_le_mul_right q (by omega : 2 ≤ q)
    omega
  have hsecond : 2 * m a * m b ≤ q * q - 2 * (q - 1) := by
    have hsq : q * q = m a * m a + 2 * m a * m b + m b * m b := by
      rw [← habSum]
      ring
    have hsquares : 2 * (q - 1) ≤ m a * m a + m b * m b := by
      have haSq : 2 * m a ≤ m a * m a + 1 := by nlinarith
      have hbSq : 2 * m b ≤ m b * m b + 1 := by nlinarith
      omega
    omega
  have hloZ :
      (q * q : ℤ) - 2 * ((q - 1 : ℕ) : ℤ) -
          2 * (m a : ℤ) * (m b : ℤ) ≤
        (AA.card : ℤ) + (BB.card : ℤ) := by
    have hz : (((q * q - 2 * (q - 1)) - 2 * m a * m b : ℕ) : ℤ) ≤
        (AA.card : ℤ) + (BB.card : ℤ) := by exact_mod_cast hlo
    rw [Nat.cast_sub hsecond, Nat.cast_sub hfirst] at hz
    push_cast at hz
    exact hz
  have habSumZ : (m a : ℤ) + (m b : ℤ) = q := by exact_mod_cast habSum
  have hqminus1Z : ((q - 1 : ℕ) : ℤ) = (q : ℤ) - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ q)]
    norm_num
  rw [hqminus1Z] at hloZ
  have hqsubZ : ((q - 2 : ℕ) : ℤ) = (q : ℤ) - 2 := by
    rw [Nat.cast_sub (by omega : 2 ≤ q)]
    norm_num
  have hrouteZ : (AD.card : ℤ) ≤ ((q - 2 : ℕ) : ℤ) := by
    rw [hqsubZ]
    push_cast at hrecA hrecB
    nlinarith [show (0 : ℤ) ≤ BD.card by positivity]
  change AD.card ≤ q - 2
  exact_mod_cast hrouteZ

end

end Erdos85
