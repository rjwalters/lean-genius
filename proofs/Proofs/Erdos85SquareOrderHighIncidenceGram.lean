import Proofs.Erdos85SquareOrderHighIncidence
import Proofs.Erdos85OneTwentyThreeResidualTerminal

/-!
# The square-order high-incidence Gram matrix

At square order, the degree-`d+1` vertices form a pairwise-balanced
incidence design: every high vertex has `d+1` neighbors and every two
distinct high vertices have exactly one common neighbor.  Consequently the
Gram matrix of their vertex-incidence columns is `d I + J`.
-/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- Entrywise form of the high-incidence Gram identity `BᵀB = dI + J`.
Here `B` has all vertices as rows and the high vertices as columns.  High
vertices are pairwise nonadjacent, so its nonzero rows are in fact carried
entirely by the low sector. -/
theorem squareOrder_highIncidence_gram_apply
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G)
    {d : ℕ} (hd : 2 ≤ d) (hmin : ∀ x : V, d ≤ G.degree x)
    (hcover : ∀ {u v}, G.Adj u v → G.degree u = d ∨ G.degree v = d)
    (hcard : Fintype.card V = d * d)
    (x y : (squareOrderHighVertices G d : Set V)) :
    (Matrix.transpose
        (finsetAdjIncidenceMatrix (K := ℤ) G Finset.univ
          (squareOrderHighVertices G d)) *
      finsetAdjIncidenceMatrix (K := ℤ) G Finset.univ
        (squareOrderHighVertices G d)) x y =
      (d : ℤ) * ((1 : Matrix
        (squareOrderHighVertices G d : Set V)
        (squareOrderHighVertices G d : Set V) ℤ) x y) + 1 := by
  classical
  rw [finsetAdjIncidence_transpose_mul_apply]
  have hx : G.degree x.1 = d + 1 := (Finset.mem_filter.mp x.2).2
  have hy : G.degree y.1 = d + 1 := (Finset.mem_filter.mp y.2).2
  by_cases hxy : x = y
  · subst y
    have heq :
        (Finset.univ.filter fun z : (Finset.univ : Finset V) =>
          G.Adj z.1 x.1 ∧ G.Adj z.1 x.1).card = G.degree x.1 := by
      rw [← G.card_neighborFinset_eq_degree]
      apply Finset.card_bij (fun z _ => z.1)
      · intro z hz
        simpa [SimpleGraph.mem_neighborFinset, G.adj_comm] using
          (Finset.mem_filter.mp hz).2.1
      · intro a ha b hb hab
        exact Subtype.ext hab
      · intro v hv
        refine ⟨⟨v, Finset.mem_univ v⟩, ?_, rfl⟩
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by
          simpa [SimpleGraph.mem_neighborFinset, G.adj_comm] using hv⟩
    have heqZ := congrArg (fun n : Nat => (n : ℤ)) heq
    rw [hx] at heqZ
    simpa using heqZ
  · have hxyval : x.1 ≠ y.1 := fun h => hxy (Subtype.ext h)
    have hone := squareOrder_card_common_degree_succ_eq_one
      G hfree hd hmin hcover hcard hx hy hxyval
    have heq :
        (Finset.univ.filter fun z : (Finset.univ : Finset V) =>
          G.Adj z.1 x.1 ∧ G.Adj z.1 y.1).card =
          (G.neighborFinset x.1 ∩ G.neighborFinset y.1).card := by
      apply Finset.card_bij (fun z _ => z.1)
      · intro z hz
        have hz' := (Finset.mem_filter.mp hz).2
        simpa [SimpleGraph.mem_neighborFinset, G.adj_comm] using hz'
      · intro a ha b hb hab
        exact Subtype.ext hab
      · intro v hv
        have hv' : G.Adj v x.1 ∧ G.Adj v y.1 := by
          simpa [SimpleGraph.mem_neighborFinset, G.adj_comm] using hv
        refine ⟨⟨v, Finset.mem_univ v⟩, ?_, rfl⟩
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hv'⟩
    have heqZ := congrArg (fun n : Nat => (n : ℤ)) heq
    rw [hone] at heqZ
    simpa [hxy] using heqZ

/-- Matrix form of the square-order high-incidence Gram identity. -/
theorem squareOrder_highIncidence_gram
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G)
    {d : ℕ} (hd : 2 ≤ d) (hmin : ∀ x : V, d ≤ G.degree x)
    (hcover : ∀ {u v}, G.Adj u v → G.degree u = d ∨ G.degree v = d)
    (hcard : Fintype.card V = d * d) :
    Matrix.transpose
        (finsetAdjIncidenceMatrix (K := ℤ) G Finset.univ
          (squareOrderHighVertices G d)) *
      finsetAdjIncidenceMatrix (K := ℤ) G Finset.univ
        (squareOrderHighVertices G d) =
      (d : ℤ) • (1 : Matrix
        (squareOrderHighVertices G d : Set V)
        (squareOrderHighVertices G d : Set V) ℤ) +
        Matrix.of (fun _ _ => (1 : ℤ)) := by
  ext x y
  rw [squareOrder_highIncidence_gram_apply G hfree hd hmin hcover hcard]
  simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.of_apply,
    smul_eq_mul]

set_option maxHeartbeats 0 in
set_option maxRecDepth 1000000 in
/-- In the positive-high branch the Gram determinant is explicit.  Writing
`h` for the number of high vertices, it is `d^(h-1) * (d+h)`. -/
theorem squareOrder_highIncidence_gram_det
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G)
    {d : ℕ} (hd : 2 ≤ d) (hmin : ∀ x : V, d ≤ G.degree x)
    (hcover : ∀ {u v}, G.Adj u v → G.degree u = d ∨ G.degree v = d)
    (hcard : Fintype.card V = d * d)
    (hpositive : 0 < (squareOrderHighVertices G d).card) :
    (Matrix.transpose
        (finsetAdjIncidenceMatrix (K := ℤ) G Finset.univ
          (squareOrderHighVertices G d)) *
      finsetAdjIncidenceMatrix (K := ℤ) G Finset.univ
        (squareOrderHighVertices G d)).det =
      (d : ℤ) ^ ((squareOrderHighVertices G d).card - 1) *
        ((d : ℤ) + (squareOrderHighVertices G d).card) := by
  classical
  let H := (squareOrderHighVertices G d : Set V)
  let M : Matrix H H ℤ :=
    (d : ℤ) • (1 : Matrix H H ℤ) + Matrix.of (fun _ _ => (1 : ℤ))
  have hHcard : Fintype.card H = (squareOrderHighVertices G d).card := by
    simp [H]
  letI : Nonempty H := Fintype.card_pos_iff.mp (by
    rw [hHcard]
    exact hpositive)
  have hgram := squareOrder_highIncidence_gram
    G hfree hd hmin hcover hcard
  change _ = _
  rw [hgram]
  change M.det = _
  have hnegM :
      ((-(d : ℤ)) • (1 : Matrix H H ℤ) -
        FriendshipTheoremOQ01.onesMatrix H) = -M := by
    ext x y
    simp [M, FriendshipTheoremOQ01.onesMatrix, Matrix.of_apply]
    ring
  have hformula :=
    FriendshipTheoremOQ01.det_scalar_sub_onesMatrix (V := H) (-(d : ℤ))
  rw [hnegM, Matrix.det_neg, hHcard] at hformula
  have hsign_ne : ((-1 : ℤ) ^ (squareOrderHighVertices G d).card) ≠ 0 :=
    pow_ne_zero _ (by norm_num)
  apply (mul_left_cancel₀ hsign_ne)
  rw [hformula]
  have hsucc : (squareOrderHighVertices G d).card =
      ((squareOrderHighVertices G d).card - 1) + 1 := by omega
  have hpowd : (-(d : ℤ)) ^ ((squareOrderHighVertices G d).card - 1) =
      (-1 : ℤ) ^ ((squareOrderHighVertices G d).card - 1) *
        (d : ℤ) ^ ((squareOrderHighVertices G d).card - 1) := by
    rw [neg_pow]
  have hsign : (-1 : ℤ) ^ (squareOrderHighVertices G d).card =
      -((-1 : ℤ) ^ ((squareOrderHighVertices G d).card - 1)) := by
    conv_lhs => rw [hsucc, pow_succ]
    ring
  rw [hpowd, hsign]
  ring

/-- The positive-high Gram matrix is nonsingular over the integers. -/
theorem squareOrder_highIncidence_gram_det_ne_zero
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G)
    {d : ℕ} (hd : 2 ≤ d) (hmin : ∀ x : V, d ≤ G.degree x)
    (hcover : ∀ {u v}, G.Adj u v → G.degree u = d ∨ G.degree v = d)
    (hcard : Fintype.card V = d * d)
    (hpositive : 0 < (squareOrderHighVertices G d).card) :
    (Matrix.transpose
        (finsetAdjIncidenceMatrix (K := ℤ) G Finset.univ
          (squareOrderHighVertices G d)) *
      finsetAdjIncidenceMatrix (K := ℤ) G Finset.univ
        (squareOrderHighVertices G d)).det ≠ 0 := by
  rw [squareOrder_highIncidence_gram_det G hfree hd hmin hcover hcard hpositive]
  apply mul_ne_zero
  · exact pow_ne_zero _ (by exact_mod_cast (show d ≠ 0 by omega))
  · exact ne_of_gt (by positivity)

end

end Erdos85
