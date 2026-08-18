import Proofs.Erdos85MooreFriendship

/-!
# Spectral reduction for the odd first near-Moore order

For the odd first-order template, let `A` be the original adjacency matrix,
`M` the triangle-free-edge perfect matching, and `J` the all-ones matrix.
The previous module proves `A²=(d-1)I+J-M`, `AM=MA`, `M²=I`, and
`tr(AM)=|V|`.  Here we package the minus-eigenspace without choosing a basis:
`B=A(I-M)`.  It satisfies `B³=4dB` and has trace `-|V|`.
-/

open SimpleGraph

namespace Erdos85

/-- Twice the restriction of `A` to the `M=-1` space. -/
noncomputable def oddFirstOrderMinusMatrix
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj] : Matrix V V ℤ :=
  G.adjMatrix ℤ *
    ((1 : Matrix V V ℤ) - (triangleFreeEdgeGraph G).adjMatrix ℤ)

/-- The basis-free minus-space matrix obeys the cubic polynomial
`X(X²-4d)`. -/
theorem oddFirstOrderMinusMatrix_cubic
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) {d : ℕ} (hd : 3 ≤ d) (hdodd : Odd d)
    (hmin : d ≤ G.minDegree)
    (hcard : Fintype.card V = d * (d - 1) + 2) :
    oddFirstOrderMinusMatrix G * oddFirstOrderMinusMatrix G *
        oddFirstOrderMinusMatrix G =
      (4 * d : ℤ) • oddFirstOrderMinusMatrix G := by
  let A := G.adjMatrix ℤ
  let M := (triangleFreeEdgeGraph G).adjMatrix ℤ
  let J := FriendshipTheoremOQ01.onesMatrix V
  let P := (1 : Matrix V V ℤ) - M
  have hsq : A * A =
      (↑d - 1 : ℤ) • (1 : Matrix V V ℤ) + J - M :=
    adjMatrix_sq_eq_sub_triangleFreeEdgeGraph_of_firstOrder_odd
      G hfree hd hdodd hmin hcard
  have hcomm : A * M = M * A :=
    adjMatrix_comm_triangleFreeEdgeGraph_of_firstOrder_odd
      G hfree hd hdodd hmin hcard
  have hM2 : M * M = (1 : Matrix V V ℤ) :=
    triangleFreeEdgeGraph_adjMatrix_sq_eq_one_of_firstOrder_odd
      G hfree hd hdodd hmin hcard
  have hdegreeM : ∀ x : V, (triangleFreeEdgeGraph G).degree x = 1 := by
    intro x
    exact triangleFreeEdgeGraph_degree_eq_one_of_firstOrder_odd
      G hfree hd hdodd hmin hcard x
  have hJM : J * M = J := by
    have h := onesMatrix_mul_adjMatrix_of_regular
      (triangleFreeEdgeGraph G) 1 hdegreeM
    simpa [J, M] using h
  have hAP : A * P = P * A := by
    simp only [P, mul_sub, sub_mul, Matrix.mul_one, Matrix.one_mul]
    rw [hcomm]
  have hP2 : P * P = (2 : ℤ) • P := by
    simp only [P]
    rw [sub_mul, Matrix.one_mul]
    rw [mul_sub, Matrix.mul_one, hM2]
    noncomm_ring
  have hJP : J * P = 0 := by
    simp only [P, mul_sub, Matrix.mul_one, hJM, sub_self]
  have hMP : M * P = -P := by
    simp only [P, mul_sub, Matrix.mul_one, hM2]
    noncomm_ring
  have hA2P : (A * A) * P = (d : ℤ) • P := by
    rw [hsq]
    simp only [add_mul, sub_mul, Matrix.smul_mul, Matrix.one_mul, hJP, hMP]
    simp [sub_smul, add_smul, smul_smul]
  have hB2 : (A * P) * (A * P) = (2 * d : ℤ) • P := by
    calc
      (A * P) * (A * P) = A * (P * A) * P := by noncomm_ring
      _ = A * (A * P) * P := by rw [← hAP]
      _ = (A * A) * (P * P) := by noncomm_ring
      _ = (A * A) * ((2 : ℤ) • P) := by rw [hP2]
      _ = (2 : ℤ) • ((A * A) * P) := by rw [Matrix.mul_smul]
      _ = (2 : ℤ) • ((d : ℤ) • P) := by rw [hA2P]
      _ = (2 * d : ℤ) • P := by module
  change (A * P) * (A * P) * (A * P) = (4 * d : ℤ) • (A * P)
  calc
    (A * P) * (A * P) * (A * P) =
        ((2 * d : ℤ) • P) * (A * P) := by rw [hB2]
    _ = (2 * d : ℤ) • (P * (A * P)) := by rw [Matrix.smul_mul]
    _ = (2 * d : ℤ) • (A * (P * P)) := by
      rw [← Matrix.mul_assoc, ← hAP, Matrix.mul_assoc]
    _ = (2 * d : ℤ) • (A * ((2 : ℤ) • P)) := by rw [hP2]
    _ = (4 * d : ℤ) • (A * P) := by
      rw [Matrix.mul_smul]
      module

/-- The minus-space trace is nonzero and in fact equals `-|V|`. -/
theorem trace_oddFirstOrderMinusMatrix
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) {d : ℕ} (hd : 3 ≤ d) (hdodd : Odd d)
    (hmin : d ≤ G.minDegree)
    (hcard : Fintype.card V = d * (d - 1) + 2) :
    Matrix.trace (oddFirstOrderMinusMatrix G) = -(Fintype.card V : ℤ) := by
  rw [oddFirstOrderMinusMatrix, mul_sub, Matrix.mul_one, Matrix.trace_sub]
  rw [SimpleGraph.trace_adjMatrix]
  rw [trace_adjMatrix_mul_triangleFreeEdgeGraph_of_firstOrder_odd
    G hfree hd hdodd hmin hcard]
  simp

/-- An integral, basis-free version of the plus space with the all-ones
direction removed.  Multiplication by `|V|` clears the projection
denominator. -/
noncomputable def oddFirstOrderPlusMatrix
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj] : Matrix V V ℤ :=
  G.adjMatrix ℤ *
    (((Fintype.card V : ℤ) •
        ((1 : Matrix V V ℤ) + (triangleFreeEdgeGraph G).adjMatrix ℤ)) -
      (2 : ℤ) • FriendshipTheoremOQ01.onesMatrix V)

/-- The complementary matrix obeys the cubic polynomial
`X(X²-4|V|²(d-2))`. -/
theorem oddFirstOrderPlusMatrix_cubic
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) {d : ℕ} (hd : 3 ≤ d) (hdodd : Odd d)
    (hmin : d ≤ G.minDegree)
    (hcard : Fintype.card V = d * (d - 1) + 2) :
    oddFirstOrderPlusMatrix G * oddFirstOrderPlusMatrix G *
        oddFirstOrderPlusMatrix G =
      (4 * (Fintype.card V : ℤ) ^ 2 * (d - 2) : ℤ) •
        oddFirstOrderPlusMatrix G := by
  let A := G.adjMatrix ℤ
  let M := (triangleFreeEdgeGraph G).adjMatrix ℤ
  let J := FriendshipTheoremOQ01.onesMatrix V
  let N : ℤ := Fintype.card V
  let Q := (1 : Matrix V V ℤ) + M
  let R := N • Q - (2 : ℤ) • J
  have hsq : A * A =
      (↑d - 1 : ℤ) • (1 : Matrix V V ℤ) + J - M :=
    adjMatrix_sq_eq_sub_triangleFreeEdgeGraph_of_firstOrder_odd
      G hfree hd hdodd hmin hcard
  have hcomm : A * M = M * A :=
    adjMatrix_comm_triangleFreeEdgeGraph_of_firstOrder_odd
      G hfree hd hdodd hmin hcard
  have hM2 : M * M = (1 : Matrix V V ℤ) :=
    triangleFreeEdgeGraph_adjMatrix_sq_eq_one_of_firstOrder_odd
      G hfree hd hdodd hmin hcard
  have hdegreeM : ∀ x : V, (triangleFreeEdgeGraph G).degree x = 1 := by
    intro x
    exact triangleFreeEdgeGraph_degree_eq_one_of_firstOrder_odd
      G hfree hd hdodd hmin hcard x
  have hMJ : M * J = J := by
    have h := FriendshipTheoremOQ01.adjMatrix_mul_ones
      (triangleFreeEdgeGraph G) 1 hdegreeM
    simpa [M, J] using h
  have hJM : J * M = J := by
    have h := onesMatrix_mul_adjMatrix_of_regular
      (triangleFreeEdgeGraph G) 1 hdegreeM
    simpa [M, J] using h
  have hbelow : Fintype.card V < (d + 1) * (d - 1) + 1 := by
    rw [hcard]
    obtain ⟨e, rfl⟩ : ∃ e : ℕ, d = e + 3 := ⟨d - 3, by omega⟩
    norm_num
    nlinarith
  have hreg : ∀ x : V, G.degree x = d :=
    regular_of_minDegree_card_lt_nextMooreLayer
      G hfree (by omega) hmin hbelow
  have hAJ : A * J = (d : ℤ) • J :=
    FriendshipTheoremOQ01.adjMatrix_mul_ones G d hreg
  have hJA : J * A = (d : ℤ) • J :=
    onesMatrix_mul_adjMatrix_of_regular G d hreg
  have hJ2 : J * J = N • J := by
    ext x y
    simp [J, N, FriendshipTheoremOQ01.onesMatrix, Matrix.mul_apply]
  have hAQ : A * Q = Q * A := by
    simp only [Q, mul_add, add_mul, Matrix.mul_one, Matrix.one_mul]
    rw [hcomm]
  have hQ2 : Q * Q = (2 : ℤ) • Q := by
    simp only [Q]
    rw [add_mul, Matrix.one_mul, mul_add, Matrix.mul_one, hM2]
    module
  have hQJ : Q * J = (2 : ℤ) • J := by
    simp only [Q, add_mul, Matrix.one_mul, hMJ]
    module
  have hJQ : J * Q = (2 : ℤ) • J := by
    simp only [Q, mul_add, Matrix.mul_one, hJM]
    module
  have hA2Q : (A * A) * Q =
      (d - 2 : ℤ) • Q + (2 : ℤ) • J := by
    rw [hsq]
    simp only [add_mul, sub_mul, Matrix.smul_mul, Matrix.one_mul, hJQ]
    have hMQ : M * Q = Q := by
      simp only [Q, mul_add, Matrix.mul_one, hM2]
      module
    rw [hMQ]
    module
  have hAR : A * R = R * A := by
    simp only [R, mul_sub, sub_mul, Matrix.mul_smul, Matrix.smul_mul, hAQ,
      hAJ, hJA]
  have hNQ2 : (N • Q) * (N • Q) = (2 * N * N : ℤ) • Q := by
    rw [Matrix.smul_mul, Matrix.mul_smul, hQ2]
    module
  have hNQJ : (N • Q) * ((2 : ℤ) • J) = (4 * N : ℤ) • J := by
    rw [Matrix.smul_mul, Matrix.mul_smul, hQJ]
    module
  have hJNQ : ((2 : ℤ) • J) * (N • Q) = (4 * N : ℤ) • J := by
    rw [Matrix.smul_mul, Matrix.mul_smul, hJQ]
    module
  have hJJ : ((2 : ℤ) • J) * ((2 : ℤ) • J) = (4 * N : ℤ) • J := by
    rw [Matrix.smul_mul, Matrix.mul_smul, hJ2]
    module
  have hR2 : R * R = (2 * N : ℤ) • R := by
    simp only [R]
    rw [sub_mul]
    rw [mul_sub, mul_sub]
    rw [hNQ2, hNQJ, hJNQ, hJJ]
    module
  have hA2J : (A * A) * J = (d * d : ℤ) • J := by
    calc
      (A * A) * J = A * (A * J) := by rw [Matrix.mul_assoc]
      _ = A * ((d : ℤ) • J) := by rw [hAJ]
      _ = (d : ℤ) • (A * J) := by rw [Matrix.mul_smul]
      _ = (d : ℤ) • ((d : ℤ) • J) := by rw [hAJ]
      _ = (d * d : ℤ) • J := by module
  have hA2R : (A * A) * R = (d - 2 : ℤ) • R := by
    simp only [R, mul_sub, Matrix.mul_smul, hA2Q]
    rw [hA2J]
    have hcast1 : ((d - 1 : ℕ) : ℤ) = (d : ℤ) - 1 := by
      rw [Nat.cast_sub (by omega)]
      norm_num
    have hN' : N = (d : ℤ) * ((d : ℤ) - 1) + 2 := by
      simp only [N, hcard, Nat.cast_add, Nat.cast_mul, hcast1]
      norm_num
    rw [hN']
    module
  have hB2 : (A * R) * (A * R) =
      (2 * N * (d - 2) : ℤ) • R := by
    calc
      (A * R) * (A * R) = A * (R * A) * R := by noncomm_ring
      _ = A * (A * R) * R := by rw [← hAR]
      _ = (A * A) * (R * R) := by noncomm_ring
      _ = (A * A) * ((2 * N : ℤ) • R) := by rw [hR2]
      _ = (2 * N : ℤ) • ((A * A) * R) := by rw [Matrix.mul_smul]
      _ = (2 * N : ℤ) • ((d - 2 : ℤ) • R) := by rw [hA2R]
      _ = (2 * N * (d - 2) : ℤ) • R := by module
  change (A * R) * (A * R) * (A * R) =
    (4 * N ^ 2 * (d - 2) : ℤ) • (A * R)
  calc
    (A * R) * (A * R) * (A * R) =
        ((2 * N * (d - 2) : ℤ) • R) * (A * R) := by rw [hB2]
    _ = (2 * N * (d - 2) : ℤ) • (R * (A * R)) := by
      rw [Matrix.smul_mul]
    _ = (2 * N * (d - 2) : ℤ) • (A * (R * R)) := by
      rw [← Matrix.mul_assoc, ← hAR, Matrix.mul_assoc]
    _ = (2 * N * (d - 2) : ℤ) •
        (A * ((2 * N : ℤ) • R)) := by rw [hR2]
    _ = (4 * N ^ 2 * (d - 2) : ℤ) • (A * R) := by
      rw [Matrix.mul_smul]
      module

/-- The complementary trace is `|V|(|V|-2d)`, nonzero for `d≥3`. -/
theorem trace_oddFirstOrderPlusMatrix
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) {d : ℕ} (hd : 3 ≤ d) (hdodd : Odd d)
    (hmin : d ≤ G.minDegree)
    (hcard : Fintype.card V = d * (d - 1) + 2) :
    Matrix.trace (oddFirstOrderPlusMatrix G) =
      (Fintype.card V : ℤ) * ((Fintype.card V : ℤ) - 2 * d) := by
  let A := G.adjMatrix ℤ
  let M := (triangleFreeEdgeGraph G).adjMatrix ℤ
  let J := FriendshipTheoremOQ01.onesMatrix V
  let N : ℤ := Fintype.card V
  have hAM := trace_adjMatrix_mul_triangleFreeEdgeGraph_of_firstOrder_odd
    G hfree hd hdodd hmin hcard
  have hbelow : Fintype.card V < (d + 1) * (d - 1) + 1 := by
    rw [hcard]
    obtain ⟨e, rfl⟩ : ∃ e : ℕ, d = e + 3 := ⟨d - 3, by omega⟩
    norm_num
    nlinarith
  have hreg : ∀ x : V, G.degree x = d :=
    regular_of_minDegree_card_lt_nextMooreLayer
      G hfree (by omega) hmin hbelow
  have hAJ : A * J = (d : ℤ) • J :=
    FriendshipTheoremOQ01.adjMatrix_mul_ones G d hreg
  change Matrix.trace (A * (N • ((1 : Matrix V V ℤ) + M) - 2 • J)) =
    N * (N - 2 * d)
  rw [mul_sub, Matrix.mul_smul, mul_add, Matrix.mul_one]
  rw [Matrix.mul_smul, hAJ]
  rw [Matrix.trace_sub, Matrix.trace_smul, Matrix.trace_add,
    Matrix.trace_smul, SimpleGraph.trace_adjMatrix]
  rw [show Matrix.trace (A * M) = N by exact_mod_cast hAM]
  have htraceJ : Matrix.trace J = N := by
    simp [J, N, FriendshipTheoremOQ01.onesMatrix, Matrix.trace]
  rw [Matrix.trace_smul, htraceJ]
  ring

/-! ## Modular trace obstruction

The odd first-order case can in fact be closed without the full cubic-trace
square principle.  Modulo a prime divisor of the cubic parameter, the matrix
is nilpotent, so its trace vanishes modulo that prime.
-/

/-- If an integer matrix satisfies `T³=qT`, every prime divisor of `q` also
divides its integer trace. -/
theorem prime_dvd_trace_of_matrix_cubic
    {V : Type*} [Fintype V] [DecidableEq V]
    (T : Matrix V V ℤ) {q p : ℕ} (hp : p.Prime) (hpq : p ∣ q)
    (hcubic : T * T * T = (q : ℤ) • T) :
    (p : ℤ) ∣ Matrix.trace T := by
  letI : Fact p.Prime := ⟨hp⟩
  let f : ℤ →+* ZMod p := Int.castRingHom (ZMod p)
  let U : Matrix V V (ZMod p) := T.map f
  have hqzero : (q : ZMod p) = 0 :=
    (ZMod.natCast_eq_zero_iff q p).mpr hpq
  have hcubeZero : U * U * U = 0 := by
    calc
      U * U * U = (T * T * T).map f := by
        simp [U, Matrix.map_mul]
      _ = ((q : ℤ) • T).map f := by rw [hcubic]
      _ = 0 := by
        ext x y
        simp only [Matrix.map_apply, Matrix.smul_apply, Matrix.zero_apply,
          smul_eq_mul]
        rw [map_mul]
        have hfq : f (q : ℤ) = (q : ZMod p) := by simp [f]
        rw [hfq, hqzero, zero_mul]
  have hnil : IsNilpotent U := by
    refine ⟨3, ?_⟩
    simpa [pow_succ, pow_two, Matrix.mul_assoc] using hcubeZero
  have htraceZero : Matrix.trace U = 0 :=
    (Matrix.isNilpotent_trace_of_isNilpotent hnil).eq_zero
  have hcastTrace : (↑(Matrix.trace T) : ZMod p) = 0 := by
    simpa [U, f, Matrix.trace] using htraceZero
  exact (ZMod.intCast_zmod_eq_zero_iff_dvd (Matrix.trace T) p).mp hcastTrace

/-- **Unconditional exclusion of the first possible order for odd degree.**
A prime divisor `p` of odd `d` divides the cubic parameter `4d`.  Nilpotent
trace reduction makes `p ∣ |V|`; the order formula then gives `p ∣ 2`, forcing
`p=2`, contrary to oddness. -/
theorem containsC4_of_odd_firstOrder
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {d : ℕ} (hd : 3 ≤ d) (hdodd : Odd d)
    (hmin : d ≤ G.minDegree)
    (hcard : Fintype.card V = d * (d - 1) + 2) :
    containsC4 V G := by
  by_contra hfree
  letI : DecidableRel (triangleFreeEdgeGraph G).Adj := Classical.decRel _
  obtain ⟨p, hp, hpd⟩ := Nat.exists_prime_and_dvd (by omega : d ≠ 1)
  have hp4d : p ∣ 4 * d := dvd_mul_of_dvd_right hpd 4
  have hptrace : (p : ℤ) ∣ Matrix.trace (oddFirstOrderMinusMatrix G) :=
    prime_dvd_trace_of_matrix_cubic (oddFirstOrderMinusMatrix G)
      hp hp4d (oddFirstOrderMinusMatrix_cubic
        G hfree hd hdodd hmin hcard)
  have htrace := trace_oddFirstOrderMinusMatrix
    G hfree hd hdodd hmin hcard
  rw [htrace] at hptrace
  have hpCardInt : (p : ℤ) ∣ (Fintype.card V : ℤ) := by
    exact dvd_neg.mp hptrace
  have hpCard : p ∣ Fintype.card V :=
    Int.natCast_dvd_natCast.mp hpCardInt
  have hpProd : p ∣ d * (d - 1) := dvd_mul_of_dvd_left hpd (d - 1)
  have hpSum : p ∣ d * (d - 1) + 2 := by rwa [← hcard]
  have hpTwo : p ∣ 2 := (Nat.dvd_add_iff_right hpProd).mpr hpSum
  have hpEqTwo : p = 2 := by
    rcases (Nat.dvd_prime Nat.prime_two).mp hpTwo with hp1 | hp2
    · exact (hp.ne_one hp1).elim
    · exact hp2
  have htwoDvd : 2 ∣ d := by rwa [← hpEqTwo]
  exact (Nat.not_even_iff_odd.mpr hdodd) ((even_iff_two_dvd.mpr htwoDvd))

/-- **Odd-degree strict Moore bound, sharpened by two over equality.** -/
theorem mul_pred_add_three_le_card_of_c4Free_minDegree_odd
    {V : Type*} [Fintype V] [Nonempty V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {d : ℕ} (hd : 3 ≤ d) (hdodd : Odd d)
    (hmin : d ≤ G.minDegree) (hfree : ¬ containsC4 V G) :
    d * (d - 1) + 3 ≤ Fintype.card V := by
  have hbase := mul_pred_add_two_le_card_of_c4Free_minDegree
    G hd hmin hfree
  by_contra hnot
  have heq : Fintype.card V = d * (d - 1) + 2 := by omega
  exact hfree (containsC4_of_odd_firstOrder G hd hdodd hmin heq)

/-- Threshold form of the sharpened odd-degree bound. -/
theorem minDegreeForC4_firstOrder_le_of_odd
    {d : ℕ} (hd : 3 ≤ d) (hdodd : Odd d) :
    minDegreeForC4 (d * (d - 1) + 2) ≤ d := by
  apply Nat.sInf_le
  intro G _ hmin
  exact containsC4_of_odd_firstOrder G hd hdodd hmin (by simp)

/-! ## Exact final algebraic interface

The graph theory is now reduced to the following generic fact about integer
matrices: a nonzero trace for a matrix annihilated by `X(X²-q)` forces `q`
to be a square.  We state the reduction with that fact as an explicit
hypothesis, without adding it as an axiom.
-/

/-- Removing a square factor from a square product. -/
theorem isSquare_of_sq_mul_eq_sq {a c s : ℕ} (ha : 0 < a)
    (h : a * a * c = s * s) :
    ∃ t : ℕ, c = t * t := by
  have hpow : a ^ 2 ∣ s ^ 2 := by
    refine ⟨c, ?_⟩
    simpa [pow_two, mul_assoc] using h.symm
  have hadiv : a ∣ s := (Nat.pow_dvd_pow_iff (by omega : 2 ≠ 0)).mp hpow
  obtain ⟨t, rfl⟩ := hadiv
  refine ⟨t, ?_⟩
  nlinarith

/-- Two natural squares cannot differ by exactly two. -/
theorem not_consecutive_distance_two_squares {d : ℕ} (hd : 2 ≤ d) :
    ¬((∃ a : ℕ, d = a * a) ∧ (∃ b : ℕ, d - 2 = b * b)) := by
  rintro ⟨⟨a, ha⟩, ⟨b, hb⟩⟩
  have hab : a * a = b * b + 2 := by omega
  have hsquareMod (x : ℕ) : x * x % 4 = 0 ∨ x * x % 4 = 1 := by
    rw [Nat.mul_mod]
    have hxlt := Nat.mod_lt x (by omega : 0 < 4)
    interval_cases hx : x % 4 <;> simp [hx]
  have haMod := hsquareMod a
  have hbMod := hsquareMod b
  have hmod := congrArg (fun z : ℕ => z % 4) hab
  rcases haMod with ha0 | ha1 <;> rcases hbMod with hb0 | hb1 <;>
    omega

/-- **Conditional closure of the odd first-order case.**  It is enough to
prove the displayed cubic-trace principle for integer matrices of the same
dimension as the graph.  The checked minus and plus matrices then force `d`
and `d-2` to be squares, a contradiction. -/
theorem containsC4_of_odd_firstOrder_of_cubicTraceSquare
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {d : ℕ} (hd : 3 ≤ d) (hdodd : Odd d)
    (hmin : d ≤ G.minDegree)
    (hcard : Fintype.card V = d * (d - 1) + 2)
    (hcubic : ∀ (T : Matrix V V ℤ) (q : ℕ),
      T * T * T = (q : ℤ) • T → Matrix.trace T ≠ 0 →
        ∃ s : ℕ, q = s * s) :
    containsC4 V G := by
  by_contra hfree
  letI : DecidableRel (triangleFreeEdgeGraph G).Adj := Classical.decRel _
  have hnpos : 0 < Fintype.card V := by
    rw [hcard]
    positivity
  have hminusCubic := oddFirstOrderMinusMatrix_cubic
    G hfree hd hdodd hmin hcard
  have hminusTrace := trace_oddFirstOrderMinusMatrix
    G hfree hd hdodd hmin hcard
  have hminusTraceNe : Matrix.trace (oddFirstOrderMinusMatrix G) ≠ 0 := by
    rw [hminusTrace]
    exact neg_ne_zero.mpr (Int.ofNat_ne_zero.mpr (Nat.ne_of_gt hnpos))
  obtain ⟨s, hs⟩ := hcubic (oddFirstOrderMinusMatrix G) (4 * d)
    hminusCubic hminusTraceNe
  have hdSquare : ∃ a : ℕ, d = a * a := by
    apply isSquare_of_sq_mul_eq_sq (a := 2) (s := s) (by omega)
    nlinarith
  have hplusCubicInt := oddFirstOrderPlusMatrix_cubic
    G hfree hd hdodd hmin hcard
  let qplus : ℕ := 4 * (Fintype.card V) ^ 2 * (d - 2)
  have hplusCubic : oddFirstOrderPlusMatrix G * oddFirstOrderPlusMatrix G *
      oddFirstOrderPlusMatrix G = (qplus : ℤ) • oddFirstOrderPlusMatrix G := by
    simpa [qplus, Nat.cast_mul, Nat.cast_pow,
      Nat.cast_sub (by omega : 2 ≤ d)] using hplusCubicInt
  have hn2d : 2 * d < Fintype.card V := by
    rw [hcard]
    obtain ⟨e, rfl⟩ : ∃ e : ℕ, d = e + 3 := ⟨d - 3, by omega⟩
    norm_num
    nlinarith
  have hplusTrace := trace_oddFirstOrderPlusMatrix
    G hfree hd hdodd hmin hcard
  have hplusTraceNe : Matrix.trace (oddFirstOrderPlusMatrix G) ≠ 0 := by
    rw [hplusTrace]
    have hcardNe : (Fintype.card V : ℤ) ≠ 0 :=
      Int.ofNat_ne_zero.mpr (Nat.ne_of_gt hnpos)
    have hdiffPos : (0 : ℤ) < (Fintype.card V : ℤ) - 2 * d := by
      apply sub_pos.mpr
      exact_mod_cast hn2d
    exact mul_ne_zero hcardNe (ne_of_gt hdiffPos)
  obtain ⟨t, ht⟩ := hcubic (oddFirstOrderPlusMatrix G) qplus
    hplusCubic hplusTraceNe
  have hd2Square : ∃ b : ℕ, d - 2 = b * b := by
    apply isSquare_of_sq_mul_eq_sq
      (a := 2 * Fintype.card V) (s := t) (by positivity)
    rw [← ht]
    simp only [qplus, pow_two]
    ring
  exact not_consecutive_distance_two_squares (by omega) ⟨hdSquare, hd2Square⟩

/-- Conditional numerical payoff: the generic cubic-trace principle improves
the strict Moore bound by one further vertex for every odd `d≥3`. -/
theorem mul_pred_add_three_le_card_of_c4Free_minDegree_odd_of_cubicTraceSquare
    {V : Type*} [Fintype V] [Nonempty V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {d : ℕ} (hd : 3 ≤ d) (hdodd : Odd d)
    (hmin : d ≤ G.minDegree) (hfree : ¬ containsC4 V G)
    (hcubic : ∀ (T : Matrix V V ℤ) (q : ℕ),
      T * T * T = (q : ℤ) • T → Matrix.trace T ≠ 0 →
        ∃ s : ℕ, q = s * s) :
    d * (d - 1) + 3 ≤ Fintype.card V := by
  have hbase := mul_pred_add_two_le_card_of_c4Free_minDegree
    G hd hmin hfree
  by_contra hnot
  have heq : Fintype.card V = d * (d - 1) + 2 := by omega
  exact hfree (containsC4_of_odd_firstOrder_of_cubicTraceSquare
    G hd hdodd hmin heq hcubic)

end Erdos85
