import Proofs.Erdos85OddFirstOrderSpectral

/-!
# The antipodal matching in the even first-order template

At order `d(d-1)+2` with even `d`, exact distance-layer accounting leaves
one vertex beyond distance two from every center.  These pairs are symmetric,
so they form a perfect matching.  Every other distinct pair has exactly one
common neighbor.  Thus, if `P` is the antipodal matching matrix,
`A²=(d-1)I+J-P`.
-/

open SimpleGraph

namespace Erdos85

/-- Vertices beyond distance two from `x`, with the subtype erased. -/
def antipodalNeighbors
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (x : V) : Finset V :=
  (externalRepairCandidates G x).map
    ⟨Subtype.val, Subtype.val_injective⟩

@[simp] theorem mem_antipodalNeighbors
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (x y : V) :
    y ∈ antipodalNeighbors G x ↔
      y ≠ x ∧ ¬ G.Adj x y ∧
        (G.neighborFinset x ∩ G.neighborFinset y).card = 0 := by
  constructor
  · intro hy
    rw [antipodalNeighbors, Finset.mem_map] at hy
    obtain ⟨z, hz, rfl⟩ := hy
    have hfar := (mem_externalRepairCandidates G x z).mp hz
    refine ⟨z.2, fun hxz => hfar.1 hxz.symm, ?_⟩
    apply Finset.card_eq_zero.mpr
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro w hw
    have hwx : G.Adj w x :=
      ((G.mem_neighborFinset x w).mp (Finset.mem_inter.mp hw).1).symm
    have hzw : G.Adj z.1 w :=
      (G.mem_neighborFinset z.1 w).mp (Finset.mem_inter.mp hw).2
    exact (hfar.2 ⟨w, fun h => by subst w; exact G.loopless.irrefl x hwx⟩ hwx) hzw
  · rintro ⟨hyx, hxy, hzero⟩
    let z : {w : V // w ≠ x} := ⟨y, hyx⟩
    rw [antipodalNeighbors, Finset.mem_map]
    refine ⟨z, ?_, rfl⟩
    rw [mem_externalRepairCandidates]
    refine ⟨fun hyxAdj => hxy hyxAdj.symm, ?_⟩
    intro w hwx hyw
    have hymem : w.1 ∈ G.neighborFinset x ∩ G.neighborFinset y :=
      Finset.mem_inter.mpr ⟨
        (G.mem_neighborFinset x w.1).mpr hwx.symm,
        (G.mem_neighborFinset y w.1).mpr hyw⟩
    rw [Finset.card_eq_zero.mp hzero] at hymem
    exact Finset.notMem_empty _ hymem

/-- The relation of being beyond distance two is symmetric. -/
theorem mem_antipodalNeighbors_comm
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (x y : V) :
    y ∈ antipodalNeighbors G x ↔ x ∈ antipodalNeighbors G y := by
  rw [mem_antipodalNeighbors, mem_antipodalNeighbors]
  constructor
  · rintro ⟨hyx, hxy, hzero⟩
    exact ⟨hyx.symm, fun hyxAdj => hxy hyxAdj.symm,
      by simpa [Finset.inter_comm] using hzero⟩
  · rintro ⟨hxy, hyx, hzero⟩
    exact ⟨hxy.symm, fun hxyAdj => hyx hxyAdj.symm,
      by simpa [Finset.inter_comm] using hzero⟩

/-- The spanning graph pairing vertices that are beyond distance two. -/
def antipodalGraph
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] : SimpleGraph V where
  Adj x y := y ∈ antipodalNeighbors G x
  symm := ⟨by
    intro x y hxy
    exact (mem_antipodalNeighbors_comm G x y).mp hxy⟩
  loopless := ⟨by
    intro x hx
    exact ((mem_antipodalNeighbors G x x).mp hx).1 rfl⟩

@[simp] theorem antipodalGraph_adj
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (x y : V) :
    (antipodalGraph G).Adj x y ↔ y ∈ antipodalNeighbors G x := by
  rfl

theorem antipodalGraph_neighborFinset
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj] (x : V) :
    (antipodalGraph G).neighborFinset x = antipodalNeighbors G x := by
  ext y
  simp [SimpleGraph.mem_neighborFinset]

/-- In the even first-order template every vertex has a unique antipode. -/
theorem antipodalGraph_degree_eq_one_of_firstOrder_even
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    (hfree : ¬ containsC4 V G) {d : ℕ} (hd : 3 ≤ d) (hdeven : Even d)
    (hmin : d ≤ G.minDegree)
    (hcard : Fintype.card V = d * (d - 1) + 2)
    (x : V) :
    (antipodalGraph G).degree x = 1 := by
  rw [← (antipodalGraph G).card_neighborFinset_eq_degree,
    antipodalGraph_neighborFinset, antipodalNeighbors, Finset.card_map]
  exact (firstOrder_structure_of_even G hfree hd hdeven hmin hcard x).1

/-- Exact common-neighbor table: antipodal pairs have no common neighbor;
every other distinct pair has exactly one. -/
theorem card_common_eq_if_antipodal_of_firstOrder_even
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G) {d : ℕ} (hd : 3 ≤ d) (hdeven : Even d)
    (hmin : d ≤ G.minDegree)
    (hcard : Fintype.card V = d * (d - 1) + 2)
    (x y : V) (hxy : x ≠ y) :
    (G.neighborFinset x ∩ G.neighborFinset y).card =
      if y ∈ antipodalNeighbors G x then 0 else 1 := by
  classical
  by_cases hanti : y ∈ antipodalNeighbors G x
  · rw [if_pos hanti]
    exact ((mem_antipodalNeighbors G x y).mp hanti).2.2
  · rw [if_neg hanti]
    have hupper := common_le_one_of_not_containsC4 hfree x y hxy
    apply le_antisymm hupper
    by_contra hnot
    have hzero : (G.neighborFinset x ∩ G.neighborFinset y).card = 0 := by
      omega
    by_cases hadj : G.Adj x y
    · let z : {w : V // w ∈ G.neighborSet x} := ⟨y, hadj⟩
      have hz := localNeighborhood_degree_eq_one_of_firstOrder_even
        G hfree hd hdeven hmin hcard x z
      rw [degree_induce_neighborSet_eq_card_common, hzero] at hz
      omega
    · exact hanti ((mem_antipodalNeighbors G x y).mpr
        ⟨hxy.symm, hadj, hzero⟩)

/-- **Even first-order matrix equation.**  If `P` is the antipodal perfect
matching, then `A² = (d-1)I + J - P`. -/
theorem adjMatrix_sq_eq_sub_antipodalGraph_of_firstOrder_even
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    (hfree : ¬ containsC4 V G) {d : ℕ} (hd : 3 ≤ d) (hdeven : Even d)
    (hmin : d ≤ G.minDegree)
    (hcard : Fintype.card V = d * (d - 1) + 2) :
    G.adjMatrix ℤ * G.adjMatrix ℤ =
      (↑d - 1 : ℤ) • (1 : Matrix V V ℤ) +
        FriendshipTheoremOQ01.onesMatrix V -
          (antipodalGraph G).adjMatrix ℤ := by
  have hbelow : Fintype.card V < (d + 1) * (d - 1) + 1 := by
    rw [hcard]
    obtain ⟨e, rfl⟩ : ∃ e : ℕ, d = e + 3 := ⟨d - 3, by omega⟩
    norm_num
    nlinarith
  have hreg : ∀ x : V, G.degree x = d :=
    regular_of_minDegree_card_lt_nextMooreLayer
      G hfree (by omega) hmin hbelow
  ext x y
  simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply,
    Matrix.one_apply, FriendshipTheoremOQ01.onesMatrix, Matrix.of_apply,
    smul_eq_mul]
  by_cases hxy : x = y
  · subst y
    rw [G.adjMatrix_mul_self_apply_self, hreg x]
    simp [SimpleGraph.adjMatrix_apply]
  · rw [adjMatrix_sq_apply_eq_card_common]
    have hcommon := card_common_eq_if_antipodal_of_firstOrder_even
      G hfree hd hdeven hmin hcard x y hxy
    by_cases hanti : y ∈ antipodalNeighbors G x
    · rw [if_pos hanti] at hcommon
      simp [SimpleGraph.adjMatrix_apply, hxy, hanti, hcommon]
    · rw [if_neg hanti] at hcommon
      simp [SimpleGraph.adjMatrix_apply, hxy, hanti, hcommon]

/-- The antipodal matching matrix is an involution. -/
theorem antipodalGraph_adjMatrix_sq_eq_one_of_firstOrder_even
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    (hfree : ¬ containsC4 V G) {d : ℕ} (hd : 3 ≤ d) (hdeven : Even d)
    (hmin : d ≤ G.minDegree)
    (hcard : Fintype.card V = d * (d - 1) + 2) :
    (antipodalGraph G).adjMatrix ℤ *
        (antipodalGraph G).adjMatrix ℤ = (1 : Matrix V V ℤ) := by
  apply adjMatrix_sq_eq_one_of_degree_one
  intro x
  exact antipodalGraph_degree_eq_one_of_firstOrder_even
    G hfree hd hdeven hmin hcard x

/-- The adjacency matrix commutes with the antipodal involution. -/
theorem adjMatrix_comm_antipodalGraph_of_firstOrder_even
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    (hfree : ¬ containsC4 V G) {d : ℕ} (hd : 3 ≤ d) (hdeven : Even d)
    (hmin : d ≤ G.minDegree)
    (hcard : Fintype.card V = d * (d - 1) + 2) :
    G.adjMatrix ℤ * (antipodalGraph G).adjMatrix ℤ =
      (antipodalGraph G).adjMatrix ℤ * G.adjMatrix ℤ := by
  let A := G.adjMatrix ℤ
  let P := (antipodalGraph G).adjMatrix ℤ
  let J := FriendshipTheoremOQ01.onesMatrix V
  let C := (↑d - 1 : ℤ) • (1 : Matrix V V ℤ)
  have hsq : A * A = C + J - P :=
    adjMatrix_sq_eq_sub_antipodalGraph_of_firstOrder_even
      G hfree hd hdeven hmin hcard
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
  have hP : P = C + J - A * A := by
    rw [hsq]
    noncomm_ring
  change A * P = P * A
  rw [hP, mul_sub, sub_mul, mul_add, add_mul, hAJ, hJA]
  simp only [C, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one,
    Matrix.one_mul]
  noncomm_ring

/-- Unlike the odd defect matching, antipodal edges are nonedges of `G`, so
the mixed trace vanishes. -/
theorem trace_adjMatrix_mul_antipodalGraph_of_firstOrder_even
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    (hfree : ¬ containsC4 V G) {d : ℕ} (hd : 3 ≤ d) (hdeven : Even d)
    (hmin : d ≤ G.minDegree)
    (hcard : Fintype.card V = d * (d - 1) + 2) :
    Matrix.trace (G.adjMatrix ℤ *
      (antipodalGraph G).adjMatrix ℤ) = 0 := by
  rw [Matrix.trace]
  apply Finset.sum_eq_zero
  intro x _
  change (G.adjMatrix ℤ * (antipodalGraph G).adjMatrix ℤ) x x = 0
  rw [(antipodalGraph G).mul_adjMatrix_apply]
  rw [antipodalGraph_neighborFinset]
  apply Finset.sum_eq_zero
  intro y hy
  rw [SimpleGraph.adjMatrix_apply, if_neg]
  exact ((mem_antipodalNeighbors G x y).mp hy).2.1

noncomputable def evenFirstOrderPlusMatrix
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj] : Matrix V V ℤ :=
  G.adjMatrix ℤ *
    (((Fintype.card V : ℤ) •
        ((1 : Matrix V V ℤ) + (antipodalGraph G).adjMatrix ℤ)) -
      (2 : ℤ) • FriendshipTheoremOQ01.onesMatrix V)

/-- The even plus-space matrix obeys the cubic polynomial
`X(X²-4|V|²(d-2))`. -/
theorem evenFirstOrderPlusMatrix_cubic
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    (hfree : ¬ containsC4 V G) {d : ℕ} (hd : 3 ≤ d) (hdeven : Even d)
    (hmin : d ≤ G.minDegree)
    (hcard : Fintype.card V = d * (d - 1) + 2) :
    evenFirstOrderPlusMatrix G * evenFirstOrderPlusMatrix G *
        evenFirstOrderPlusMatrix G =
      (4 * (Fintype.card V : ℤ) ^ 2 * (d - 2) : ℤ) •
        evenFirstOrderPlusMatrix G := by
  let A := G.adjMatrix ℤ
  let M := (antipodalGraph G).adjMatrix ℤ
  let J := FriendshipTheoremOQ01.onesMatrix V
  let N : ℤ := Fintype.card V
  let Q := (1 : Matrix V V ℤ) + M
  let R := N • Q - (2 : ℤ) • J
  have hsq : A * A =
      (↑d - 1 : ℤ) • (1 : Matrix V V ℤ) + J - M :=
    adjMatrix_sq_eq_sub_antipodalGraph_of_firstOrder_even
      G hfree hd hdeven hmin hcard
  have hcomm : A * M = M * A :=
    adjMatrix_comm_antipodalGraph_of_firstOrder_even
      G hfree hd hdeven hmin hcard
  have hM2 : M * M = (1 : Matrix V V ℤ) :=
    antipodalGraph_adjMatrix_sq_eq_one_of_firstOrder_even
      G hfree hd hdeven hmin hcard
  have hdegreeM : ∀ x : V, (antipodalGraph G).degree x = 1 := by
    intro x
    exact antipodalGraph_degree_eq_one_of_firstOrder_even
      G hfree hd hdeven hmin hcard x
  have hMJ : M * J = J := by
    have h := FriendshipTheoremOQ01.adjMatrix_mul_ones
      (antipodalGraph G) 1 hdegreeM
    simpa [M, J] using h
  have hJM : J * M = J := by
    have h := onesMatrix_mul_adjMatrix_of_regular
      (antipodalGraph G) 1 hdegreeM
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


/-- The even plus-space matrix has trace `-2d|V|`, hence nonzero. -/
theorem trace_evenFirstOrderPlusMatrix
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    (hfree : ¬ containsC4 V G) {d : ℕ} (hd : 3 ≤ d) (hdeven : Even d)
    (hmin : d ≤ G.minDegree)
    (hcard : Fintype.card V = d * (d - 1) + 2) :
    Matrix.trace (evenFirstOrderPlusMatrix G) =
      -(2 : ℤ) * d * Fintype.card V := by
  let A := G.adjMatrix ℤ
  let P := (antipodalGraph G).adjMatrix ℤ
  let J := FriendshipTheoremOQ01.onesMatrix V
  let N : ℤ := Fintype.card V
  have hAP := trace_adjMatrix_mul_antipodalGraph_of_firstOrder_even
    G hfree hd hdeven hmin hcard
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
  change Matrix.trace (A * (N • ((1 : Matrix V V ℤ) + P) - 2 • J)) =
    -2 * d * N
  rw [mul_sub, Matrix.mul_smul, mul_add, Matrix.mul_one]
  rw [Matrix.mul_smul, hAJ]
  rw [Matrix.trace_sub, Matrix.trace_smul, Matrix.trace_add,
    Matrix.trace_smul, SimpleGraph.trace_adjMatrix]
  rw [show Matrix.trace (A * P) = 0 by exact hAP]
  have htraceJ : Matrix.trace J = N := by
    simp [J, N, FriendshipTheoremOQ01.onesMatrix, Matrix.trace]
  rw [Matrix.trace_smul, htraceJ]
  ring

/-- Any prime divisor of `d-2` in an even first-order example must be
`2`.  This is the unconditional modular shadow of the expected square
condition on `d-2`. -/
theorem prime_eq_two_of_dvd_sub_two_of_firstOrder_even
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    (hfree : ¬ containsC4 V G) {d p : ℕ} (hd : 3 ≤ d) (hdeven : Even d)
    (hmin : d ≤ G.minDegree)
    (hcard : Fintype.card V = d * (d - 1) + 2)
    (hp : p.Prime) (hpdiv : p ∣ d - 2) :
    p = 2 := by
  have hpq : p ∣ 4 * (Fintype.card V) ^ 2 * (d - 2) := by
    exact dvd_mul_of_dvd_right hpdiv _
  have hpcubic := evenFirstOrderPlusMatrix_cubic
    G hfree hd hdeven hmin hcard
  have hptrace : (p : ℤ) ∣ Matrix.trace (evenFirstOrderPlusMatrix G) :=
    prime_dvd_trace_of_matrix_cubic (evenFirstOrderPlusMatrix G)
      hp hpq (by
        simpa only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat,
          Nat.cast_sub (by omega : 2 ≤ d)] using hpcubic)
  rw [trace_evenFirstOrderPlusMatrix G hfree hd hdeven hmin hcard] at hptrace
  have hpnat : p ∣ 2 * d * Fintype.card V := by
    have hz := hptrace
    rw [show -(2 : ℤ) * d * Fintype.card V =
      -(2 * d * Fintype.card V) by ring] at hz
    have hz' : (p : ℤ) ∣ 2 * (d : ℤ) * Fintype.card V :=
      dvd_neg.mp hz
    exact_mod_cast hz'
  have peq_of_dvd_two (hp2 : p ∣ 2) : p = 2 := by
    rcases (Nat.dvd_prime (by norm_num : Nat.Prime 2)).mp hp2 with hp1 | hp2eq
    · exact (hp.ne_one hp1).elim
    · exact hp2eq
  rcases hp.dvd_mul.mp hpnat with hp2d | hpN
  · rcases hp.dvd_mul.mp hp2d with hp2 | hpd
    · exact peq_of_dvd_two hp2
    · have hp2 : p ∣ 2 := by
        have hsub := Nat.dvd_sub hpd hpdiv
        have heq : d - (d - 2) = 2 := by omega
        rwa [heq] at hsub
      exact peq_of_dvd_two hp2
  · have hp4 : p ∣ 4 := by
      rw [hcard] at hpN
      have hprod : p ∣ (d + 1) * (d - 2) :=
        dvd_mul_of_dvd_right hpdiv _
      have hdiff : d * (d - 1) + 2 - (d + 1) * (d - 2) = 4 := by
        have h1 : d - 1 + 1 = d := Nat.sub_add_cancel (by omega)
        have h2 : d - 2 + 2 = d := Nat.sub_add_cancel (by omega)
        have heq : d * (d - 1) + 2 = (d + 1) * (d - 2) + 4 := by
          nlinarith
        omega
      rw [← hdiff]
      exact Nat.dvd_sub hpN hprod
    have hp2 : p ∣ 2 := hp.dvd_of_dvd_pow (n := 2) (by simpa using hp4)
    exact peq_of_dvd_two hp2

/-- Hence the even first-order template forces `d-2` to be a power of
two. -/
theorem sub_two_eq_two_pow_of_firstOrder_even
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    (hfree : ¬ containsC4 V G) {d : ℕ} (hd : 3 ≤ d) (hdeven : Even d)
    (hmin : d ≤ G.minDegree)
    (hcard : Fintype.card V = d * (d - 1) + 2) :
    ∃ k : ℕ, d - 2 = 2 ^ k := by
  refine ⟨(d - 2).primeFactorsList.length, ?_⟩
  apply Nat.eq_prime_pow_of_unique_prime_dvd (by omega)
  intro p hp hpdiv
  exact prime_eq_two_of_dvd_sub_two_of_firstOrder_even
    G hfree hd hdeven hmin hcard hp hpdiv

end Erdos85
