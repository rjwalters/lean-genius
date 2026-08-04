import Proofs.Erdos85MooreFriendship

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

end Erdos85
