import Proofs.Erdos85ExcessDefectRegular
import Proofs.Erdos85ConflictDegreeAccounting

/-!
# The second-order defect operator without regularity

Regularity is needed only to make the diagonal term in the defect square
identity scalar.  For an arbitrary `C₄`-free graph one has

`A² = diag(degree - 1) + J - D`.

This is the operator interface for treating the thin nonregular degree bands
produced by `Erdos85DegreeExcessStratification`.
-/

open SimpleGraph

namespace Erdos85

/-- The diagonal matrix whose `x` entry is `degree x - 1`, over the
integers so that no truncated subtraction is involved. -/
def degreePredDiagonal {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] : Matrix V V ℤ :=
  Matrix.diagonal fun x ↦ (G.degree x : ℤ) - 1

@[simp] theorem degreePredDiagonal_apply_self
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (x : V) :
    degreePredDiagonal G x x = (G.degree x : ℤ) - 1 := by
  simp [degreePredDiagonal]

theorem degreePredDiagonal_apply_of_ne
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {x y : V} (hxy : x ≠ y) :
    degreePredDiagonal G x y = 0 := by
  simp [degreePredDiagonal, hxy]

/-- **Order-free nonregular defect matrix equation.** -/
theorem adjMatrix_sq_eq_degreePredDiagonal_add_ones_sub_secondOrderDefect
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) :
    G.adjMatrix ℤ * G.adjMatrix ℤ =
      degreePredDiagonal G + FriendshipTheoremOQ01.onesMatrix V -
        (secondOrderDefectGraph G).adjMatrix ℤ := by
  ext x y
  simp only [Matrix.add_apply, Matrix.sub_apply,
    FriendshipTheoremOQ01.onesMatrix, Matrix.of_apply]
  by_cases hxy : x = y
  · subst y
    rw [G.adjMatrix_mul_self_apply_self]
    simp [SimpleGraph.adjMatrix_apply]
  · rw [adjMatrix_sq_apply_eq_card_common,
      degreePredDiagonal_apply_of_ne G hxy]
    have hcommon := card_common_eq_if_secondOrderDefect G hfree x y hxy
    by_cases hdefect : y ∈ (secondOrderDefectGraph G).neighborFinset x
    · rw [if_pos hdefect] at hcommon
      have hadj : (secondOrderDefectGraph G).Adj x y :=
        ((secondOrderDefectGraph G).mem_neighborFinset x y).mp hdefect
      simp [SimpleGraph.adjMatrix_apply, hxy, hadj, hcommon]
    · rw [if_neg hdefect] at hcommon
      have hadj : ¬(secondOrderDefectGraph G).Adj x y := by
        intro hadj
        exact hdefect
          (((secondOrderDefectGraph G).mem_neighborFinset x y).mpr hadj)
      simp [SimpleGraph.adjMatrix_apply, hxy, hadj, hcommon]

/-- The familiar scalar regular identity is the specialization of the
nonregular diagonal identity. -/
theorem degreePredDiagonal_eq_smul_one_of_regular
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {d : ℕ} (hreg : ∀ x, G.degree x = d) :
    degreePredDiagonal G =
      (↑d - 1 : ℤ) • (1 : Matrix V V ℤ) := by
  ext x y
  by_cases hxy : x = y
  · subst y
    simp [degreePredDiagonal, hreg]
  · simp [degreePredDiagonal, hxy]

/-- Multiplication by the all-ones matrix records the row degree. -/
theorem adjMatrix_mul_onesMatrix_apply_eq_degree
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (x y : V) :
    (G.adjMatrix ℤ * FriendshipTheoremOQ01.onesMatrix V) x y =
      (G.degree x : ℤ) := by
  rw [Matrix.mul_apply]
  simp [FriendshipTheoremOQ01.onesMatrix,
    SimpleGraph.adjMatrix_apply, degree, neighborFinset_eq_filter,
    Finset.sum_boole]

/-- Multiplication on the other side records the column degree. -/
theorem onesMatrix_mul_adjMatrix_apply_eq_degree
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (x y : V) :
    (FriendshipTheoremOQ01.onesMatrix V * G.adjMatrix ℤ) x y =
      (G.degree y : ℤ) := by
  rw [Matrix.mul_apply]
  simp [FriendshipTheoremOQ01.onesMatrix,
    SimpleGraph.adjMatrix_apply, degree, neighborFinset_eq_filter,
    Finset.sum_boole, G.adj_comm]

/-- **Exact nonregular commutator.**  Failure of adjacency--defect
commutation is supported precisely on nonedges whose endpoints have different
degrees. -/
theorem adjMatrix_secondOrderDefect_commutator_apply
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) (x y : V) :
    (G.adjMatrix ℤ * (secondOrderDefectGraph G).adjMatrix ℤ -
        (secondOrderDefectGraph G).adjMatrix ℤ * G.adjMatrix ℤ) x y =
      ((G.degree x : ℤ) - G.degree y) *
        (1 - G.adjMatrix ℤ x y) := by
  let A := G.adjMatrix ℤ
  let D := (secondOrderDefectGraph G).adjMatrix ℤ
  let B := degreePredDiagonal G
  let J := FriendshipTheoremOQ01.onesMatrix V
  have hsq : A * A = B + J - D :=
    adjMatrix_sq_eq_degreePredDiagonal_add_ones_sub_secondOrderDefect
      G hfree
  have hD : D = B + J - A * A := by
    rw [hsq]
    noncomm_ring
  change (A * D - D * A) x y = _
  rw [hD]
  have hmatrix :
      A * (B + J - A * A) - (B + J - A * A) * A =
        (A * B - B * A) + (A * J - J * A) := by
    noncomm_ring
  rw [hmatrix]
  simp only [Matrix.add_apply, Matrix.sub_apply, B, degreePredDiagonal,
    Matrix.mul_diagonal, Matrix.diagonal_mul]
  rw [adjMatrix_mul_onesMatrix_apply_eq_degree G x y,
    onesMatrix_mul_adjMatrix_apply_eq_degree G x y]
  dsimp [A]
  ring

/-- If adjacency and defect commute, every nonadjacent pair has equal
degree. -/
theorem degree_eq_of_not_adj_of_adjMatrix_comm_secondOrderDefect
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G)
    (hcomm : G.adjMatrix ℤ * (secondOrderDefectGraph G).adjMatrix ℤ =
      (secondOrderDefectGraph G).adjMatrix ℤ * G.adjMatrix ℤ)
    {x y : V} (hxy : ¬ G.Adj x y) :
    G.degree x = G.degree y := by
  have hentry := congrFun (congrFun hcomm x) y
  have hformula :=
    adjMatrix_secondOrderDefect_commutator_apply G hfree x y
  have hzero :
      (G.adjMatrix ℤ * (secondOrderDefectGraph G).adjMatrix ℤ -
        (secondOrderDefectGraph G).adjMatrix ℤ * G.adjMatrix ℤ) x y = 0 := by
    rw [Matrix.sub_apply, hentry, sub_self]
  rw [hzero, SimpleGraph.adjMatrix_apply, if_neg hxy] at hformula
  simp only [sub_zero, mul_one] at hformula
  exact_mod_cast sub_eq_zero.mp hformula.symm

/-- Under the tight-edge cover, commuting defect and adjacency operators
force all non-tight vertices to have the same degree. -/
theorem degree_eq_of_nontight_of_nontight_of_comm
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) {d : ℕ}
    (hcover : ∀ {u v}, G.Adj u v → G.degree u = d ∨ G.degree v = d)
    (hcomm : G.adjMatrix ℤ * (secondOrderDefectGraph G).adjMatrix ℤ =
      (secondOrderDefectGraph G).adjMatrix ℤ * G.adjMatrix ℤ)
    {x y : V} (hx : G.degree x ≠ d) (hy : G.degree y ≠ d) :
    G.degree x = G.degree y := by
  apply degree_eq_of_not_adj_of_adjMatrix_comm_secondOrderDefect
    G hfree hcomm
  exact not_adj_of_degree_ne_of_degree_ne_of_tight_edge_cover
    G hcover hx hy

/-- A non-tight vertex is adjacent to every tight vertex whenever adjacency
and defect commute. -/
theorem adj_nontight_tight_of_comm
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) {d : ℕ}
    (hcomm : G.adjMatrix ℤ * (secondOrderDefectGraph G).adjMatrix ℤ =
      (secondOrderDefectGraph G).adjMatrix ℤ * G.adjMatrix ℤ)
    {x y : V} (hx : G.degree x ≠ d) (hy : G.degree y = d) :
    G.Adj x y := by
  by_contra hxy
  have heq := degree_eq_of_not_adj_of_adjMatrix_comm_secondOrderDefect
    G hfree hcomm hxy
  exact hx (heq.trans hy)

/-- **Commutation characterizes regularity in the edge-minimal regime.**
For minimum degree at least three, a `C₄`-free graph with the tight-edge
cover cannot be nonregular while its adjacency and defect operators commute.
Indeed, commutation would make a non-tight vertex adjacent to every tight
vertex.  A second non-tight vertex would then have too many common neighbors
with it; with only one non-tight vertex, any tight neighbor creates the same
contradiction. -/
theorem regular_of_adjMatrix_comm_secondOrderDefect_of_tight_edge_cover
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) {d : ℕ} (hd : 3 ≤ d)
    (hmin : ∀ x : V, d ≤ G.degree x)
    (hcover : ∀ {u v}, G.Adj u v → G.degree u = d ∨ G.degree v = d)
    (hcomm : G.adjMatrix ℤ * (secondOrderDefectGraph G).adjMatrix ℤ =
      (secondOrderDefectGraph G).adjMatrix ℤ * G.adjMatrix ℤ) :
    ∀ x : V, G.degree x = d := by
  intro x
  by_contra hx
  have hxgt : d < G.degree x := lt_of_le_of_ne (hmin x) (Ne.symm hx)
  have hneighborTight : ∀ {y : V}, G.Adj x y → G.degree y = d := by
    intro y hxy
    rcases hcover hxy with hxtight | hytight
    · exact (hx hxtight).elim
    · exact hytight
  have hunique : ∀ {z : V}, G.degree z ≠ d → z = x := by
    intro z hz
    by_contra hzx
    have hxzNot : ¬ G.Adj x z :=
      not_adj_of_degree_ne_of_degree_ne_of_tight_edge_cover
        G hcover hx hz
    have hsub : G.neighborFinset x ⊆
        G.neighborFinset x ∩ G.neighborFinset z := by
      intro y hy
      have hxy : G.Adj x y := (G.mem_neighborFinset x y).mp hy
      have hytight := hneighborTight hxy
      have hzy : G.Adj z y := adj_nontight_tight_of_comm
        G hfree hcomm hz hytight
      exact Finset.mem_inter.mpr
        ⟨hy, (G.mem_neighborFinset z y).mpr hzy⟩
    have hcardle := Finset.card_le_card hsub
    have hcommon := common_le_one_of_not_containsC4 hfree x z (Ne.symm hzx)
    rw [G.card_neighborFinset_eq_degree] at hcardle
    omega
  have hxpos : 0 < G.degree x := by omega
  obtain ⟨y, hy⟩ := Finset.card_pos.mp
    (show 0 < (G.neighborFinset x).card by
      rw [G.card_neighborFinset_eq_degree]
      exact hxpos)
  have hxy : G.Adj x y := (G.mem_neighborFinset x y).mp hy
  have hyxMem : x ∈ G.neighborFinset y :=
    (G.mem_neighborFinset y x).mpr hxy.symm
  have hytight : G.degree y = d := hneighborTight hxy
  have hxyNe : x ≠ y := G.ne_of_adj hxy
  have heraseSub : (G.neighborFinset y).erase x ⊆
      G.neighborFinset x ∩ G.neighborFinset y := by
    intro z hz
    have ⟨hzx, hyzMem⟩ := Finset.mem_erase.mp hz
    have hyz : G.Adj y z := (G.mem_neighborFinset y z).mp hyzMem
    have hztight : G.degree z = d := by
      by_contra hzNot
      have hzxEq := hunique hzNot
      exact hzx hzxEq
    have hxz : G.Adj x z := adj_nontight_tight_of_comm
      G hfree hcomm hx hztight
    exact Finset.mem_inter.mpr
      ⟨(G.mem_neighborFinset x z).mpr hxz, hyzMem⟩
  have heraseCard := Finset.card_le_card heraseSub
  have hcommon := common_le_one_of_not_containsC4 hfree x y hxyNe
  rw [Finset.card_erase_of_mem hyxMem,
    G.card_neighborFinset_eq_degree, hytight] at heraseCard
  omega

/-- In an edge-minimal `C₄`-free graph of minimum degree at least three,
adjacency--defect commutation is equivalent to regularity. -/
theorem adjMatrix_comm_secondOrderDefect_iff_regular_of_tight_edge_cover
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) {d : ℕ} (hd : 3 ≤ d)
    (hmin : ∀ x : V, d ≤ G.degree x)
    (hcover : ∀ {u v}, G.Adj u v → G.degree u = d ∨ G.degree v = d) :
    (G.adjMatrix ℤ * (secondOrderDefectGraph G).adjMatrix ℤ =
      (secondOrderDefectGraph G).adjMatrix ℤ * G.adjMatrix ℤ) ↔
      ∀ x : V, G.degree x = d := by
  constructor
  · exact regular_of_adjMatrix_comm_secondOrderDefect_of_tight_edge_cover
      G hfree hd hmin hcover
  · exact adjMatrix_comm_secondOrderDefect_of_regular G hfree

end Erdos85
