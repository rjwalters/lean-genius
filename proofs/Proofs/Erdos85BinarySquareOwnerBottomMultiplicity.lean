import Proofs.Erdos85BinarySquareCenteredOwnerRank
import Proofs.Erdos85BinarySquareComponentIncidenceSelf

/-!
# Exact bottom multiplicity of every owner color

The uncentered incidence block of a defect component has full column rank:
its Gram matrix is the connected-component Laplacian plus the all-ones
matrix.  Its row Gram is the shifted owner adjacency matrix.  Consequently
an owner belonging to a component of order `q m` has shifted rank exactly
`q m`, and bottom eigenvalue `-m` with multiplicity exactly `q²-qm`.
-/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- The real ambient-by-component neighbor-incidence matrix. -/
def realDefectComponentNeighborIncidenceMatrix
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (c : (secondOrderDefectGraph G).ConnectedComponent) :
    Matrix V c.supp ℝ :=
  (defectComponentNeighborIncidenceMatrix (K := ℤ) G c).map
    (Int.castRingHom ℝ)

private theorem lapMatrix_map_intCast_ownerBottom
    {W : Type*} [Fintype W] [DecidableEq W]
    (H : SimpleGraph W) [DecidableRel H.Adj] :
    (H.lapMatrix ℤ).map (Int.castRingHom ℝ) = H.lapMatrix ℝ := by
  ext x y
  simp only [SimpleGraph.lapMatrix, SimpleGraph.degMatrix,
    Matrix.map_apply, Matrix.sub_apply, Matrix.diagonal_apply,
    SimpleGraph.adjMatrix_apply]
  split_ifs <;> norm_num

/-- The real incidence self-Gram is `L + J` on the induced defect
component. -/
theorem transpose_realDefectComponentNeighborIncidenceMatrix_mul_self_eq
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) {q : ℕ} (hq : 3 ≤ q)
    (hreg : ∀ x, G.degree x = q)
    (hcard : Fintype.card V = q * q)
    (c : (secondOrderDefectGraph G).ConnectedComponent) :
    (realDefectComponentNeighborIncidenceMatrix G c).transpose *
        realDefectComponentNeighborIncidenceMatrix G c =
      ((secondOrderDefectGraph G).induce c.supp).lapMatrix ℝ +
        Matrix.of (fun _ _ => (1 : ℝ)) := by
  have hz := transpose_defectComponentNeighborIncidenceMatrix_mul_self
    G hfree (by omega : 1 ≤ q) hreg c
  have hr := congrArg
    (fun M : Matrix c.supp c.supp ℤ => M.map (Int.castRingHom ℝ)) hz
  have hlap := congrArg
    (fun M : Matrix c.supp c.supp ℤ => M.map (Int.castRingHom ℝ))
    (binarySquare_regular_inducedDefectComponent_lapMatrix_eq
      G hfree hq hreg hcard c)
  rw [lapMatrix_map_intCast_ownerBottom] at hlap
  rw [hlap]
  have hr' :
      (realDefectComponentNeighborIncidenceMatrix G c).transpose *
          realDefectComponentNeighborIncidenceMatrix G c =
        (((((q - 1 : ℕ) : ℤ) • (1 : Matrix c.supp c.supp ℤ) +
            Matrix.of (fun _ _ => (1 : ℤ))) -
          ((secondOrderDefectGraph G).induce c.supp).adjMatrix ℤ).map
            (Int.castRingHom ℝ)) := by
    have hleft :
        ((defectComponentNeighborIncidenceMatrix (K := ℤ) G c).transpose *
            defectComponentNeighborIncidenceMatrix (K := ℤ) G c).map
              (Int.castRingHom ℝ) =
          (realDefectComponentNeighborIncidenceMatrix G c).transpose *
            realDefectComponentNeighborIncidenceMatrix G c := by
      rw [Matrix.map_mul, Matrix.transpose_map]
      rfl
    exact hleft.symm.trans hr
  rw [hr']
  ext x y
  simp only [Matrix.map_apply, Matrix.add_apply,
    Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply,
    Matrix.of_apply, map_add, map_sub]
  norm_num
  ring

/-- The uncentered component-incidence block has full column rank. -/
theorem realDefectComponentNeighborIncidenceMatrix_rank
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) {q : ℕ} (hq : 3 ≤ q)
    (hreg : ∀ x, G.degree x = q)
    (hcard : Fintype.card V = q * q)
    (c : (secondOrderDefectGraph G).ConnectedComponent) :
    (realDefectComponentNeighborIncidenceMatrix G c).rank =
      Fintype.card c.supp := by
  let D := secondOrderDefectGraph G
  let H := D.induce c.supp
  let I := realDefectComponentNeighborIncidenceMatrix G c
  let L := H.lapMatrix ℝ
  let J : Matrix c.supp c.supp ℝ := Matrix.of fun _ _ => 1
  letI : Nonempty c.supp := Set.nonempty_coe_sort.mpr c.nonempty_supp
  have hgram : I.transpose * I = L + J := by
    simpa [I, L, J, H, D] using
      transpose_realDefectComponentNeighborIncidenceMatrix_mul_self_eq
        G hfree hq hreg hcard c
  have hker : LinearMap.ker I.mulVecLin = ⊥ := by
    ext v
    constructor
    · intro hv
      rw [Submodule.mem_bot]
      have hIv : I.mulVec v = 0 := by
        simpa [LinearMap.mem_ker, Matrix.mulVecLin_apply] using hv
      have hgramv : (L + J).mulVec v = 0 := by
        rw [← hgram, ← Matrix.mulVec_mulVec, hIv, Matrix.mulVec_zero]
      have hsumL (w : c.supp → ℝ) : ∑ x, (L.mulVec w) x = 0 := by
        let one : c.supp → ℝ := fun _ => 1
        have hLone : L.mulVec one = 0 := by
          exact H.lapMatrix_mulVec_const_eq_zero
        have heq : one ⬝ᵥ (L.mulVec w) = 0 := by
          rw [Matrix.dotProduct_mulVec]
          have hsymm : L.transpose = L := (H.isSymm_lapMatrix ℝ).eq
          rw [← hsymm, Matrix.vecMul_transpose, hLone,
            zero_dotProduct]
        simpa [dotProduct, one] using heq
      have hsumv : ∑ x, v x = 0 := by
        have hs := congrArg (fun w : c.supp → ℝ => ∑ x, w x) hgramv
        simp only [Matrix.add_mulVec, Pi.add_apply, Pi.zero_apply,
          Finset.sum_add_distrib, Finset.sum_const_zero] at hs
        rw [hsumL] at hs
        have hJ (x : c.supp) : (J.mulVec v) x = ∑ y, v y := by
          simp [J, Matrix.mulVec, dotProduct]
        simp_rw [hJ] at hs
        simp only [Finset.sum_const] at hs
        have hs' : (Fintype.card c.supp : ℝ) * (∑ y, v y) = 0 := by
          simpa [nsmul_eq_mul] using hs
        have hcne : (Fintype.card c.supp : ℝ) ≠ 0 := by positivity
        exact (mul_eq_zero.mp hs').resolve_left hcne
      have hJv : J.mulVec v = 0 := by
        funext x
        simp [J, Matrix.mulVec, dotProduct, hsumv]
      have hLv : L.mulVec v = 0 := by
        rw [Matrix.add_mulVec, hJv, add_zero] at hgramv
        exact hgramv
      have hconst : ∀ x y : c.supp, v x = v y := by
        intro x y
        exact (H.lapMatrix_mulVec_eq_zero_iff_forall_reachable.mp hLv)
          x y (c.connected_toSimpleGraph x y)
      let x₀ : c.supp := Classical.choice inferInstance
      have hvbase : v x₀ = 0 := by
        have hs : ∑ x, v x = Fintype.card c.supp * v x₀ := by
          calc
            ∑ x, v x = ∑ _x : c.supp, v x₀ :=
              Finset.sum_congr rfl fun x _ => hconst x x₀
            _ = Fintype.card c.supp * v x₀ := by simp
        rw [hs] at hsumv
        exact (mul_eq_zero.mp hsumv).resolve_left (by positivity)
      funext x
      rw [Pi.zero_apply, hconst x x₀, hvbase]
    · intro hv
      rw [Submodule.mem_bot] at hv
      subst v
      exact LinearMap.map_zero _
  have hrankNull := LinearMap.finrank_range_add_finrank_ker I.mulVecLin
  rw [hker] at hrankNull
  simp at hrankNull
  rw [Matrix.rank]
  simpa [Module.finrank_fintype_fun_eq_card ℝ] using hrankNull

/-- The row Gram of the uncentered incidence block is exactly the owner
adjacency matrix shifted by its bottom-eigenvalue magnitude. -/
theorem realDefectComponentNeighborIncidenceMatrix_mul_transpose_eq_ownerShift
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
    realDefectComponentNeighborIncidenceMatrix G c *
        (realDefectComponentNeighborIncidenceMatrix G c).transpose =
      (componentOwnerGraph G (secondOrderDefectGraph G) c).adjMatrix ℝ +
        (m_c : ℝ) • (1 : Matrix V V ℝ) := by
  let D := secondOrderDefectGraph G
  let IZ := defectComponentNeighborIncidenceMatrix (K := ℤ) G c
  let O := componentOwnerGraph G D c
  have hgram : IZ * IZ.transpose =
      G.adjMatrix ℤ * defectComponentDiagonalMatrix D c * G.adjMatrix ℤ := by
    ext x y
    rw [Matrix.mul_apply,
      adjMatrix_mul_defectComponentDiagonalMatrix_mul_adjMatrix_apply]
    simp only [IZ, Matrix.transpose_apply,
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
        simp_rw [show ∀ z : V,
            (if D.connectedComponentMk z = c then
                if G.Adj x z then if G.Adj y z then (1 : ℤ) else 0 else 0
              else 0) =
              if D.connectedComponentMk z = c ∧ G.Adj x z ∧ G.Adj y z
                then 1 else 0 by
          intro z
          by_cases hc' : D.connectedComponentMk z = c <;>
            by_cases hx : G.Adj x z <;> by_cases hy : G.Adj y z <;>
              simp [hc', hx, hy]]
        rw [Finset.sum_boole]
        have hfilter : (Finset.univ : Finset V).filter
            (fun z => D.connectedComponentMk z = c ∧ G.Adj x z ∧ G.Adj y z) =
            componentNeighborFinset G D c x ∩
              componentNeighborFinset G D c y := by
          ext z
          simp [componentNeighborFinset, SimpleGraph.mem_neighborFinset,
            and_assoc, and_left_comm, and_comm]
        rw [hfilter]
  have howner := binarySquare_regular_componentOwnerGraph_adjMatrix_eq
    G hfree hq hreg hcard c hc
  have hz : IZ * IZ.transpose = O.adjMatrix ℤ +
      (m_c : ℤ) • (1 : Matrix V V ℤ) := by
    rw [hgram, howner]
    module
  have hr := congrArg
    (fun M : Matrix V V ℤ => M.map (Int.castRingHom ℝ)) hz
  have hleft : (IZ * IZ.transpose).map (Int.castRingHom ℝ) =
      realDefectComponentNeighborIncidenceMatrix G c *
        (realDefectComponentNeighborIncidenceMatrix G c).transpose := by
    rw [Matrix.map_mul, Matrix.transpose_map]
    rfl
  rw [hleft] at hr
  have hright :
      (O.adjMatrix ℤ + (m_c : ℤ) • (1 : Matrix V V ℤ)).map
          (Int.castRingHom ℝ) =
        O.adjMatrix ℝ + (m_c : ℝ) • (1 : Matrix V V ℝ) := by
    ext x y
    change (((O.adjMatrix ℤ x y + (m_c : ℤ) *
        (if x = y then 1 else 0) : ℤ) : ℝ)) =
      O.adjMatrix ℝ x y + (m_c : ℝ) * (if x = y then 1 else 0)
    by_cases hxy : x = y <;>
      simp [SimpleGraph.adjMatrix_apply, hxy]
  exact hr.trans hright

/-- **Exact shifted-owner rank.**  An owner belonging to a component of order
`q m_c` has shifted rank exactly `q m_c`. -/
theorem binarySquare_regular_real_componentOwnerGraph_shift_rank
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
    ((componentOwnerGraph G (secondOrderDefectGraph G) c).adjMatrix ℝ +
      (m_c : ℝ) • (1 : Matrix V V ℝ)).rank = q * m_c := by
  let I := realDefectComponentNeighborIncidenceMatrix G c
  rw [← realDefectComponentNeighborIncidenceMatrix_mul_transpose_eq_ownerShift
    G hfree hq hreg hcard c hc, Matrix.rank_self_mul_transpose]
  rw [realDefectComponentNeighborIncidenceMatrix_rank
    G hfree hq hreg hcard c, Set.fintypeCard_eq_ncard, hc]

/-- **Exact bottom multiplicity.**  The owner eigenvalue `-m_c` has
multiplicity exactly `q²-qm_c`. -/
theorem binarySquare_regular_finrank_componentOwnerGraph_bottom_kernel_real
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
    Module.finrank ℝ (LinearMap.ker
      ((componentOwnerGraph G (secondOrderDefectGraph G) c).adjMatrix ℝ +
        (m_c : ℝ) • (1 : Matrix V V ℝ)).mulVecLin) =
      q * q - q * m_c := by
  let M := (componentOwnerGraph G (secondOrderDefectGraph G) c).adjMatrix ℝ +
    (m_c : ℝ) • (1 : Matrix V V ℝ)
  have hrank : M.rank = q * m_c :=
    binarySquare_regular_real_componentOwnerGraph_shift_rank
      G hfree hq hreg hcard c hc
  have hnull := LinearMap.finrank_range_add_finrank_ker M.mulVecLin
  have hnull' : q * m_c +
      Module.finrank ℝ (LinearMap.ker M.mulVecLin) = q * q := by
    calc
      _ = M.rank + Module.finrank ℝ (LinearMap.ker M.mulVecLin) := by rw [hrank]
      _ = Module.finrank ℝ (V → ℝ) := hnull
      _ = Fintype.card V := Module.finrank_fintype_fun_eq_card ℝ
      _ = q * q := hcard
  have hle : q * m_c ≤ q * q := by
    rw [← hc, ← hcard]
    simpa using Set.ncard_le_ncard (Set.subset_univ c.supp)
  have hexact : Module.finrank ℝ (LinearMap.ker M.mulVecLin) =
      q * q - q * m_c := by omega
  simpa [M] using hexact

/-- At order `64`, every normalized size-two owner has bottom eigenvalue
`-2` with multiplicity exactly `48`. -/
theorem orderSixtyFour_sizeSixteen_componentOwnerGraph_bottom_multiplicity
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G)
    (hreg : ∀ x, G.degree x = 8)
    (hcard : Fintype.card V = 64)
    (c : (secondOrderDefectGraph G).ConnectedComponent)
    (hc : c.supp.ncard = 16) :
    Module.finrank ℝ (LinearMap.ker
      ((componentOwnerGraph G (secondOrderDefectGraph G) c).adjMatrix ℝ +
        (2 : ℝ) • (1 : Matrix V V ℝ)).mulVecLin) = 48 := by
  simpa using
    (binarySquare_regular_finrank_componentOwnerGraph_bottom_kernel_real
      G hfree (q := 8) (by omega) hreg (by simpa using hcard) c
        (m_c := 2) (by simpa using hc))

end

end Erdos85
