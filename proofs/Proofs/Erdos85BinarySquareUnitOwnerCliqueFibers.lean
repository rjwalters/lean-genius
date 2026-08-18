import Proofs.Erdos85BinarySquareUnitOwnerRank

/-!
# Clique fibers forced by a unit owner sector

Endpoint rigidity feeds back into the underlying owner graph: its reflexive
adjacency matrix is a scaled projection, forcing adjacency transitivity.
-/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- For a unit color, the reflexive owner adjacency satisfies `M²=qM`. -/
theorem binarySquare_regular_unit_ownerReflexiveAdj_mul_self
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) {q : ℕ} (hq : 3 ≤ q)
    (hreg : ∀ x, G.degree x = q)
    (hcard : Fintype.card V = q * q)
    (c : (secondOrderDefectGraph G).ConnectedComponent)
    (hc : c.supp.ncard = q) :
    let M : Matrix V V ℝ :=
      (componentOwnerGraph G (secondOrderDefectGraph G) c).adjMatrix ℝ +
        (1 : Matrix V V ℝ)
    M * M = (q : ℝ) • M := by
  dsimp
  let O := componentOwnerGraph G (secondOrderDefectGraph G) c
  let A := O.adjMatrix ℝ
  let M : Matrix V V ℝ := A + 1
  let J : Matrix V V ℝ := fun _ _ ↦ 1
  let C : Matrix V V ℝ := (q : ℝ) • M - J
  have hOreg : ∀ x, O.degree x = q - 1 := by
    have h := binarySquare_regular_componentOwnerGraph_degree
      G hfree hq hreg hcard c (m_c := 1) (by simpa using hc)
    simpa [O] using h
  have hMone : M.mulVec (Function.const V 1) =
      (q : ℝ) • Function.const V 1 := by
    rw [show M = O.adjMatrix ℝ + (1 : Matrix V V ℝ) by rfl,
      Matrix.add_mulVec, Matrix.one_mulVec]
    funext x
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rw [SimpleGraph.adjMatrix_mulVec_const_apply, mul_one, hOreg x,
      Nat.cast_sub (by omega : 1 ≤ q)]
    norm_num
  have hMJ : M * J = (q : ℝ) • J := by
    ext x y
    have hx := congrFun hMone x
    simpa [Matrix.mul_apply, Matrix.mulVec, dotProduct, J] using hx
  have hJM : J * M = (q : ℝ) • J := by
    have hMt : M.transpose = M := by
      simp [M, A, O]
    have hJt : J.transpose = J := by rfl
    calc
      J * M = (M * J).transpose := by rw [Matrix.transpose_mul, hMt, hJt]
      _ = ((q : ℝ) • J).transpose := by rw [hMJ]
      _ = (q : ℝ) • J := by simp [hJt]
  have hJJ : J * J = ((q : ℝ) ^ 2) • J := by
    ext x y
    simp [J, Matrix.mul_apply, hcard]
    ring
  have hproj : C * C = ((q : ℝ) ^ 2) • C := by
    simpa [C, M, A, O, J] using
      binarySquare_regular_unit_centeredOwnerGram_real_mul_self
        G hfree hq hreg hcard c hc
  dsimp [C] at hproj
  simp only [sub_mul, mul_sub, Matrix.smul_mul, Matrix.mul_smul] at hproj
  rw [hMJ, hJM, hJJ] at hproj
  have hq0 : (q : ℝ) ≠ 0 := by positivity
  ext x y
  have hxy := congrFun (congrFun hproj x) y
  simp only [Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul] at hxy ⊢
  have hfactor :
      (q : ℝ) ^ 2 * ((M * M) x y - (q : ℝ) * M x y) = 0 := by
    calc
      _ =
          ((q : ℝ) * ((q : ℝ) * (M * M) x y) -
              (q : ℝ) * ((q : ℝ) * J x y) -
                ((q : ℝ) * ((q : ℝ) * J x y) -
                  (q : ℝ) ^ 2 * J x y)) -
            (q : ℝ) ^ 2 * ((q : ℝ) * M x y - J x y) := by ring
      _ = 0 := sub_eq_zero.mpr hxy
  have hq2 : (q : ℝ) ^ 2 ≠ 0 := pow_ne_zero 2 hq0
  exact sub_eq_zero.mp ((mul_eq_zero.mp hfactor).resolve_left hq2)

/-- A unit owner graph has transitive adjacency: every length-two path whose
endpoints differ closes to a triangle.  Consequently its connected components
are cliques (and regularity makes them `K_q` fibers). -/
theorem binarySquare_regular_unit_componentOwnerGraph_adj_trans
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) {q : ℕ} (hq : 3 ≤ q)
    (hreg : ∀ x, G.degree x = q)
    (hcard : Fintype.card V = q * q)
    (c : (secondOrderDefectGraph G).ConnectedComponent)
    (hc : c.supp.ncard = q)
    {x y z : V}
    (hxy : (componentOwnerGraph G (secondOrderDefectGraph G) c).Adj x y)
    (hyz : (componentOwnerGraph G (secondOrderDefectGraph G) c).Adj y z)
    (hxz : x ≠ z) :
    (componentOwnerGraph G (secondOrderDefectGraph G) c).Adj x z := by
  let O := componentOwnerGraph G (secondOrderDefectGraph G) c
  let M : Matrix V V ℝ := O.adjMatrix ℝ + (1 : Matrix V V ℝ)
  have hquad : M * M = (q : ℝ) • M := by
    simpa [M, O] using
      binarySquare_regular_unit_ownerReflexiveAdj_mul_self
        G hfree hq hreg hcard c hc
  by_contra hnot
  have hxyO : O.Adj x y := by simpa [O] using hxy
  have hyzO : O.Adj y z := by simpa [O] using hyz
  have hnotO : ¬ O.Adj x z := by simpa [O] using hnot
  have hxzZero : M x z = 0 := by
    simp [M, SimpleGraph.adjMatrix_apply, hxz, hnotO]
  have hsumZero : ∑ w : V, M x w * M w z = 0 := by
    have hxzEntry := congrFun (congrFun hquad x) z
    rw [Matrix.mul_apply, Matrix.smul_apply, smul_eq_mul, hxzZero, mul_zero]
      at hxzEntry
    exact hxzEntry
  have hnonneg (w : V) : 0 ≤ M x w * M w z := by
    simp only [M, Matrix.add_apply, Matrix.one_apply,
      SimpleGraph.adjMatrix_apply]
    split_ifs <;> norm_num
  have hall := (Finset.sum_eq_zero_iff_of_nonneg
    (fun w _hw ↦ hnonneg w)).mp hsumZero
  have hyZero := hall y (Finset.mem_univ y)
  have hxyNe : x ≠ y := hxyO.ne
  have hyzNe : y ≠ z := hyzO.ne
  simp [M, SimpleGraph.adjMatrix_apply, hxyO, hyzO, hxyNe, hyzNe] at hyZero

/-- Distinct vertices of the self-indexed defect component lie in distinct
owner clique fibers: their closed owner neighborhoods are disjoint. -/
theorem binarySquare_regular_unit_selfComponent_closedOwnerNeighborhood_disjoint
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) {q : ℕ} (hq : 3 ≤ q)
    (hreg : ∀ x, G.degree x = q)
    (hcard : Fintype.card V = q * q)
    (c : (secondOrderDefectGraph G).ConnectedComponent)
    (hc : c.supp.ncard = q)
    {u v : V} (hu : u ∈ c.supp) (hv : v ∈ c.supp) (huv : u ≠ v) :
    Disjoint
      (insert u ((componentOwnerGraph G (secondOrderDefectGraph G) c).neighborFinset u))
      (insert v ((componentOwnerGraph G (secondOrderDefectGraph G) c).neighborFinset v)) := by
  let O := componentOwnerGraph G (secondOrderDefectGraph G) c
  have hucomp : (secondOrderDefectGraph G).connectedComponentMk u = c :=
    (SimpleGraph.ConnectedComponent.mem_supp_iff c u).mp hu
  have hvcomp : (secondOrderDefectGraph G).connectedComponentMk v = c :=
    (SimpleGraph.ConnectedComponent.mem_supp_iff c v).mp hv
  have hnotUV : ¬ O.Adj u v := by
    exact binarySquare_regular_sizeQ_component_not_componentOwnerGraph_adj
      G hfree hq hreg hcard c c (m_c := 1) (by simpa using hc) hc hucomp hvcomp
  rw [Finset.disjoint_left]
  intro w huw hwv
  simp only [Finset.mem_insert, SimpleGraph.mem_neighborFinset] at huw hwv
  rcases huw with rfl | huw
  · rcases hwv with huv' | hvu
    · exact huv huv'
    · exact hnotUV hvu.symm
  · rcases hwv with hwv | hwv
    · subst w
      exact hnotUV huw
    · apply hnotUV
      exact binarySquare_regular_unit_componentOwnerGraph_adj_trans
        G hfree hq hreg hcard c hc huw hwv.symm huv

/-- Every closed neighborhood of a unit owner graph has exactly `q` vertices,
so the disjoint fibers selected by the self component are `q`-sets. -/
theorem binarySquare_regular_unit_componentOwnerGraph_closedNeighborhood_card
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) {q : ℕ} (hq : 3 ≤ q)
    (hreg : ∀ x, G.degree x = q)
    (hcard : Fintype.card V = q * q)
    (c : (secondOrderDefectGraph G).ConnectedComponent)
    (hc : c.supp.ncard = q) (u : V) :
    (insert u
      ((componentOwnerGraph G (secondOrderDefectGraph G) c).neighborFinset u)).card = q := by
  let O := componentOwnerGraph G (secondOrderDefectGraph G) c
  have hOreg : O.degree u = q - 1 := by
    have h := binarySquare_regular_componentOwnerGraph_degree
      G hfree hq hreg hcard c (m_c := 1) (by simpa using hc)
    simpa [O] using h u
  have hnotmem : u ∉ O.neighborFinset u := by
    simp [SimpleGraph.mem_neighborFinset]
  rw [Finset.card_insert_of_notMem hnotmem, O.card_neighborFinset_eq_degree,
    hOreg]
  omega

end


end Erdos85
