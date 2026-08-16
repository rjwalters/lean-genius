import Proofs.Erdos85SquareOrderHighDifferenceQuadratic

/-!
# The doubled high-difference quadratic sector

Coordinate differences of high vertices are supported on the high sector,
whereas adjacency-row differences of high vertices vanish there.  The two
independent families therefore combine into one independent family of size
`2(|H|-1)`.  Adjacency exchanges the two halves, with product `d`.
-/

open SimpleGraph

namespace Erdos85

noncomputable section

def squareOrderHighQuadraticSectorFamily
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (H : Finset V) (a : V) :
    Sum {x // x ∈ H.erase a} {x // x ∈ H.erase a} → (V → ℚ)
  | Sum.inl b => coordinateDifferenceRat b.1 a
  | Sum.inr b => squareOrderHighRowDifferenceRat G b.1 a

theorem squareOrder_adjMatrixRat_mulVec_highQuadraticSectorFamily_inl
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (H : Finset V) (a : V) (b : {x // x ∈ H.erase a}) :
    (G.adjMatrix ℚ).mulVec
        (squareOrderHighQuadraticSectorFamily G H a (Sum.inl b)) =
      squareOrderHighQuadraticSectorFamily G H a (Sum.inr b) := by
  funext x
  simp only [squareOrderHighQuadraticSectorFamily, Matrix.mulVec, dotProduct,
    coordinateDifferenceRat, squareOrderHighRowDifferenceRat]
  simp_rw [mul_sub]
  rw [Finset.sum_sub_distrib]
  simp [G.adj_comm]

theorem squareOrder_adjMatrixRat_mulVec_highQuadraticSectorFamily_inr
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G)
    {d : Nat} (hd : 2 ≤ d) (hmin : ∀ x : V, d ≤ G.degree x)
    (hcard : Fintype.card V = d * d)
    (H : Finset V) (a : V) (b : {x // x ∈ H.erase a})
    (hb : G.degree b.1 = d + 1) (ha : G.degree a = d + 1) :
    (G.adjMatrix ℚ).mulVec
        (squareOrderHighQuadraticSectorFamily G H a (Sum.inr b)) =
      (d : ℚ) • squareOrderHighQuadraticSectorFamily G H a (Sum.inl b) := by
  funext x
  have hx := congrFun
    (squareOrder_adjMatrixRat_mulVec_highRowDifferenceRat
      G hfree hd hmin hcard hb ha) x
  simpa [squareOrderHighQuadraticSectorFamily, Pi.smul_apply] using hx

theorem squareOrder_adjMatrixRat_sq_mulVec_highQuadraticSectorFamily
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G)
    {d : Nat} (hd : 2 ≤ d) (hmin : ∀ x : V, d ≤ G.degree x)
    (hcard : Fintype.card V = d * d)
    {a : V} (ha : a ∈ squareOrderHighVertices G d)
    (i : Sum
      {x // x ∈ (squareOrderHighVertices G d).erase a}
      {x // x ∈ (squareOrderHighVertices G d).erase a}) :
    (G.adjMatrix ℚ).mulVec ((G.adjMatrix ℚ).mulVec
        (squareOrderHighQuadraticSectorFamily
          G (squareOrderHighVertices G d) a i)) =
      (d : ℚ) • squareOrderHighQuadraticSectorFamily
        G (squareOrderHighVertices G d) a i := by
  have haDegree : G.degree a = d + 1 := (Finset.mem_filter.mp ha).2
  cases i with
  | inl b =>
      rw [squareOrder_adjMatrixRat_mulVec_highQuadraticSectorFamily_inl]
      exact squareOrder_adjMatrixRat_mulVec_highQuadraticSectorFamily_inr
        G hfree hd hmin hcard _ a b
        (Finset.mem_filter.mp (Finset.mem_of_mem_erase b.2)).2 haDegree
  | inr b =>
      rw [squareOrder_adjMatrixRat_mulVec_highQuadraticSectorFamily_inr
        G hfree hd hmin hcard _ a b
        (Finset.mem_filter.mp (Finset.mem_of_mem_erase b.2)).2 haDegree]
      rw [Matrix.mulVec_smul,
        squareOrder_adjMatrixRat_mulVec_highQuadraticSectorFamily_inl]

def squareOrderAdjacencyQuadraticDefect
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (d : Nat) :
    (V → ℚ) →ₗ[ℚ] (V → ℚ) :=
  (G.adjMatrix ℚ).toLin' * (G.adjMatrix ℚ).toLin' -
    (d : ℚ) • LinearMap.id

theorem squareOrder_highQuadraticSectorFamily_mem_quadraticDefect_ker
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G)
    {d : Nat} (hd : 2 ≤ d) (hmin : ∀ x : V, d ≤ G.degree x)
    (hcard : Fintype.card V = d * d)
    {a : V} (ha : a ∈ squareOrderHighVertices G d)
    (i : Sum
      {x // x ∈ (squareOrderHighVertices G d).erase a}
      {x // x ∈ (squareOrderHighVertices G d).erase a}) :
    squareOrderHighQuadraticSectorFamily
        G (squareOrderHighVertices G d) a i ∈
      LinearMap.ker (squareOrderAdjacencyQuadraticDefect G d) := by
  rw [LinearMap.mem_ker]
  simp only [squareOrderAdjacencyQuadraticDefect, Module.End.mul_eq_comp,
    LinearMap.sub_apply, LinearMap.comp_apply, Matrix.toLin'_apply,
    LinearMap.smul_apply, LinearMap.id_coe, id_eq, sub_eq_zero]
  exact squareOrder_adjMatrixRat_sq_mulVec_highQuadraticSectorFamily
    G hfree hd hmin hcard ha i

theorem squareOrder_highQuadraticSectorFamily_linearIndependent
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G)
    {d : Nat} (hd : 2 ≤ d) (hmin : ∀ x : V, d ≤ G.degree x)
    (hcover : ∀ {u v}, G.Adj u v → G.degree u = d ∨ G.degree v = d)
    (hcard : Fintype.card V = d * d)
    {a : V} (ha : a ∈ squareOrderHighVertices G d) :
    LinearIndependent ℚ
      (squareOrderHighQuadraticSectorFamily
        G (squareOrderHighVertices G d) a) := by
  classical
  let H := squareOrderHighVertices G d
  let E := {x // x ∈ H.erase a}
  let coords : E → (V → ℚ) := fun b => coordinateDifferenceRat b.1 a
  let rows : E → (V → ℚ) := fun b => squareOrderHighRowDifferenceRat G b.1 a
  have hcoord : LinearIndependent ℚ coords := by
    simpa [H, E, coords] using coordinateDifferencesRat_linearIndependent H a
  have hrows : LinearIndependent ℚ rows := by
    simpa [H, E, rows] using
      squareOrder_highRowDifferencesRat_linearIndependent
        G hfree hd hmin hcard ha
  have hnotAdj : ∀ {x y : V}, x ∈ H → y ∈ H → ¬ G.Adj x y := by
    intro x y hx hy hxy
    exact squareOrder_not_adj_degree_succ_of_tightEdgeCover G hcover
      (Finset.mem_filter.mp hx).2 (Finset.mem_filter.mp hy).2 hxy
  rw [Fintype.linearIndependent_iff]
  intro g hg i
  have hleft : (∑ b : E, g (Sum.inl b) • coords b) = 0 := by
    funext x
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
    by_cases hx : x ∈ H
    · have hxg := congrFun hg x
      rw [Fintype.sum_sum_type] at hxg
      simp only [Pi.add_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
        Pi.zero_apply, squareOrderHighQuadraticSectorFamily] at hxg
      change (∑ b : E, g (Sum.inl b) * coords b x) +
          (∑ b : E, g (Sum.inr b) * rows b x) = 0 at hxg
      have hrowzero :
          (∑ b : E, g (Sum.inr b) * rows b x) = 0 := by
        apply Finset.sum_eq_zero
        intro b _hb
        have hbH : b.1 ∈ H := Finset.mem_of_mem_erase b.2
        have hba : ¬ G.Adj b.1 x := hnotAdj hbH hx
        have hax : ¬ G.Adj a x := hnotAdj ha hx
        simp [rows, squareOrderHighRowDifferenceRat,
          SimpleGraph.adjMatrix_apply, hba, hax]
      rw [hrowzero, add_zero] at hxg
      exact hxg
    ·
      apply Finset.sum_eq_zero
      intro b _hb
      have hbH : b.1 ∈ H := Finset.mem_of_mem_erase b.2
      have hxb : x ≠ b.1 := fun h => hx (h ▸ hbH)
      have hxa : x ≠ a := fun h => hx (h ▸ ha)
      simp [coords, coordinateDifferenceRat, hxb, hxa]
  have hgleft : ∀ b : E, g (Sum.inl b) = 0 :=
    Fintype.linearIndependent_iff.mp hcoord (fun b => g (Sum.inl b)) hleft
  have hright : (∑ b : E, g (Sum.inr b) • rows b) = 0 := by
    have hsplit := hg
    rw [Fintype.sum_sum_type] at hsplit
    have hleftzero : (∑ b : E, g (Sum.inl b) •
        squareOrderHighQuadraticSectorFamily G H a (Sum.inl b)) = 0 := by
      apply Finset.sum_eq_zero
      intro b _hb
      rw [hgleft b]
      simp
    rw [hleftzero, zero_add] at hsplit
    simpa [H, E, rows, squareOrderHighQuadraticSectorFamily] using hsplit
  have hgright : ∀ b : E, g (Sum.inr b) = 0 :=
    Fintype.linearIndependent_iff.mp hrows (fun b => g (Sum.inr b)) hright
  cases i with
  | inl b => exact hgleft b
  | inr b => exact hgright b

/-- The rational span of the doubled high-difference family is invariant under
the adjacency operator. -/
theorem squareOrder_highQuadraticSector_span_invariant
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G)
    {d : Nat} (hd : 2 ≤ d) (hmin : ∀ x : V, d ≤ G.degree x)
    (hcard : Fintype.card V = d * d)
    {a : V} (ha : a ∈ squareOrderHighVertices G d) :
    ∀ x ∈ Submodule.span ℚ
        (Set.range (squareOrderHighQuadraticSectorFamily
          G (squareOrderHighVertices G d) a)),
      (G.adjMatrix ℚ).toLin' x ∈ Submodule.span ℚ
        (Set.range (squareOrderHighQuadraticSectorFamily
          G (squareOrderHighVertices G d) a)) := by
  let S := Submodule.span ℚ
    (Set.range (squareOrderHighQuadraticSectorFamily
      G (squareOrderHighVertices G d) a))
  intro x hx
  have hle : S ≤ S.comap (G.adjMatrix ℚ).toLin' := by
    refine Submodule.span_le.mpr ?_
    intro y hy
    obtain ⟨i, rfl⟩ := hy
    cases i with
    | inl b =>
        change (G.adjMatrix ℚ).toLin'
            (squareOrderHighQuadraticSectorFamily
              G (squareOrderHighVertices G d) a (Sum.inl b)) ∈ S
        rw [Matrix.toLin'_apply,
          squareOrder_adjMatrixRat_mulVec_highQuadraticSectorFamily_inl]
        exact Submodule.subset_span (Set.mem_range_self (Sum.inr b))
    | inr b =>
        change (G.adjMatrix ℚ).toLin'
            (squareOrderHighQuadraticSectorFamily
              G (squareOrderHighVertices G d) a (Sum.inr b)) ∈ S
        rw [Matrix.toLin'_apply,
          squareOrder_adjMatrixRat_mulVec_highQuadraticSectorFamily_inr
            G hfree hd hmin hcard _ a b
            (Finset.mem_filter.mp (Finset.mem_of_mem_erase b.2)).2
            (Finset.mem_filter.mp ha).2]
        exact S.smul_mem (d : ℚ)
          (Submodule.subset_span (Set.mem_range_self (Sum.inl b)))
  exact hle hx

theorem squareOrder_highQuadraticSector_le_finrank_quadraticDefect_ker
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G)
    {d : Nat} (hd : 2 ≤ d) (hmin : ∀ x : V, d ≤ G.degree x)
    (hcover : ∀ {u v}, G.Adj u v → G.degree u = d ∨ G.degree v = d)
    (hcard : Fintype.card V = d * d)
    {a : V} (ha : a ∈ squareOrderHighVertices G d) :
    Fintype.card (Sum
        {x // x ∈ (squareOrderHighVertices G d).erase a}
        {x // x ∈ (squareOrderHighVertices G d).erase a}) ≤
      Module.finrank ℚ
        (LinearMap.ker (squareOrderAdjacencyQuadraticDefect G d)) := by
  let I := Sum
    {x // x ∈ (squareOrderHighVertices G d).erase a}
    {x // x ∈ (squareOrderHighVertices G d).erase a}
  let f : I → (V → ℚ) := squareOrderHighQuadraticSectorFamily
    G (squareOrderHighVertices G d) a
  let fker : I → LinearMap.ker (squareOrderAdjacencyQuadraticDefect G d) :=
    fun i => ⟨f i,
      squareOrder_highQuadraticSectorFamily_mem_quadraticDefect_ker
        G hfree hd hmin hcard ha i⟩
  have hf : LinearIndependent ℚ f := by
    simpa [I, f] using squareOrder_highQuadraticSectorFamily_linearIndependent
      G hfree hd hmin hcover hcard ha
  have hfker : LinearIndependent ℚ fker := by
    apply LinearIndependent.of_comp
      (LinearMap.ker (squareOrderAdjacencyQuadraticDefect G d)).subtype
    simpa [Function.comp_def, fker] using hf
  exact hfker.fintype_card_le_finrank

theorem squareOrder_twice_high_card_sub_one_le_finrank_quadraticDefect_ker
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G)
    {d : Nat} (hd : 2 ≤ d) (hmin : ∀ x : V, d ≤ G.degree x)
    (hcover : ∀ {u v}, G.Adj u v → G.degree u = d ∨ G.degree v = d)
    (hcard : Fintype.card V = d * d)
    {a : V} (ha : a ∈ squareOrderHighVertices G d) :
    2 * ((squareOrderHighVertices G d).card - 1) ≤
      Module.finrank ℚ
        (LinearMap.ker (squareOrderAdjacencyQuadraticDefect G d)) := by
  have h := squareOrder_highQuadraticSector_le_finrank_quadraticDefect_ker
    G hfree hd hmin hcover hcard ha
  have herase :
      Fintype.card {x // x ∈ (squareOrderHighVertices G d).erase a} =
        (squareOrderHighVertices G d).card - 1 := by
    rw [Fintype.card_coe, Finset.card_erase_of_mem ha]
  simpa only [Fintype.card_sum, herase, two_mul] using h

end

end Erdos85
