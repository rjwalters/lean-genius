import Proofs.Erdos85SquareOrderDefectEigenvectors
import Proofs.Erdos85SquareOrderHighQuadraticCharpoly

/-!
# The two-dimensional defect-incidence quotient at square order

The low-sector indicator `ℓ` and the high-incidence vector `k` span an
invariant sector for the defect adjacency operator:

`Dℓ = (d - 1)ℓ - k` and `Dk = hℓ - k`.

Consequently `k` is killed by
`D² - (d - 2)D + (h - d + 1)I`, whose discriminant is `d² - 4h`.
-/

open SimpleGraph

namespace Erdos85

noncomputable section

def squareOrderLowIndicatorRat
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (d : ℕ) : V → ℚ :=
  fun x => if G.degree x = d then 1 else 0

def squareOrderHighIncidenceRat
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (d : ℕ) : V → ℚ :=
  fun x => squareOrderHighIncidenceCount G d x

def squareOrderDefectIncidenceFamily
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (d : ℕ) : Bool → V → ℚ
  | false => squareOrderLowIndicatorRat G d
  | true => squareOrderHighIncidenceRat G d

/-- Two low vertices with different high incidences make the low indicator
and high-incidence vector linearly independent. -/
theorem squareOrder_defectIncidenceFamily_linearIndependent_of_heterogeneous
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] {d : ℕ}
    {x y : V} (hx : G.degree x = d) (hy : G.degree y = d)
    (hxy : squareOrderHighIncidenceCount G d x ≠
      squareOrderHighIncidenceCount G d y) :
    LinearIndependent ℚ (squareOrderDefectIncidenceFamily G d) := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro g hg i
  have hgx := congrFun hg x
  have hgy := congrFun hg y
  rw [Fintype.sum_bool] at hgx hgy
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply,
    squareOrderDefectIncidenceFamily, squareOrderLowIndicatorRat,
    squareOrderHighIncidenceRat, hx, hy, if_pos] at hgx hgy
  have htrue : g true = 0 := by
    by_contra hne
    have hkxy :
        (squareOrderHighIncidenceCount G d x : ℚ) =
          squareOrderHighIncidenceCount G d y := by
      apply (mul_left_cancel₀ hne)
      linarith
    exact hxy (by exact_mod_cast hkxy)
  have hfalse : g false = 0 := by
    simpa [htrue] using hgx
  cases i <;> assumption

theorem squareOrder_defect_mulVec_highIncidenceRat
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G)
    {d : ℕ} (hd : 2 ≤ d) (hmin : ∀ y : V, d ≤ G.degree y)
    (hcover : ∀ {u v}, G.Adj u v → G.degree u = d ∨ G.degree v = d)
    (hcard : Fintype.card V = d * d) :
    ((secondOrderDefectGraph G).adjMatrix ℚ).mulVec
        (squareOrderHighIncidenceRat G d) =
      (squareOrderHighVertices G d).card • squareOrderLowIndicatorRat G d -
        squareOrderHighIncidenceRat G d := by
  classical
  funext y
  rcases squareOrder_degree_eq_or_succ_of_tightEdgeCover
      G hfree hd hmin hcover hcard y with hy | hy
  · rw [SimpleGraph.adjMatrix_mulVec_apply]
    have hlocal := squareOrder_sum_highIncidence_over_defectNeighbors_add_self
      G hfree hd hmin hcard hy
    change
      (∑ x ∈ (secondOrderDefectGraph G).neighborFinset y,
          (squareOrderHighIncidenceCount G d x : ℚ)) =
        (squareOrderHighVertices G d).card *
            squareOrderLowIndicatorRat G d y -
          squareOrderHighIncidenceRat G d y
    simp only [squareOrderLowIndicatorRat, squareOrderHighIncidenceRat, hy,
      if_pos, mul_one]
    have hlocalQ := congrArg (fun n : ℕ => (n : ℚ)) hlocal
    push_cast at hlocalQ
    linarith
  · have hyDdegree : (secondOrderDefectGraph G).degree y = 0 :=
      (squareOrder_degree_succ_highRoot_structure
        G hfree hd hmin hcard hy).1
    have hyD : (secondOrderDefectGraph G).neighborFinset y = ∅ := by
      rw [← Finset.card_eq_zero,
        (secondOrderDefectGraph G).card_neighborFinset_eq_degree, hyDdegree]
    have hyIncidence : squareOrderHighIncidenceCount G d y = 0 :=
      squareOrder_highNeighborCount_eq_zero_of_high G hcover
        (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hy⟩)
    rw [SimpleGraph.adjMatrix_mulVec_apply]
    simp [hyD, squareOrderLowIndicatorRat, squareOrderHighIncidenceRat,
      hy, hyIncidence]

theorem squareOrder_defect_mulVec_lowIndicatorRat
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G)
    {d : ℕ} (hd : 2 ≤ d) (hmin : ∀ y : V, d ≤ G.degree y)
    (hcover : ∀ {u v}, G.Adj u v → G.degree u = d ∨ G.degree v = d)
    (hcard : Fintype.card V = d * d) :
    ((secondOrderDefectGraph G).adjMatrix ℚ).mulVec
        (squareOrderLowIndicatorRat G d) =
      (d - 1 : ℕ) • squareOrderLowIndicatorRat G d -
        squareOrderHighIncidenceRat G d := by
  classical
  let D := secondOrderDefectGraph G
  funext y
  rcases squareOrder_degree_eq_or_succ_of_tightEdgeCover
      G hfree hd hmin hcover hcard y with hy | hy
  · have hneighborLow : ∀ x ∈ D.neighborFinset y, G.degree x = d := by
      intro x hx
      rcases squareOrder_degree_eq_or_succ_of_tightEdgeCover
          G hfree hd hmin hcover hcard x with hxlow | hxhigh
      · exact hxlow
      · have hxzero : D.degree x = 0 :=
          (squareOrder_degree_succ_highRoot_structure
            G hfree hd hmin hcard hxhigh).1
        have hxy : D.Adj x y := by
          simpa [SimpleGraph.mem_neighborFinset, D.adj_comm] using hx
        have : 0 < D.degree x :=
          (D.degree_pos_iff_exists_adj x).mpr ⟨y, hxy⟩
        omega
    have hdegree := squareOrder_defectDegree_add_highIncidence_eq_pred
      G hfree hd hmin hcover hcard hy
    change D.degree y + squareOrderHighIncidenceCount G d y = d - 1 at hdegree
    rw [SimpleGraph.adjMatrix_mulVec_apply]
    change
      (∑ x ∈ D.neighborFinset y, squareOrderLowIndicatorRat G d x) =
        (d - 1 : ℕ) * squareOrderLowIndicatorRat G d y -
          squareOrderHighIncidenceRat G d y
    have hsum :
        (∑ x ∈ D.neighborFinset y, squareOrderLowIndicatorRat G d x) =
          (D.degree y : ℚ) := by
      calc
        _ = ∑ _x ∈ D.neighborFinset y, (1 : ℚ) := by
          apply Finset.sum_congr rfl
          intro x hx
          simp [squareOrderLowIndicatorRat, hneighborLow x hx]
        _ = (D.degree y : ℚ) := by simp [D.card_neighborFinset_eq_degree]
    rw [hsum]
    simp only [squareOrderLowIndicatorRat, squareOrderHighIncidenceRat, hy,
      if_pos, Nat.cast_sub (by omega : 1 ≤ d), Nat.cast_one,
      mul_one]
    have hdegreeQ := congrArg (fun n : ℕ => (n : ℚ)) hdegree
    push_cast at hdegreeQ
    rw [Nat.cast_sub (by omega : 1 ≤ d)] at hdegreeQ
    norm_num at hdegreeQ
    linarith
  · have hyDdegree : D.degree y = 0 :=
      (squareOrder_degree_succ_highRoot_structure
        G hfree hd hmin hcard hy).1
    have hyD : D.neighborFinset y = ∅ := by
      rw [← Finset.card_eq_zero, D.card_neighborFinset_eq_degree, hyDdegree]
    have hyIncidence : squareOrderHighIncidenceCount G d y = 0 :=
      squareOrder_highNeighborCount_eq_zero_of_high G hcover
        (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hy⟩)
    rw [SimpleGraph.adjMatrix_mulVec_apply]
    change
      (∑ x ∈ D.neighborFinset y, squareOrderLowIndicatorRat G d x) =
        (d - 1 : ℕ) * squareOrderLowIndicatorRat G d y -
          squareOrderHighIncidenceRat G d y
    rw [hyD]
    simp [squareOrderLowIndicatorRat, squareOrderHighIncidenceRat,
      hy, hyIncidence]

/-- The span of the low indicator and high-incidence vector is invariant
under the rational defect adjacency operator. -/
theorem squareOrder_defectIncidence_span_invariant
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G)
    {d : ℕ} (hd : 2 ≤ d) (hmin : ∀ y : V, d ≤ G.degree y)
    (hcover : ∀ {u v}, G.Adj u v → G.degree u = d ∨ G.degree v = d)
    (hcard : Fintype.card V = d * d) :
    ∀ v ∈ Submodule.span ℚ (Set.range (squareOrderDefectIncidenceFamily G d)),
      ((secondOrderDefectGraph G).adjMatrix ℚ).toLin' v ∈
        Submodule.span ℚ (Set.range (squareOrderDefectIncidenceFamily G d)) := by
  let S := Submodule.span ℚ
    (Set.range (squareOrderDefectIncidenceFamily G d))
  have hell := squareOrder_defect_mulVec_lowIndicatorRat
    G hfree hd hmin hcover hcard
  have hk := squareOrder_defect_mulVec_highIncidenceRat
    G hfree hd hmin hcover hcard
  intro v hv
  have hle : S ≤ S.comap ((secondOrderDefectGraph G).adjMatrix ℚ).toLin' := by
    refine Submodule.span_le.mpr ?_
    intro w hw
    obtain ⟨i, rfl⟩ := hw
    cases i with
    | false =>
        change ((secondOrderDefectGraph G).adjMatrix ℚ).toLin'
          (squareOrderDefectIncidenceFamily G d false) ∈ S
        rw [Matrix.toLin'_apply, squareOrderDefectIncidenceFamily, hell]
        exact S.sub_mem
          (S.nsmul_mem
            (Submodule.subset_span (Set.mem_range_self false)) (d - 1))
          (Submodule.subset_span (Set.mem_range_self true))
    | true =>
        change ((secondOrderDefectGraph G).adjMatrix ℚ).toLin'
          (squareOrderDefectIncidenceFamily G d true) ∈ S
        rw [Matrix.toLin'_apply, squareOrderDefectIncidenceFamily, hk]
        exact S.sub_mem
          (S.nsmul_mem
            (Submodule.subset_span (Set.mem_range_self false))
              (squareOrderHighVertices G d).card)
          (Submodule.subset_span (Set.mem_range_self true))
  exact hle hv

/-- In the heterogeneous branch the natural pair is a basis of its span. -/
noncomputable def squareOrderDefectIncidenceBasis
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] {d : ℕ}
    {x y : V} (hx : G.degree x = d) (hy : G.degree y = d)
    (hxy : squareOrderHighIncidenceCount G d x ≠
      squareOrderHighIncidenceCount G d y) :
    Module.Basis Bool ℚ
      (Submodule.span ℚ (Set.range (squareOrderDefectIncidenceFamily G d))) :=
  Module.Basis.span
    (squareOrder_defectIncidenceFamily_linearIndependent_of_heterogeneous
      G hx hy hxy)

def defectIncidenceQuotientMatrix (d h : ℚ) : Matrix Bool Bool ℚ
  | false, false => d - 1
  | true, false => -1
  | false, true => h
  | true, true => -1

theorem defectIncidenceQuotientMatrix_charpoly (d h : ℚ) :
    (defectIncidenceQuotientMatrix d h).charpoly =
      Polynomial.X ^ 2 - Polynomial.C (d - 2) * Polynomial.X +
        Polynomial.C (h - d + 1) := by
  unfold Matrix.charpoly
  rw [← Matrix.det_reindex_self finTwoEquiv.symm
    (defectIncidenceQuotientMatrix d h).charmatrix]
  rw [Matrix.det_fin_two]
  simp [Matrix.reindex_apply, defectIncidenceQuotientMatrix, finTwoEquiv]
  rw [Polynomial.C_ofNat]
  ring

theorem squareOrder_defectIncidence_restrict_basis_false
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G)
    {d : ℕ} (hd : 2 ≤ d) (hmin : ∀ y : V, d ≤ G.degree y)
    (hcover : ∀ {u v}, G.Adj u v → G.degree u = d ∨ G.degree v = d)
    (hcard : Fintype.card V = d * d)
    {x y : V} (hx : G.degree x = d) (hy : G.degree y = d)
    (hxy : squareOrderHighIncidenceCount G d x ≠
      squareOrderHighIncidenceCount G d y) :
    LinearMap.restrict ((secondOrderDefectGraph G).adjMatrix ℚ).toLin'
        (squareOrder_defectIncidence_span_invariant
          G hfree hd hmin hcover hcard)
        (squareOrderDefectIncidenceBasis G hx hy hxy false) =
      (d - 1 : ℕ) • squareOrderDefectIncidenceBasis G hx hy hxy false -
        squareOrderDefectIncidenceBasis G hx hy hxy true := by
  apply Subtype.ext
  simpa [squareOrderDefectIncidenceBasis, squareOrderDefectIncidenceFamily,
    Matrix.toLin'_apply] using
    squareOrder_defect_mulVec_lowIndicatorRat
      G hfree hd hmin hcover hcard

theorem squareOrder_defectIncidence_restrict_basis_true
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G)
    {d : ℕ} (hd : 2 ≤ d) (hmin : ∀ y : V, d ≤ G.degree y)
    (hcover : ∀ {u v}, G.Adj u v → G.degree u = d ∨ G.degree v = d)
    (hcard : Fintype.card V = d * d)
    {x y : V} (hx : G.degree x = d) (hy : G.degree y = d)
    (hxy : squareOrderHighIncidenceCount G d x ≠
      squareOrderHighIncidenceCount G d y) :
    LinearMap.restrict ((secondOrderDefectGraph G).adjMatrix ℚ).toLin'
        (squareOrder_defectIncidence_span_invariant
          G hfree hd hmin hcover hcard)
        (squareOrderDefectIncidenceBasis G hx hy hxy true) =
      (squareOrderHighVertices G d).card •
          squareOrderDefectIncidenceBasis G hx hy hxy false -
        squareOrderDefectIncidenceBasis G hx hy hxy true := by
  apply Subtype.ext
  simpa [squareOrderDefectIncidenceBasis, squareOrderDefectIncidenceFamily,
    Matrix.toLin'_apply] using
    squareOrder_defect_mulVec_highIncidenceRat
      G hfree hd hmin hcover hcard

theorem squareOrder_defectIncidence_restrict_toMatrix
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G)
    {d : ℕ} (hd : 2 ≤ d) (hmin : ∀ y : V, d ≤ G.degree y)
    (hcover : ∀ {u v}, G.Adj u v → G.degree u = d ∨ G.degree v = d)
    (hcard : Fintype.card V = d * d)
    {x y : V} (hx : G.degree x = d) (hy : G.degree y = d)
    (hxy : squareOrderHighIncidenceCount G d x ≠
      squareOrderHighIncidenceCount G d y) :
    let B := squareOrderDefectIncidenceBasis G hx hy hxy
    LinearMap.toMatrix B B
        (LinearMap.restrict ((secondOrderDefectGraph G).adjMatrix ℚ).toLin'
          (squareOrder_defectIncidence_span_invariant
            G hfree hd hmin hcover hcard)) =
      defectIncidenceQuotientMatrix (d : ℚ)
        ((squareOrderHighVertices G d).card : ℚ) := by
  classical
  dsimp only
  ext i j
  cases j with
  | false =>
      rw [LinearMap.toMatrix_apply,
        squareOrder_defectIncidence_restrict_basis_false
        G hfree hd hmin hcover hcard hx hy hxy]
      cases i <;>
        simp [defectIncidenceQuotientMatrix,
          Nat.cast_sub (by omega : 1 ≤ d)]
  | true =>
      rw [LinearMap.toMatrix_apply,
        squareOrder_defectIncidence_restrict_basis_true
        G hfree hd hmin hcover hcard hx hy hxy]
      cases i <;>
        simp [defectIncidenceQuotientMatrix]

/-- In the heterogeneous branch, the defect restriction to the incidence
sector has the explicit quadratic characteristic polynomial. -/
theorem squareOrder_defectIncidence_restrict_charpoly
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G)
    {d : ℕ} (hd : 2 ≤ d) (hmin : ∀ y : V, d ≤ G.degree y)
    (hcover : ∀ {u v}, G.Adj u v → G.degree u = d ∨ G.degree v = d)
    (hcard : Fintype.card V = d * d)
    {x y : V} (hx : G.degree x = d) (hy : G.degree y = d)
    (hxy : squareOrderHighIncidenceCount G d x ≠
      squareOrderHighIncidenceCount G d y) :
    LinearMap.charpoly
        (LinearMap.restrict ((secondOrderDefectGraph G).adjMatrix ℚ).toLin'
          (squareOrder_defectIncidence_span_invariant
            G hfree hd hmin hcover hcard)) =
      Polynomial.X ^ 2 - Polynomial.C ((d : ℚ) - 2) * Polynomial.X +
        Polynomial.C
          (((squareOrderHighVertices G d).card : ℚ) - d + 1) := by
  let B := squareOrderDefectIncidenceBasis G hx hy hxy
  rw [← LinearMap.charpoly_toMatrix
    (LinearMap.restrict ((secondOrderDefectGraph G).adjMatrix ℚ).toLin'
      (squareOrder_defectIncidence_span_invariant
        G hfree hd hmin hcover hcard)) B]
  rw [squareOrder_defectIncidence_restrict_toMatrix
    G hfree hd hmin hcover hcard hx hy hxy]
  exact defectIncidenceQuotientMatrix_charpoly
    (d : ℚ) ((squareOrderHighVertices G d).card : ℚ)

/-- The incidence quadratic divides the full rational defect characteristic
polynomial whenever the low incidence profile is heterogeneous. -/
theorem squareOrder_defectIncidenceQuadratic_dvd_defectCharpoly
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G)
    {d : ℕ} (hd : 2 ≤ d) (hmin : ∀ y : V, d ≤ G.degree y)
    (hcover : ∀ {u v}, G.Adj u v → G.degree u = d ∨ G.degree v = d)
    (hcard : Fintype.card V = d * d)
    {x y : V} (hx : G.degree x = d) (hy : G.degree y = d)
    (hxy : squareOrderHighIncidenceCount G d x ≠
      squareOrderHighIncidenceCount G d y) :
    Polynomial.X ^ 2 - Polynomial.C ((d : ℚ) - 2) * Polynomial.X +
        Polynomial.C
          (((squareOrderHighVertices G d).card : ℚ) - d + 1) ∣
      LinearMap.charpoly ((secondOrderDefectGraph G).adjMatrix ℚ).toLin' := by
  rw [← squareOrder_defectIncidence_restrict_charpoly
    G hfree hd hmin hcover hcard hx hy hxy]
  exact restrict_charpoly_dvd_charpoly
    ((secondOrderDefectGraph G).adjMatrix ℚ).toLin'
    (Submodule.span ℚ (Set.range (squareOrderDefectIncidenceFamily G d)))
    (squareOrder_defectIncidence_span_invariant
      G hfree hd hmin hcover hcard)

/-- In a positive heterogeneous high sector, the `-1` factor and incidence
quadratic are coprime and therefore their product divides the full rational
defect characteristic polynomial. -/
theorem squareOrder_combinedDefectFactors_dvd_defectCharpoly
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G)
    {d : ℕ} (hd : 2 ≤ d) (hmin : ∀ y : V, d ≤ G.degree y)
    (hcover : ∀ {u v}, G.Adj u v → G.degree u = d ∨ G.degree v = d)
    (hcard : Fintype.card V = d * d)
    {a x y : V} (ha : a ∈ squareOrderHighVertices G d)
    (hx : G.degree x = d) (hy : G.degree y = d)
    (hxy : squareOrderHighIncidenceCount G d x ≠
      squareOrderHighIncidenceCount G d y) :
    (Polynomial.X + 1) ^ ((squareOrderHighVertices G d).card - 1) *
        (Polynomial.X ^ 2 - Polynomial.C ((d : ℚ) - 2) * Polynomial.X +
          Polynomial.C
            (((squareOrderHighVertices G d).card : ℚ) - d + 1)) ∣
      LinearMap.charpoly ((secondOrderDefectGraph G).adjMatrix ℚ).toLin' := by
  let h : ℚ := (squareOrderHighVertices G d).card
  let L : Polynomial ℚ := Polynomial.X + 1
  let Q : Polynomial ℚ :=
    Polynomial.X ^ 2 - Polynomial.C ((d : ℚ) - 2) * Polynomial.X +
      Polynomial.C (h - d + 1)
  let R : Polynomial ℚ := Polynomial.X - Polynomial.C ((d : ℚ) - 1)
  have hhpos : 0 < (squareOrderHighVertices G d).card := by
    rw [Finset.card_pos]
    exact ⟨a, ha⟩
  have hhne : h ≠ 0 := by
    dsimp [h]
    exact_mod_cast (Nat.ne_of_gt hhpos)
  have hdecomp : Q = L * R + Polynomial.C h := by
    simp only [Q, L, R, map_sub, map_add, map_one, map_ofNat]
    ring
  have hcop : IsCoprime L Q := by
    refine ⟨-Polynomial.C h⁻¹ * R, Polynomial.C h⁻¹, ?_⟩
    rw [hdecomp]
    have hinv : h⁻¹ * h = 1 := inv_mul_cancel₀ hhne
    calc
      -Polynomial.C h⁻¹ * R * L +
          Polynomial.C h⁻¹ * (L * R + Polynomial.C h) =
          Polynomial.C h⁻¹ * Polynomial.C h := by ring
      _ = Polynomial.C (h⁻¹ * h) := by rw [Polynomial.C_mul]
      _ = 1 := by rw [hinv, Polynomial.C_1]
  have hminus := squareOrder_defectMinusOneFactor_dvd_defectCharpoly
    G hfree hd hmin hcover hcard ha
  have hquad := squareOrder_defectIncidenceQuadratic_dvd_defectCharpoly
    G hfree hd hmin hcover hcard hx hy hxy
  change L ^ ((squareOrderHighVertices G d).card - 1) * Q ∣ _
  exact hcop.pow_left.mul_dvd hminus hquad

theorem squareOrder_defect_incidence_quadratic
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G)
    {d : ℕ} (hd : 2 ≤ d) (hmin : ∀ y : V, d ≤ G.degree y)
    (hcover : ∀ {u v}, G.Adj u v → G.degree u = d ∨ G.degree v = d)
    (hcard : Fintype.card V = d * d) :
    let D := (secondOrderDefectGraph G).adjMatrix ℚ
    let k := squareOrderHighIncidenceRat G d
    let h := (squareOrderHighVertices G d).card
    D.mulVec (D.mulVec k) - (d - 2 : ℕ) • D.mulVec k +
        (h + 1 - d : ℤ) • k = 0 := by
  classical
  let D := (secondOrderDefectGraph G).adjMatrix ℚ
  let ell := squareOrderLowIndicatorRat G d
  let k := squareOrderHighIncidenceRat G d
  let h := (squareOrderHighVertices G d).card
  dsimp only
  have hk := squareOrder_defect_mulVec_highIncidenceRat
    G hfree hd hmin hcover hcard
  have hell := squareOrder_defect_mulVec_lowIndicatorRat
    G hfree hd hmin hcover hcard
  change D.mulVec k = h • ell - k at hk
  change D.mulVec ell = (d - 1 : ℕ) • ell - k at hell
  rw [hk, Matrix.mulVec_sub, Matrix.mulVec_smul, hell, hk]
  funext x
  have hdq : ((d - 2 : ℕ) : ℚ) = (d : ℚ) - 2 := by
    rw [Nat.cast_sub (by omega : 2 ≤ d)]
    norm_num
  have hd1q : ((d - 1 : ℕ) : ℚ) = (d : ℚ) - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ d)]
    norm_num
  simp only [Pi.sub_apply, Pi.add_apply, nsmul_eq_mul, zsmul_eq_mul,
    Pi.mul_apply, Pi.natCast_apply, Pi.intCast_apply]
  rw [hdq, hd1q]
  push_cast
  simp only [k, h, Pi.zero_apply]
  ring

end

end Erdos85
