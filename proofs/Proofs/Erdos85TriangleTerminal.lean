import Proofs.Erdos85BinaryCycleIntertwiner
import Proofs.Erdos85BoundaryQuotientExcess
import Proofs.Erdos85QuadraticTrace

/-!
# Arithmetic collapse of the triangle terminal case

When every defect component is a triangle, the component quotient has zero
diagonal and satisfies `Q²=(d-3)I+3J`.  Its nonprincipal eigenvalues are
therefore `±√(d-3)`.  Since `trace Q=0`, irrational conjugate eigenvalues
would cancel and leave the principal eigenvalue `d`, an impossibility.  Thus
`d-3=t²`; the trace equation then makes `t` divide `d=t²+3`, hence `t|3`.
Only `d=4` and `d=12` remain.

This file isolates the terminal integer argument.  The graph-facing quotient
and characteristic-polynomial bridges are kept separate.
-/

namespace Erdos85

/-- The canonical projection onto the constant vectors of a nonempty finite
index type, written as a matrix. -/
noncomputable def normalizedOnesProjection (I : Type*) [Fintype I] :
    Matrix I I ℚ :=
  (Fintype.card I : ℚ)⁻¹ • Matrix.of (fun _ _ => 1)

theorem normalizedOnesProjection_mul_self
    (I : Type*) [Fintype I] [DecidableEq I] [Nonempty I] :
    normalizedOnesProjection I * normalizedOnesProjection I =
      normalizedOnesProjection I := by
  have hm : (Fintype.card I : ℚ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  apply Matrix.ext
  intro i j
  simp only [normalizedOnesProjection, Matrix.mul_apply,
    Matrix.smul_apply, Matrix.of_apply]
  rw [Finset.sum_const, Finset.card_univ]
  simp only [nsmul_eq_mul, smul_eq_mul, mul_one]
  field_simp

theorem normalizedOnesProjection_toLin_isIdempotent
    (I : Type*) [Fintype I] [DecidableEq I] [Nonempty I] :
    IsIdempotentElem (normalizedOnesProjection I).toLin' := by
  rw [IsIdempotentElem]
  simpa only [Module.End.mul_eq_comp, Matrix.toLin'_mul] using
    congrArg Matrix.toLin' (normalizedOnesProjection_mul_self I)

theorem Matrix.mul_normalizedOnesProjection_of_row_sum
    {I : Type*} [Fintype I] [DecidableEq I]
    (Q : Matrix I I ℚ) (d : ℕ)
    (hrow : ∀ i, ∑ j, Q i j = d) :
    Q * normalizedOnesProjection I =
      (d : ℚ) • normalizedOnesProjection I := by
  apply Matrix.ext
  intro i j
  simp only [Matrix.mul_apply, normalizedOnesProjection,
    Matrix.smul_apply, Matrix.of_apply, mul_one]
  simp only [smul_eq_mul, mul_one]
  calc
    (∑ x, Q i x * (Fintype.card I : ℚ)⁻¹) =
        (∑ x, Q i x) * (Fintype.card I : ℚ)⁻¹ :=
      (Finset.sum_mul (s := Finset.univ) (f := fun x => Q i x)
        (Fintype.card I : ℚ)⁻¹).symm
    _ = (d : ℚ) * (Fintype.card I : ℚ)⁻¹ := by rw [hrow]

theorem Matrix.normalizedOnesProjection_mul_of_col_sum
    {I : Type*} [Fintype I] [DecidableEq I]
    (Q : Matrix I I ℚ) (d : ℕ)
    (hcol : ∀ j, ∑ i, Q i j = d) :
    normalizedOnesProjection I * Q =
      (d : ℚ) • normalizedOnesProjection I := by
  apply Matrix.ext
  intro i j
  simp only [Matrix.mul_apply, normalizedOnesProjection,
    Matrix.smul_apply, Matrix.of_apply, one_mul]
  simp only [smul_eq_mul, mul_one]
  calc
    (∑ x, (Fintype.card I : ℚ)⁻¹ * Q x j) =
        (Fintype.card I : ℚ)⁻¹ * (∑ x, Q x j) :=
      (Finset.mul_sum (s := Finset.univ) (f := fun x => Q x j)
        (Fintype.card I : ℚ)⁻¹).symm
    _ = (Fintype.card I : ℚ)⁻¹ * d := by rw [hcol]
    _ = (d : ℚ) * (Fintype.card I : ℚ)⁻¹ := by ring

theorem normalizedOnesProjection_trace
    (I : Type*) [Fintype I] [DecidableEq I] [Nonempty I] :
    Matrix.trace (normalizedOnesProjection I) = 1 := by
  have hm : (Fintype.card I : ℚ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  simp only [normalizedOnesProjection, Matrix.trace, Matrix.diag,
    Matrix.smul_apply, Matrix.of_apply, Finset.sum_const,
    Finset.card_univ, nsmul_eq_mul, smul_eq_mul, mul_one]
  field_simp

theorem normalizedOnesProjection_ker_nontrivial
    (I : Type*) [Fintype I] [DecidableEq I]
    (hcard : 1 < Fintype.card I) :
    Nontrivial (LinearMap.ker (normalizedOnesProjection I).toLin') := by
  letI : Nontrivial I := Fintype.one_lt_card_iff_nontrivial.mp hcard
  let a : I := Classical.choice inferInstance
  let b : I := Classical.choose (exists_ne a)
  have hab : a ≠ b := (Classical.choose_spec (exists_ne a)).symm
  let v : I → ℚ := Pi.single a 1 - Pi.single b 1
  have hv : (normalizedOnesProjection I).toLin' v = 0 := by
    ext i
    simp only [normalizedOnesProjection, Matrix.toLin'_apply, Matrix.mulVec,
      dotProduct, Matrix.smul_apply, Matrix.of_apply, v, Pi.sub_apply,
      one_mul, smul_eq_mul]
    rw [← Finset.mul_sum]
    simp [Finset.sum_sub_distrib, hab]
  have hvne : v ≠ 0 := by
    intro hz
    have ha := congrFun hz a
    simp [v, hab] at ha
  exact ⟨⟨v, hv⟩, 0, by
    intro h
    apply hvne
    exact Subtype.ext_iff.mp h⟩

/-- A finite graph whose connected components all have order three has one
component for every three vertices. -/
theorem three_mul_card_connectedComponents_of_all_order_three
    {V : Type*} [Fintype V]
    (D : SimpleGraph V) [Fintype D.ConnectedComponent]
    (hthree : ∀ c : D.ConnectedComponent, c.supp.ncard = 3) :
    3 * Fintype.card D.ConnectedComponent = Fintype.card V := by
  classical
  have hparts : (∑ c : D.ConnectedComponent, c.supp.ncard) =
      Fintype.card V := by
    calc
      (∑ c : D.ConnectedComponent, c.supp.ncard) =
          ∑ c : D.ConnectedComponent, Fintype.card c.supp := by
            apply Finset.sum_congr rfl
            intro c hc
            simpa [Nat.card_eq_fintype_card] using
              (Nat.card_coe_set_eq c.supp).symm
      _ = Fintype.card (Σ c : D.ConnectedComponent, c.supp) :=
        Fintype.card_sigma.symm
      _ = Fintype.card V :=
        (Fintype.card_congr (vertexConnectedComponentEquiv D)).symm
  calc
    3 * Fintype.card D.ConnectedComponent =
        ∑ _c : D.ConnectedComponent, 3 := by simp [Nat.mul_comm]
    _ = ∑ c : D.ConnectedComponent, c.supp.ncard := by
      apply Finset.sum_congr rfl
      intro c hc
      rw [hthree c]
    _ = Fintype.card V := hparts

/-- Rational cast of the natural component quotient. -/
noncomputable def componentQuotientMatrixRat
    {V : Type*} [Fintype V] [DecidableEq V]
    (G D : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableEq D.ConnectedComponent] :
    Matrix D.ConnectedComponent D.ConnectedComponent ℚ :=
  fun c e => componentQuotientMatrix G D c e

/-- A nonnegative integral vector whose first and second moments agree is
binary.  Applied to a triangle-component quotient row, this says every block
degree is at most one. -/
theorem nat_le_one_of_sum_sq_eq_sum
    {I : Type*} [Fintype I] [DecidableEq I]
    (f : I → ℕ) (h : (∑ i, f i * f i) = ∑ i, f i) :
    ∀ i, f i ≤ 1 := by
  intro i
  by_contra hi
  have hi2 : 2 ≤ f i := by omega
  have hpoint : f i < f i * f i := by nlinarith
  have hrest : (∑ j ∈ Finset.univ.erase i, f j) ≤
      ∑ j ∈ Finset.univ.erase i, f j * f j := by
    apply Finset.sum_le_sum
    intro j hj
    nlinarith
  have hlt : (∑ j, f j) < ∑ j, f j * f j := by
    rw [← Finset.sum_erase_add _ _ (Finset.mem_univ i),
      ← Finset.sum_erase_add _ _ (Finset.mem_univ i)]
    exact Nat.add_lt_add_of_le_of_lt hrest hpoint
  omega

/-- If every second-order defect component is a triangle, every entry in the
component quotient is binary.  This is the graph-facing zero-excess step. -/
theorem secondOrder_triangleComponents_quotient_le_one
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) {d : ℕ} (hd : 4 ≤ d) (heven : Even d)
    (hmin : d ≤ G.minDegree)
    (hcard : Fintype.card V = d * (d - 1) + 3)
    (htri : ∀ c : (secondOrderDefectGraph G).ConnectedComponent,
      c.supp.ncard = 3) :
    ∀ c e, componentQuotientMatrix G (secondOrderDefectGraph G) c e ≤ 1 := by
  let D := secondOrderDefectGraph G
  let Q := componentQuotientMatrix G D
  have hsymm (c e : D.ConnectedComponent) : Q c e = Q e c := by
    have hbal := secondOrder_componentQuotientMatrix_balance
      G hfree hd heven hmin hcard c e
    change c.supp.ncard * Q c e = e.supp.ncard * Q e c at hbal
    rw [htri c, htri e] at hbal
    omega
  intro c e
  have hsq0 := secondOrder_componentQuotientMatrix_sq_apply
    G hfree hd heven hmin hcard c c
  have hsq : (∑ j, Q c j * Q c j) = d := by
    change (∑ j, Q c j * Q j c) =
      (d - 3) * (if c = c then 1 else 0) + c.supp.ncard at hsq0
    rw [htri c] at hsq0
    simp only [if_pos, mul_one] at hsq0
    have hrhs : d - 3 + 3 = d := by omega
    rw [hrhs] at hsq0
    rw [← hsq0]
    apply Finset.sum_congr rfl
    intro j hj
    rw [hsymm j c]
  have hrow : (∑ j, Q c j) = d :=
    sum_secondOrder_componentQuotientMatrix_row_eq_degree
      G hfree hd heven hmin hcard c
  exact nat_le_one_of_sum_sq_eq_sum (Q c) (hsq.trans hrow.symm) e

/-- The triangle-component quotient has zero diagonal: its entries are binary,
while the internal handshake parity says three times a diagonal entry is
even. -/
theorem secondOrder_triangleComponents_quotient_diagonal_zero
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) {d : ℕ} (hd : 4 ≤ d) (heven : Even d)
    (hmin : d ≤ G.minDegree)
    (hcard : Fintype.card V = d * (d - 1) + 3)
    (htri : ∀ c : (secondOrderDefectGraph G).ConnectedComponent,
      c.supp.ncard = 3) :
    ∀ c, componentQuotientMatrix G (secondOrderDefectGraph G) c c = 0 := by
  intro c
  have hle := secondOrder_triangleComponents_quotient_le_one
    G hfree hd heven hmin hcard htri c c
  have hevenDiag := secondOrder_componentQuotientMatrix_diagonal_mul_even
    G hfree hd heven hmin hcard c
  rw [htri c] at hevenDiag
  obtain ⟨k, hk⟩ := hevenDiag
  omega

/-- Over equal triangular defect components, the rational quotient is
symmetric. -/
theorem secondOrder_triangleComponents_quotientRat_symmetric
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) {d : ℕ} (hd : 4 ≤ d) (heven : Even d)
    (hmin : d ≤ G.minDegree)
    (hcard : Fintype.card V = d * (d - 1) + 3)
    (htri : ∀ c : (secondOrderDefectGraph G).ConnectedComponent,
      c.supp.ncard = 3) :
    (componentQuotientMatrixRat G (secondOrderDefectGraph G)).IsSymm := by
  rw [Matrix.IsSymm.ext_iff]
  intro c e
  have hbal := secondOrder_componentQuotientMatrix_balance
    G hfree hd heven hmin hcard c e
  rw [htri c, htri e] at hbal
  simp only [componentQuotientMatrixRat]
  exact_mod_cast (Nat.eq_of_mul_eq_mul_left (by norm_num : 0 < 3) hbal).symm

theorem secondOrder_triangleComponents_quotientRat_row_sum
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) {d : ℕ} (hd : 4 ≤ d) (heven : Even d)
    (hmin : d ≤ G.minDegree)
    (hcard : Fintype.card V = d * (d - 1) + 3) :
    ∀ c, ∑ e, componentQuotientMatrixRat G
      (secondOrderDefectGraph G) c e = d := by
  intro c
  simp only [componentQuotientMatrixRat, ← Nat.cast_sum]
  exact_mod_cast sum_secondOrder_componentQuotientMatrix_row_eq_degree
    G hfree hd heven hmin hcard c

theorem secondOrder_triangleComponents_quotientRat_trace_zero
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) {d : ℕ} (hd : 4 ≤ d) (heven : Even d)
    (hmin : d ≤ G.minDegree)
    (hcard : Fintype.card V = d * (d - 1) + 3)
    (htri : ∀ c : (secondOrderDefectGraph G).ConnectedComponent,
      c.supp.ncard = 3) :
    Matrix.trace (componentQuotientMatrixRat G
      (secondOrderDefectGraph G)) = 0 := by
  rw [Matrix.trace]
  apply Finset.sum_eq_zero
  intro c hc
  simp only [Matrix.diag, componentQuotientMatrixRat]
  exact_mod_cast secondOrder_triangleComponents_quotient_diagonal_zero
    G hfree hd heven hmin hcard htri c

theorem secondOrder_triangleComponents_quotientRat_sq
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) {d : ℕ} (hd : 4 ≤ d) (heven : Even d)
    (hmin : d ≤ G.minDegree)
    (hcard : Fintype.card V = d * (d - 1) + 3)
    (htri : ∀ c : (secondOrderDefectGraph G).ConnectedComponent,
      c.supp.ncard = 3) :
    let I := (secondOrderDefectGraph G).ConnectedComponent
    let Q := componentQuotientMatrixRat G (secondOrderDefectGraph G)
    Q * Q = ((d - 3 : ℕ) : ℚ) • (1 : Matrix I I ℚ) +
      (3 : ℚ) • Matrix.of (fun _ _ => 1) := by
  dsimp only
  apply Matrix.ext
  intro c e
  have hsq := secondOrder_componentQuotientMatrix_sq_apply
    G hfree hd heven hmin hcard c e
  rw [htri e] at hsq
  simp only [Matrix.mul_apply] at hsq
  simp only [Matrix.mul_apply, componentQuotientMatrixRat,
    Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply, Matrix.of_apply,
    smul_eq_mul, mul_one]
  exact_mod_cast hsq

/-- The final arithmetic step in the triangle-terminal quotient argument. -/
theorem triangleTerminal_degree_eq_four_or_twelve
    {d t p q : ℕ} (hd : 4 ≤ d)
    (hsq : t * t = d - 3)
    (htrace : d + p * t = q * t) : d = 4 ∨ d = 12 := by
  have hdform : d = t * t + 3 := by omega
  have htpos : 0 < t := by
    by_contra ht
    have : t = 0 := by omega
    subst t
    simp at hsq
    omega
  have htd : t ∣ d := by
    have hpt : t ∣ p * t := ⟨p, by ring⟩
    have hqt : t ∣ q * t := ⟨q, by ring⟩
    have hsum : t ∣ d + p * t := by rw [htrace]; exact hqt
    exact (Nat.dvd_add_iff_left hpt).mpr hsum
  have htt : t ∣ t * t := dvd_mul_right t t
  have ht3 : t ∣ 3 := by
    rw [hdform] at htd
    exact (Nat.dvd_add_iff_right htt).mpr htd
  have htle : t ≤ 3 := Nat.le_of_dvd (by norm_num) ht3
  interval_cases t <;> norm_num at ht3 <;> omega

/-- The same terminal arithmetic in the form naturally produced by the
rational eigenspace trace argument: the complementary trace `-d` is an
integral multiple of `t`. -/
theorem triangleTerminal_degree_eq_four_or_twelve_of_int_trace
    {d t : ℕ} {z : ℤ} (hd : 4 ≤ d)
    (hsq : t * t = d - 3)
    (htrace : -(d : ℚ) = (z : ℚ) * t) : d = 4 ∨ d = 12 := by
  have htpos : 0 < t := by
    by_contra ht
    have : t = 0 := by omega
    subst t
    simp at hsq
    omega
  have htraceZ : -(d : ℤ) = z * t := by exact_mod_cast htrace
  have htdZ : (t : ℤ) ∣ (d : ℤ) := by
    refine ⟨-z, ?_⟩
    calc
      (d : ℤ) = -(z * t) := by omega
      _ = (t : ℤ) * (-z) := by ring
  have htd : t ∣ d := Int.natCast_dvd_natCast.mp htdZ
  have hdform : d = t * t + 3 := by omega
  have htt : t ∣ t * t := dvd_mul_right t t
  have ht3 : t ∣ 3 := by
    rw [hdform] at htd
    exact (Nat.dvd_add_iff_right htt).mpr htd
  have htle : t ≤ 3 := Nat.le_of_dvd (by norm_num) ht3
  interval_cases t <;> norm_num at ht3 <;> omega

/-- Abstract spectral closure of the triangle terminal case.  A trace-zero
endomorphism has principal trace `d` on one invariant summand and squares to
`(d-3)I` on its nonzero complement.  Quadratic conjugacy first forces
`d-3` to be a square; the idempotent eigenspace projection then makes the
complementary trace an integral multiple of its square root. -/
theorem triangleTerminal_degree_eq_four_or_twelve_of_complementary_spaces
    {E : Type*} [AddCommGroup E] [Module ℚ E] [FiniteDimensional ℚ E]
    (A : E →ₗ[ℚ] E) (U W : Submodule ℚ E) [Nontrivial W]
    (hcompl : IsCompl U W)
    (hU : ∀ x ∈ U, A x ∈ U) (hW : ∀ x ∈ W, A x ∈ W)
    {d : ℕ} (hd : 4 ≤ d)
    (htrace : LinearMap.trace ℚ E A = 0)
    (hUtrace : LinearMap.trace ℚ U (A.restrict hU) = d)
    (hWsq : (A.restrict hW) * (A.restrict hW) =
      ((d - 3 : ℕ) : ℚ) • LinearMap.id) : d = 4 ∨ d = 12 := by
  have hsquare : IsSquare (d - 3) :=
    isSquare_of_complementary_traces_sq_nat
      A U W hcompl hU hW htrace d (by positivity) hUtrace (d - 3) hWsq
  obtain ⟨t, ht⟩ := hsquare
  have htpos : 0 < t := by
    by_contra htn
    have htzero : t = 0 := by omega
    subst t
    simp at ht
    omega
  have hsplit := trace_eq_add_trace_restrict_of_isCompl
    A U W hcompl hU hW
  have hWtrace : LinearMap.trace ℚ W (A.restrict hW) = -(d : ℚ) := by
    rw [htrace, hUtrace] at hsplit
    linarith
  have hWsq' : (A.restrict hW) * (A.restrict hW) =
      ((t * t : ℕ) : ℚ) • LinearMap.id := by
    calc
      (A.restrict hW) * (A.restrict hW) =
          ((d - 3 : ℕ) : ℚ) • LinearMap.id := hWsq
      _ = ((t * t : ℕ) : ℚ) • LinearMap.id := by rw [ht]
  obtain ⟨z, hz⟩ :=
    LinearMap.exists_int_mul_eq_trace_of_sq_eq_square_nat
      (A.restrict hW) t htpos hWsq'
  apply triangleTerminal_degree_eq_four_or_twelve_of_int_trace hd ht.symm
  rw [← hWtrace]
  exact hz

/-- Matrix-facing version of the abstract triangle-terminal closure.  It is
designed for the component quotient: `P` is the normalized all-ones
projection, so its range is the principal eigenspace and its kernel is the
zero-sum space. -/
theorem Matrix.triangleTerminal_degree_eq_four_or_twelve
    {I : Type*} [Fintype I] [DecidableEq I]
    (Q P : Matrix I I ℚ) {d : ℕ} (hd : 4 ≤ d)
    (hP : IsIdempotentElem P.toLin')
    (hcomm : Q.toLin' * P.toLin' = P.toLin' * Q.toLin')
    (htrace : Matrix.trace Q = 0)
    (hPtrace : LinearMap.trace ℚ (LinearMap.range P.toLin')
      (Q.toLin'.restrict (mapsTo_range_of_commute Q.toLin' P.toLin' hcomm)) = d)
    [Nontrivial (LinearMap.ker P.toLin')]
    (hkerSq :
      let hker := mapsTo_ker_of_commute Q.toLin' P.toLin' hcomm
      (Q.toLin'.restrict hker) * (Q.toLin'.restrict hker) =
        ((d - 3 : ℕ) : ℚ) • LinearMap.id) : d = 4 ∨ d = 12 := by
  let A := Q.toLin'
  let R := LinearMap.range P.toLin'
  let K := LinearMap.ker P.toLin'
  let hR := mapsTo_range_of_commute A P.toLin' hcomm
  let hK := mapsTo_ker_of_commute A P.toLin' hcomm
  apply triangleTerminal_degree_eq_four_or_twelve_of_complementary_spaces
    A R K (LinearMap.IsIdempotentElem.isCompl hP) hR hK hd
  · simpa [A, Matrix.trace_toLin'_eq] using htrace
  · simpa [A, R, hR] using hPtrace
  · simpa [A, K, hK] using hkerSq

/-- Quotient-matrix closure with the canonical all-ones projection.  The
only remaining hypothesis is the scalar-square identity on the zero-sum
space; row/column sums supply commutation and the principal trace. -/
theorem Matrix.triangleTerminal_degree_eq_four_or_twelve_of_row_col
    {I : Type*} [Fintype I] [DecidableEq I] [Nonempty I]
    (Q : Matrix I I ℚ) {d : ℕ} (hd : 4 ≤ d)
    (hcard : 1 < Fintype.card I)
    (hrow : ∀ i, ∑ j, Q i j = d)
    (hcol : ∀ j, ∑ i, Q i j = d)
    (htrace : Matrix.trace Q = 0)
    (hkerSq :
      let P := normalizedOnesProjection I
      let hcomm : Q.toLin' * P.toLin' = P.toLin' * Q.toLin' := by
        have hQP := Matrix.mul_normalizedOnesProjection_of_row_sum Q d hrow
        have hPQ := Matrix.normalizedOnesProjection_mul_of_col_sum Q d hcol
        have hm : Q * P = P * Q := hQP.trans hPQ.symm
        simpa only [Module.End.mul_eq_comp, Matrix.toLin'_mul] using
          congrArg Matrix.toLin' hm
      let hker := mapsTo_ker_of_commute Q.toLin' P.toLin' hcomm
      (Q.toLin'.restrict hker) * (Q.toLin'.restrict hker) =
        ((d - 3 : ℕ) : ℚ) • LinearMap.id) : d = 4 ∨ d = 12 := by
  let P := normalizedOnesProjection I
  have hQP := Matrix.mul_normalizedOnesProjection_of_row_sum Q d hrow
  have hPQ := Matrix.normalizedOnesProjection_mul_of_col_sum Q d hcol
  have hcommM : Q * P = P * Q := hQP.trans hPQ.symm
  have hcomm : Q.toLin' * P.toLin' = P.toLin' * Q.toLin' := by
    simpa only [Module.End.mul_eq_comp, Matrix.toLin'_mul] using
      congrArg Matrix.toLin' hcommM
  letI : Nontrivial (LinearMap.ker P.toLin') :=
    normalizedOnesProjection_ker_nontrivial I hcard
  have hPtrace : LinearMap.trace ℚ (LinearMap.range P.toLin')
      (Q.toLin'.restrict
        (mapsTo_range_of_commute Q.toLin' P.toLin' hcomm)) = d := by
    rw [trace_restrict_range_eq_trace_mul_of_idempotent
      Q.toLin' P.toLin' (normalizedOnesProjection_toLin_isIdempotent I) hcomm]
    have hlin := congrArg Matrix.toLin' hQP
    have hmul : Q.toLin' * P.toLin' = (d : ℚ) • P.toLin' := by
      simpa only [P, Module.End.mul_eq_comp, Matrix.toLin'_mul,
        map_smul] using hlin
    rw [hmul, map_smul]
    have hpt : LinearMap.trace ℚ (I → ℚ) P.toLin' = 1 := by
      rw [Matrix.trace_toLin'_eq]
      exact normalizedOnesProjection_trace I
    rw [hpt]
    simp
  apply Matrix.triangleTerminal_degree_eq_four_or_twelve
    Q P hd (normalizedOnesProjection_toLin_isIdempotent I)
    hcomm htrace hPtrace
  simpa [P, hcomm] using hkerSq

/-- On the kernel of the all-ones projection, an equation
`Q² = cI + kJ` reduces to the scalar equation `Q² = cI`. -/
theorem Matrix.restrict_ker_normalizedOnesProjection_sq
    {I : Type*} [Fintype I] [DecidableEq I] [Nonempty I]
    (Q : Matrix I I ℚ) (d : ℕ) (c k : ℚ)
    (hrow : ∀ i, ∑ j, Q i j = d)
    (hcol : ∀ j, ∑ i, Q i j = d)
    (hsq : Q * Q = c • (1 : Matrix I I ℚ) +
      k • Matrix.of (fun _ _ => 1)) :
    let P := normalizedOnesProjection I
    let hcomm : Q.toLin' * P.toLin' = P.toLin' * Q.toLin' := by
      have hQP := Matrix.mul_normalizedOnesProjection_of_row_sum
        Q d hrow
      have hPQ := Matrix.normalizedOnesProjection_mul_of_col_sum
        Q d hcol
      have hm : Q * P = P * Q := hQP.trans hPQ.symm
      simpa only [Module.End.mul_eq_comp, Matrix.toLin'_mul] using
        congrArg Matrix.toLin' hm
    let hker := mapsTo_ker_of_commute Q.toLin' P.toLin' hcomm
    (Q.toLin'.restrict hker) * (Q.toLin'.restrict hker) =
      c • LinearMap.id := by
  let P := normalizedOnesProjection I
  have hQP := Matrix.mul_normalizedOnesProjection_of_row_sum Q d hrow
  have hPQ := Matrix.normalizedOnesProjection_mul_of_col_sum Q d hcol
  have hcommM : Q * P = P * Q := hQP.trans hPQ.symm
  have hcomm : Q.toLin' * P.toLin' = P.toLin' * Q.toLin' := by
    simpa only [Module.End.mul_eq_comp, Matrix.toLin'_mul] using
      congrArg Matrix.toLin' hcommM
  let hker := mapsTo_ker_of_commute Q.toLin' P.toLin' hcomm
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  have hxP : P.toLin' x.1 = 0 := x.2
  let i : I := Classical.choice inferInstance
  have hsum : ∑ j, x.1 j = 0 := by
    have hi := congrFun hxP i
    simp only [P, normalizedOnesProjection, Matrix.toLin'_apply,
      Matrix.mulVec, dotProduct, Matrix.smul_apply, Matrix.of_apply,
      one_mul, Pi.zero_apply, smul_eq_mul] at hi
    rw [← Finset.mul_sum] at hi
    have hm : (Fintype.card I : ℚ) ≠ 0 := by
      exact_mod_cast Fintype.card_ne_zero
    field_simp at hi
    simpa using hi
  have hJx : (Matrix.of (fun _ _ : I => (1 : ℚ))).toLin' x.1 = 0 := by
    ext a
    simp [Matrix.toLin'_apply, Matrix.mulVec, dotProduct, hsum]
  have hsLin := congrArg Matrix.toLin' hsq
  have hsLin' : Q.toLin' * Q.toLin' =
      c • LinearMap.id + k • (Matrix.of (fun _ _ : I => (1 : ℚ))).toLin' := by
    simpa only [Module.End.mul_eq_comp, Matrix.toLin'_mul, map_add,
      map_smul, Matrix.toLin'_one] using hsLin
  have hx := LinearMap.congr_fun hsLin' x.1
  simp only [LinearMap.restrict_apply, Module.End.mul_apply,
    LinearMap.add_apply, LinearMap.smul_apply, LinearMap.id_apply, hJx,
    smul_zero, add_zero] at hx ⊢
  exact hx

/-- Complete graph-facing closure of the equal-triangle terminal case.  An
even second-order boundary graph whose defect components are all triangles
can only have degree four or twelve. -/
theorem secondOrder_triangleComponents_degree_eq_four_or_twelve
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) {d : ℕ} (hd : 4 ≤ d) (heven : Even d)
    (hmin : d ≤ G.minDegree)
    (hcard : Fintype.card V = d * (d - 1) + 3)
    (htri : ∀ c : (secondOrderDefectGraph G).ConnectedComponent,
      c.supp.ncard = 3) : d = 4 ∨ d = 12 := by
  let D := secondOrderDefectGraph G
  let I := D.ConnectedComponent
  let Q := componentQuotientMatrixRat G D
  have hparts : 3 * Fintype.card I = Fintype.card V :=
    three_mul_card_connectedComponents_of_all_order_three D htri
  have hIcard : 1 < Fintype.card I := by
    have hdm1 : 3 ≤ d - 1 := by omega
    have hprod : 12 ≤ d * (d - 1) := by
      calc
        12 = 4 * 3 := by norm_num
        _ ≤ d * (d - 1) := Nat.mul_le_mul hd hdm1
    rw [hcard] at hparts
    omega
  letI : Nonempty I := Fintype.card_pos_iff.mp (by omega)
  have hrow : ∀ i, ∑ j, Q i j = d :=
    secondOrder_triangleComponents_quotientRat_row_sum
      G hfree hd heven hmin hcard
  have hsym : Q.IsSymm :=
    secondOrder_triangleComponents_quotientRat_symmetric
      G hfree hd heven hmin hcard htri
  rw [Matrix.IsSymm.ext_iff] at hsym
  have hcol : ∀ j, ∑ i, Q i j = d := by
    intro j
    calc
      (∑ i, Q i j) = ∑ i, Q j i := by
        apply Finset.sum_congr rfl
        intro i hi
        exact hsym j i
      _ = d := hrow j
  have htrace : Matrix.trace Q = 0 :=
    secondOrder_triangleComponents_quotientRat_trace_zero
      G hfree hd heven hmin hcard htri
  have hsq : Q * Q = ((d - 3 : ℕ) : ℚ) • (1 : Matrix I I ℚ) +
      (3 : ℚ) • Matrix.of (fun _ _ => 1) :=
    secondOrder_triangleComponents_quotientRat_sq
      G hfree hd heven hmin hcard htri
  have hkerSq := Matrix.restrict_ker_normalizedOnesProjection_sq
    Q d ((d - 3 : ℕ) : ℚ) 3 hrow hcol hsq
  exact Matrix.triangleTerminal_degree_eq_four_or_twelve_of_row_col
    Q hd hIcard hrow hcol htrace hkerSq

end Erdos85
