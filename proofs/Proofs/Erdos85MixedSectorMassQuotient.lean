import Proofs.Erdos85MixedNonsquareMass
import Proofs.Erdos85DifferenceArrayBoundary

/-!
# Quotient interpretation of the mixed selected-sector anchor mass
-/

namespace Erdos85

noncomputable section

open SimpleGraph

/-- Trace splitting through an arbitrary rank-one idempotent.  This is the
weighted analogue of the normalized-ones argument used in the equal-cycle
quotient theorem. -/
theorem LinearMap.trace_eq_scalar_of_idempotent_nonsquare
    {E : Type*} [AddCommGroup E] [Module ℚ E] [FiniteDimensional ℚ E]
    (Q P : E →ₗ[ℚ] E) (d k : ℚ) (a : ℕ)
    (hP : IsIdempotentElem P) (hcomm : Q * P = P * Q)
    (hQP : Q * P = d • P) (htraceP : LinearMap.trace ℚ E P = 1)
    (ha : ¬ IsSquare a)
    (hQsq : Q * Q = (a : ℚ) • LinearMap.id + k • P) :
    LinearMap.trace ℚ E Q = d := by
  let R := LinearMap.range P
  let W := LinearMap.ker P
  let hR := mapsTo_range_of_commute Q P hcomm
  let hW := mapsTo_ker_of_commute Q P hcomm
  have hRtrace : LinearMap.trace ℚ R (Q.restrict hR) = d := by
    rw [trace_restrict_range_eq_trace_mul_of_idempotent Q P hP hcomm,
      hQP, map_smul, htraceP, smul_eq_mul, mul_one]
  have hWsq : (Q.restrict hW) * (Q.restrict hW) =
      (a : ℚ) • LinearMap.id := by
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    have hs := LinearMap.congr_fun hQsq x
    have hx := x.property
    rw [LinearMap.mem_ker] at hx
    simpa [LinearMap.restrict_apply, Module.End.mul_apply, hx] using hs
  have hWtrace : LinearMap.trace ℚ W (Q.restrict hW) = 0 := by
    cases subsingleton_or_nontrivial W with
    | inl hsub =>
        letI : Subsingleton W := hsub
        have hz : Q.restrict hW = 0 := Subsingleton.elim _ _
        rw [hz]
        simp
    | inr hntriv =>
        letI : Nontrivial W := hntriv
        exact LinearMap.trace_eq_zero_of_sq_eq_nonsquare_nat
          (Q.restrict hW) a ha hWsq
  have hsplit := trace_eq_add_trace_restrict_of_isCompl Q R W
    (LinearMap.IsIdempotentElem.isCompl hP) hR hW
  rw [hRtrace, hWtrace, add_zero] at hsplit
  exact hsplit

/-- Rank-one projection onto the constant vector, normalized by an arbitrary
nonzero weight vector. -/
def weightedConstantProjection {I : Type*} [Fintype I]
    (r : I → ℚ) : Matrix I I ℚ :=
  fun _ j ↦ r j / ∑ i, r i

theorem weightedConstantProjection_isIdempotent
    {I : Type*} [Fintype I] [DecidableEq I]
    (r : I → ℚ) (hR : (∑ i, r i) ≠ 0) :
    IsIdempotentElem (weightedConstantProjection r) := by
  rw [IsIdempotentElem]
  ext i j
  simp only [Matrix.mul_apply, weightedConstantProjection]
  rw [← Finset.sum_mul, ← Finset.sum_div]
  simp [div_self hR]

theorem weightedConstantProjection_trace
    {I : Type*} [Fintype I] [DecidableEq I]
    (r : I → ℚ) (hR : (∑ i, r i) ≠ 0) :
    Matrix.trace (weightedConstantProjection r) = 1 := by
  rw [Matrix.trace]
  simp only [Matrix.diag, weightedConstantProjection]
  rw [← Finset.sum_div]
  exact (div_self hR)

/-- A quotient with constant row sum, weighted left eigenvector, and the
Moore rank-one square equation has trace equal to its principal eigenvalue
when the transverse scalar is nonsquare. -/
theorem Matrix.trace_eq_degree_of_sq_weightedRankOne_of_nonsquare
    {I : Type*} [Fintype I] [DecidableEq I]
    (Q : Matrix I I ℚ) (r : I → ℚ) (d : ℚ) (a : ℕ)
    (hR : (∑ i, r i) ≠ 0)
    (hrow : ∀ i, ∑ j, Q i j = d)
    (hleft : ∀ j, ∑ i, r i * Q i j = d * r j)
    (hsq : Q * Q = (a : ℚ) • (1 : Matrix I I ℚ) +
      Matrix.of (fun _ j ↦ r j))
    (ha : ¬ IsSquare a) : Matrix.trace Q = d := by
  let P := weightedConstantProjection r
  have hPmat : IsIdempotentElem P :=
    weightedConstantProjection_isIdempotent r hR
  have hQPmat : Q * P = d • P := by
    ext i j
    simp only [Matrix.mul_apply, P, weightedConstantProjection,
      Matrix.smul_apply, smul_eq_mul]
    rw [← Finset.sum_mul, hrow]
  have hPQmat : P * Q = d • P := by
    ext i j
    simp only [Matrix.mul_apply, P, weightedConstantProjection,
      Matrix.smul_apply, smul_eq_mul]
    simp_rw [div_mul_eq_mul_div]
    rw [← Finset.sum_div, hleft]
    ring
  have hcommMat : Q * P = P * Q := hQPmat.trans hPQmat.symm
  have hrank : Matrix.of (fun _ j ↦ r j) = (∑ i, r i) • P := by
    ext i j
    simp only [Matrix.of_apply, Matrix.smul_apply, smul_eq_mul, P,
      weightedConstantProjection]
    field_simp
  have hP : IsIdempotentElem P.toLin' := by
    rw [IsIdempotentElem]
    simpa only [Module.End.mul_eq_comp, Matrix.toLin'_mul] using
      congrArg Matrix.toLin' hPmat
  have hQP : Q.toLin' * P.toLin' = d • P.toLin' := by
    have h := congrArg Matrix.toLin' hQPmat
    simpa [Module.End.mul_eq_comp, Matrix.toLin'_mul, map_smul] using h
  have hcomm : Q.toLin' * P.toLin' = P.toLin' * Q.toLin' := by
    have h := congrArg Matrix.toLin' hcommMat
    simpa [Module.End.mul_eq_comp, Matrix.toLin'_mul] using h
  have htraceP : LinearMap.trace ℚ (I → ℚ) P.toLin' = 1 := by
    rw [Matrix.trace_toLin'_eq]
    exact weightedConstantProjection_trace r hR
  have hQsq : Q.toLin' * Q.toLin' =
      (a : ℚ) • LinearMap.id + (∑ i, r i) • P.toLin' := by
    have h := congrArg Matrix.toLin' hsq
    rw [hrank] at h
    simpa [Module.End.mul_eq_comp, Matrix.toLin'_mul, Matrix.toLin'_one,
      map_add, map_smul] using h
  have htrace := LinearMap.trace_eq_scalar_of_idempotent_nonsquare
    Q.toLin' P.toLin' d (∑ i, r i) a hP hcomm hQP htraceP ha hQsq
  simpa [Matrix.trace_toLin'_eq] using htrace

/-- Without any common-component-order hypothesis, the natural second-order
component quotient has trace `d` in the nonsquare branch.  Detailed balance
provides the weighted left eigenvector needed by the rank-one trace lemma. -/
theorem secondOrder_componentQuotient_trace_eq_degree_of_nonsquare
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) {d : ℕ}
    (hd : 4 ≤ d) (heven : Even d) (hmin : d ≤ G.minDegree)
    (hcard : Fintype.card V = d * (d - 1) + 3)
    (hnonsquare : ¬ IsSquare (d - 3)) :
    ∑ c, componentQuotientMatrix G (secondOrderDefectGraph G) c c = d := by
  let D := secondOrderDefectGraph G
  let I := D.ConnectedComponent
  let Q := componentQuotientMatrixRat G D
  let r : I → ℚ := fun c ↦ c.supp.ncard
  letI : Nonempty V := Fintype.card_pos_iff.mp (by rw [hcard]; omega)
  letI : Nonempty I :=
    ⟨D.connectedComponentMk (Classical.choice (inferInstance : Nonempty V))⟩
  have hparts : (∑ c : I, c.supp.ncard) = Fintype.card V := by
    calc
      (∑ c : I, c.supp.ncard) =
          ∑ c : I, Fintype.card c.supp := by
        apply Finset.sum_congr rfl
        intro c _
        simpa [Nat.card_eq_fintype_card] using
          (Nat.card_coe_set_eq c.supp).symm
      _ = Fintype.card (Σ c : I, c.supp) := Fintype.card_sigma.symm
      _ = Fintype.card V :=
        (Fintype.card_congr (vertexConnectedComponentEquiv D)).symm
  have hR : (∑ c : I, r c) ≠ 0 := by
    have hpartsQ : (∑ c : I, r c) = (Fintype.card V : ℚ) := by
      simp only [r]
      exact_mod_cast hparts
    rw [hpartsQ]
    exact_mod_cast (Fintype.card_ne_zero : Fintype.card V ≠ 0)
  have hrow : ∀ c : I, ∑ e, Q c e = (d : ℚ) := by
    intro c
    simp only [Q, D, componentQuotientMatrixRat]
    exact_mod_cast sum_secondOrder_componentQuotientMatrix_row_eq_degree
      G hfree hd heven hmin hcard c
  have hleft : ∀ e : I, ∑ c, r c * Q c e = (d : ℚ) * r e := by
    intro e
    calc
      ∑ c, r c * Q c e = ∑ c, r e * Q e c := by
        apply Finset.sum_congr rfl
        intro c _
        simp only [r, Q, D, componentQuotientMatrixRat]
        exact_mod_cast secondOrder_componentQuotientMatrix_balance
          G hfree hd heven hmin hcard c e
      _ = r e * ∑ c, Q e c := by rw [Finset.mul_sum]
      _ = (d : ℚ) * r e := by rw [hrow]; ring
  have hsq : Q * Q = ((d - 3 : ℕ) : ℚ) • (1 : Matrix I I ℚ) +
      Matrix.of (fun _ e ↦ r e) := by
    ext c e
    have hs := secondOrder_componentQuotientMatrix_sq_apply
      G hfree hd heven hmin hcard c e
    simp only [Matrix.mul_apply, Q, componentQuotientMatrixRat,
      Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply,
      Matrix.of_apply, r, smul_eq_mul] at hs ⊢
    exact_mod_cast hs
  have htrace := Matrix.trace_eq_degree_of_sq_weightedRankOne_of_nonsquare
    Q r (d : ℚ) (d - 3) hR hrow hleft hsq hnonsquare
  rw [Matrix.trace] at htrace
  have htraceQ : (∑ c : I,
      (componentQuotientMatrix G D c c : ℚ)) = d := by
    simpa only [Q, Matrix.diag, componentQuotientMatrixRat] using htrace
  exact_mod_cast htraceQ

/-- The selected-sector anchor mass is exactly the partial diagonal trace of
the second-order component quotient over the `p`-divisible components. -/
theorem pDivisibleAnchorMass_eq_sum_diagonalQuotient
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    [∀ c : (secondOrderDefectGraph G).ConnectedComponent,
      NeZero c.supp.ncard]
    (hfree : ¬ containsC4 V G) {d p : ℕ}
    (hd : 4 ≤ d) (heven : Even d) (hmin : d ≤ G.minDegree)
    (hcard : Fintype.card V = d * (d - 1) + 3)
    (u : ∀ c : (secondOrderDefectGraph G).ConnectedComponent,
      ZMod c.supp.ncard → V)
    (hu : ∀ c, Function.Injective (u c))
    (huRange : ∀ c, Set.range (u c) = c.supp) :
    pDivisibleAnchorMass G u p =
      ∑ c ∈ Finset.univ.filter (fun c :
        (secondOrderDefectGraph G).ConnectedComponent ↦ p ∣ c.supp.ncard),
          componentQuotientMatrix G (secondOrderDefectGraph G) c c := by
  unfold pDivisibleAnchorMass
  apply Finset.sum_congr rfl
  intro c hc
  exact card_graphCycleBlockZeroSupport_eq_componentQuotient G hfree hd
    heven hmin hcard c c (u c) (u c) (hu c) (huRange c) (huRange c)

/-- In the nonsquare branch, selected anchor mass plus the complementary
diagonal quotient trace is exactly the degree.  Thus Fable's divisibility of
the selected mass is equivalently a congruence for the complementary trace. -/
theorem pDivisibleAnchorMass_add_complementaryTrace_eq_degree_of_nonsquare
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    [∀ c : (secondOrderDefectGraph G).ConnectedComponent,
      NeZero c.supp.ncard]
    (hfree : ¬ containsC4 V G) {d p : ℕ}
    (hd : 4 ≤ d) (heven : Even d) (hmin : d ≤ G.minDegree)
    (hcard : Fintype.card V = d * (d - 1) + 3)
    (hnonsquare : ¬ IsSquare (d - 3))
    (u : ∀ c : (secondOrderDefectGraph G).ConnectedComponent,
      ZMod c.supp.ncard → V)
    (hu : ∀ c, Function.Injective (u c))
    (huRange : ∀ c, Set.range (u c) = c.supp) :
    pDivisibleAnchorMass G u p +
        ∑ c ∈ Finset.univ.filter (fun c :
          (secondOrderDefectGraph G).ConnectedComponent ↦
            ¬ p ∣ c.supp.ncard),
          componentQuotientMatrix G (secondOrderDefectGraph G) c c = d := by
  rw [pDivisibleAnchorMass_eq_sum_diagonalQuotient G hfree hd heven hmin
    hcard u hu huRange]
  rw [← secondOrder_componentQuotient_trace_eq_degree_of_nonsquare
    G hfree hd heven hmin hcard hnonsquare]
  exact Finset.sum_filter_add_sum_filter_not Finset.univ
    (fun c : (secondOrderDefectGraph G).ConnectedComponent ↦
      p ∣ c.supp.ncard)
    (fun c ↦ componentQuotientMatrix G (secondOrderDefectGraph G) c c)

end

end Erdos85
