import Proofs.Erdos85DifferencePacking
import Proofs.Erdos85TriangleTerminal

/-!
# Uniform equal-cycle terminal bounds

The linked difference-family structure bounds every diagonal quotient entry
by two.  On the other hand, when `d-3` is nonsquare, the quadratic quotient
equation forces the quotient trace to equal its principal eigenvalue `d`.
Together these facts bound the common defect-cycle order without classifying
quotient rows.
-/

namespace Erdos85

noncomputable section

/-- A rational matrix with constant row and column sum `d` and square equal
to `(d-3)I` plus a rank-one constant matrix has trace `d` whenever `d-3` is
nonsquare. -/
theorem Matrix.trace_eq_degree_of_sq_rankOne_of_nonsquare
    {I : Type*} [Fintype I] [DecidableEq I] [Nonempty I]
    (Q : Matrix I I ℚ) {d : ℕ}
    (hcard : 1 < Fintype.card I)
    (hrow : ∀ i, ∑ j, Q i j = d)
    (hcol : ∀ j, ∑ i, Q i j = d)
    (k : ℚ)
    (hsq : Q * Q = (((d - 3 : ℕ) : ℚ)) •
        (1 : Matrix I I ℚ) + k • Matrix.of (fun _ _ ↦ 1))
    (hnonsquare : ¬ IsSquare (d - 3)) :
    Matrix.trace Q = d := by
  let P := normalizedOnesProjection I
  have hQP := Matrix.mul_normalizedOnesProjection_of_row_sum Q d hrow
  have hPQ := Matrix.normalizedOnesProjection_mul_of_col_sum Q d hcol
  have hcommM : Q * P = P * Q := hQP.trans hPQ.symm
  have hcomm : Q.toLin' * P.toLin' = P.toLin' * Q.toLin' := by
    simpa only [Module.End.mul_eq_comp, Matrix.toLin'_mul] using
      congrArg Matrix.toLin' hcommM
  let R := LinearMap.range P.toLin'
  let W := LinearMap.ker P.toLin'
  let hR := mapsTo_range_of_commute Q.toLin' P.toLin' hcomm
  let hW := mapsTo_ker_of_commute Q.toLin' P.toLin' hcomm
  letI : Nontrivial W := normalizedOnesProjection_ker_nontrivial I hcard
  have hRtrace : LinearMap.trace ℚ R (Q.toLin'.restrict hR) = d := by
    rw [trace_restrict_range_eq_trace_mul_of_idempotent
      Q.toLin' P.toLin' (normalizedOnesProjection_toLin_isIdempotent I) hcomm]
    have hlin := congrArg Matrix.toLin' hQP
    have hmul : Q.toLin' * P.toLin' = (d : ℚ) • P.toLin' := by
      simpa only [P, Module.End.mul_eq_comp, Matrix.toLin'_mul,
        map_smul] using hlin
    rw [hmul, map_smul, Matrix.trace_toLin'_eq,
      normalizedOnesProjection_trace]
    simp
  have hWsq : (Q.toLin'.restrict hW) * (Q.toLin'.restrict hW) =
      (((d - 3 : ℕ) : ℚ)) • LinearMap.id := by
    simpa [P, hcomm, W, hW] using
      (Matrix.restrict_ker_normalizedOnesProjection_sq
        Q d (((d - 3 : ℕ) : ℚ)) k hrow hcol hsq)
  have hWtrace : LinearMap.trace ℚ W (Q.toLin'.restrict hW) = 0 :=
    LinearMap.trace_eq_zero_of_sq_eq_nonsquare_nat
      (Q.toLin'.restrict hW) (d - 3) hnonsquare hWsq
  have hsplit := trace_eq_add_trace_restrict_of_isCompl
    Q.toLin' R W (LinearMap.IsIdempotentElem.isCompl
      (normalizedOnesProjection_toLin_isIdempotent I)) hR hW
  rw [hRtrace, hWtrace, add_zero] at hsplit
  simpa [Matrix.trace_toLin'_eq] using hsplit

/-- If every diagonal entry of such a quotient is at most two, nonsquare
`d-3` forces at least `d/2` components. -/
theorem Matrix.degree_le_two_mul_card_of_sq_rankOne_of_nonsquare
    {I : Type*} [Fintype I] [DecidableEq I] [Nonempty I]
    (Q : Matrix I I ℚ) {d : ℕ}
    (hcard : 1 < Fintype.card I)
    (hrow : ∀ i, ∑ j, Q i j = d)
    (hcol : ∀ j, ∑ i, Q i j = d)
    (k : ℚ)
    (hsq : Q * Q = (((d - 3 : ℕ) : ℚ)) •
        (1 : Matrix I I ℚ) + k • Matrix.of (fun _ _ ↦ 1))
    (hnonsquare : ¬ IsSquare (d - 3))
    (hdiagNonneg : ∀ i, 0 ≤ Q i i)
    (hdiag : ∀ i, Q i i ≤ 2) :
    (d : ℚ) ≤ 2 * Fintype.card I := by
  have htrace := Matrix.trace_eq_degree_of_sq_rankOne_of_nonsquare
    Q hcard hrow hcol k hsq hnonsquare
  rw [Matrix.trace] at htrace
  rw [← htrace]
  calc
    ∑ i, Matrix.diag Q i ≤ ∑ _i : I, (2 : ℚ) := by
      apply Finset.sum_le_sum
      intro i hi
      exact hdiag i
    _ = 2 * Fintype.card I := by simp [mul_comm]

/-- In the graph quotient the diagonal entries are in `{0,2}`.  Thus the
nonsquare trace identity is sharper than the cardinal bound: exactly `d/2`
components (expressed without division below) have a nonzero diagonal block.
These components are orientation anchors, since a nonzero odd self-block
cannot be reverse-circulant. -/
theorem Matrix.two_mul_card_diagonal_two_eq_degree_of_sq_rankOne_of_nonsquare
    {I : Type*} [Fintype I] [DecidableEq I] [Nonempty I]
    (Q : Matrix I I ℚ) {d : ℕ}
    (hcard : 1 < Fintype.card I)
    (hrow : ∀ i, ∑ j, Q i j = d)
    (hcol : ∀ j, ∑ i, Q i j = d)
    (k : ℚ)
    (hsq : Q * Q = (((d - 3 : ℕ) : ℚ)) •
        (1 : Matrix I I ℚ) + k • Matrix.of (fun _ _ ↦ 1))
    (hnonsquare : ¬ IsSquare (d - 3))
    (hdiag : ∀ i, Q i i = 0 ∨ Q i i = 2) :
    (d : ℚ) = 2 * ((Finset.univ.filter fun i ↦ Q i i = 2).card : ℚ) := by
  have htrace := Matrix.trace_eq_degree_of_sq_rankOne_of_nonsquare
    Q hcard hrow hcol k hsq hnonsquare
  rw [Matrix.trace] at htrace
  rw [← htrace]
  calc
    ∑ i, Matrix.diag Q i =
        ∑ i, if Q i i = 2 then (2 : ℚ) else 0 := by
      apply Finset.sum_congr rfl
      intro i hi
      simp only [Matrix.diag]
      rcases hdiag i with hzero | htwo
      · simp [hzero]
      · simp [htwo]
    _ = 2 * ((Finset.univ.filter fun i ↦ Q i i = 2).card : ℚ) := by
      rw [← Finset.sum_boole (fun i ↦ Q i i = 2) Finset.univ]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      split <;> simp_all

end

end Erdos85
