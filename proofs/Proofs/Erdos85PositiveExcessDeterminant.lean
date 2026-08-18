import Proofs.Erdos85PlateauExcessStructure
import Proofs.Erdos85FrequencyPairTransport

/-!
# The determinant obstruction at positive excess

At order `d(d-1)+3+e`, the combined defect graph is `(e+2)`-regular and

`A^2 = (d-1)I + J - D`.

After separating the all-ones direction, this forces the determinant of the
defect resolvent to be `d-e-3` times a rational square.  This is the
positive-excess version of the boundary determinant obstruction; unlike the
cycle factorization, it does not require the defect graph to be two-regular.
-/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- At positive excess, `(d-1)I-D` is nonsingular by strict diagonal
dominance. -/
theorem positiveExcess_scalar_sub_defect_det_ne_zero
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) {d e : ℕ} (hd : 4 ≤ d)
    (he : e ≤ d - 4) (hreg : ∀ x, G.degree x = d)
    (hcard : Fintype.card V = d * (d - 1) + 3 + e) :
    Matrix.det ((d - 1 : ℚ) • (1 : Matrix V V ℚ) -
      (secondOrderDefectGraph G).adjMatrix ℚ) ≠ 0 := by
  let D := secondOrderDefectGraph G
  let B := (d - 1 : ℚ) • (1 : Matrix V V ℚ) - D.adjMatrix ℚ
  apply det_ne_zero_of_sum_row_lt_diag
  intro x
  have hdegree : D.degree x = e + 2 :=
    secondOrderDefectGraph_degree_eq_excess_add_two G hfree hreg hcard x
  have hoff : ∑ y ∈ Finset.univ.erase x, ‖B x y‖ = (e + 2 : ℝ) := by
    change ∑ y ∈ Finset.univ.erase x,
      ‖((d - 1 : ℚ) • (1 : Matrix V V ℚ) - D.adjMatrix ℚ) x y‖ = _
    calc
      _ = ∑ y ∈ Finset.univ.erase x, if D.Adj x y then (1 : ℝ) else 0 := by
        apply Finset.sum_congr rfl
        intro y hy
        have hne : x ≠ y := by
          simpa using (Finset.mem_erase.mp hy).1.symm
        simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply,
          SimpleGraph.adjMatrix_apply, hne, if_false, smul_eq_mul,
          mul_zero, zero_sub]
        by_cases hadj : D.Adj x y <;> simp [hadj]
      _ = ((Finset.univ.erase x).filter (fun y => D.Adj x y)).card := by
        simpa using (Finset.sum_boole (R := ℝ)
          (fun y : V => D.Adj x y) (Finset.univ.erase x))
      _ = (e + 2 : ℝ) := by
        congr 1
        have hfilt : (Finset.univ.erase x).filter (fun y => D.Adj x y) =
            D.neighborFinset x := by
          ext y
          simp only [Finset.mem_filter, Finset.mem_erase, Finset.mem_univ,
            and_true, SimpleGraph.mem_neighborFinset]
          constructor
          · exact fun h => h.2
          · intro hadj
            exact ⟨(D.ne_of_adj hadj).symm, hadj⟩
        rw [hfilt, D.card_neighborFinset_eq_degree, hdegree]
        norm_num
  rw [hoff]
  change (e + 2 : ℝ) < ‖B x x‖
  dsimp only [B]
  simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply,
    SimpleGraph.adjMatrix_apply, D.loopless.irrefl, if_false, sub_zero,
    smul_eq_mul, if_pos, mul_one]
  rw [← Rat.norm_cast_real, Real.norm_eq_abs, abs_of_nonneg]
  · exact_mod_cast (show (e : ℤ) + 2 < (d : ℤ) - 1 by omega)
  · exact_mod_cast (show (0 : ℤ) ≤ (d : ℤ) - 1 by omega)

/-- The positive-excess rank-one determinant identity.  The defect
resolvent has eigenvalue `d-e-3` on the all-ones vector, while adding `J`
changes that eigenvalue to `d²`. -/
theorem positiveExcess_defect_det_square
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) {d e : ℕ} (hd : 4 ≤ d)
    (he : e ≤ d - 4) (hreg : ∀ x, G.degree x = d)
    (hcard : Fintype.card V = d * (d - 1) + 3 + e) :
    (d - e - 3 : ℚ) * Matrix.det (G.adjMatrix ℚ) ^ 2 =
      (d : ℚ) ^ 2 * Matrix.det
        ((d - 1 : ℚ) • (1 : Matrix V V ℚ) -
          (secondOrderDefectGraph G).adjMatrix ℚ) := by
  let D := secondOrderDefectGraph G
  let A := G.adjMatrix ℚ
  let B := (d - 1 : ℚ) • (1 : Matrix V V ℚ) - D.adjMatrix ℚ
  let J : Matrix V V ℚ := Matrix.of fun _ _ => 1
  let u : V → ℚ := fun _ => 1
  let c : ℚ := d - e - 3
  have hdet : B.det ≠ 0 :=
    positiveExcess_scalar_sub_defect_det_ne_zero G hfree hd he hreg hcard
  have hunit : IsUnit B.det := (isUnit_iff_ne_zero).mpr hdet
  letI : Invertible B := Matrix.invertibleOfIsUnitDet B hunit
  have hBu : B.mulVec u = c • u := by
    funext x
    change (∑ y, B x y * 1) = c * 1
    simp only [mul_one]
    dsimp only [B, c]
    simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply,
      SimpleGraph.adjMatrix_apply, smul_eq_mul]
    rw [Finset.sum_sub_distrib]
    have hdiag : ∑ y : V, (d - 1 : ℚ) * (if x = y then 1 else 0) = d - 1 := by
      simp
    rw [hdiag, Finset.sum_boole]
    have hfilt : Finset.univ.filter (fun y => D.Adj x y) = D.neighborFinset x := by
      ext y
      simp [SimpleGraph.mem_neighborFinset]
    rw [hfilt, D.card_neighborFinset_eq_degree,
      secondOrderDefectGraph_degree_eq_excess_add_two G hfree hreg hcard x]
    push_cast
    ring
  have hc : c ≠ 0 := by
    dsimp only [c]
    exact_mod_cast (show (d : ℤ) - e - 3 ≠ 0 by omega)
  have hinvu : B⁻¹.mulVec u = c⁻¹ • u := by
    apply Matrix.inv_mulVec_eq_vec
    calc
      u = c⁻¹ • (c • u) := by ext x; simp [hc]
      _ = c⁻¹ • B.mulVec u := by rw [hBu]
      _ = B.mulVec (c⁻¹ • u) := by rw [Matrix.mulVec_smul]
  have hJ : J = Matrix.replicateCol Unit u * Matrix.replicateRow Unit u := by
    ext x y
    simp [J, Matrix.mul_apply, u]
  have hrank : c * Matrix.det (B + J) = (d : ℚ) ^ 2 * B.det := by
    rw [hJ, Matrix.det_add_replicateCol_mul_replicateRow hunit]
    have hscalar :
        Matrix.det ((1 : Matrix Unit Unit ℚ) +
          Matrix.replicateRow Unit u * B⁻¹ * Matrix.replicateCol Unit u) =
          1 + (Fintype.card V : ℚ) * c⁻¹ := by
      rw [Matrix.mul_assoc, ← Matrix.replicateCol_mulVec, hinvu,
        Matrix.replicateRow_mul_replicateCol]
      rw [Matrix.det_unique]
      simp only [Matrix.add_apply, Matrix.one_apply, Matrix.of_apply,
        if_pos, u, Pi.smul_apply, smul_eq_mul, one_mul]
      simp [dotProduct, c]
    rw [hscalar]
    have hn : (Fintype.card V : ℚ) =
        (d : ℚ) * ((d : ℚ) - 1) + 3 + e := by
      rw [hcard]
      push_cast
      rw [Nat.cast_sub (by omega : 1 ≤ d)]
      norm_num
    rw [hn]
    field_simp [hc]
    ring
  have hsq : A * A = B + J := by
    have hz := adjMatrix_sq_eq_sub_secondOrderDefect_of_regular G hfree hreg
    have hzQ : G.adjMatrix ℚ * G.adjMatrix ℚ =
        (d - 1 : ℚ) • (1 : Matrix V V ℚ) +
          Matrix.of (fun (_ : V) (_ : V) => (1 : ℚ)) - D.adjMatrix ℚ := by
      have h := congrArg (fun M ↦ M.map (Int.castRingHom ℚ)) hz
      simp only [Matrix.map_mul, adjMatrix_map_intCast] at h
      rw [h]
      ext x y
      simp only [Matrix.map_apply, Matrix.sub_apply, Matrix.add_apply,
        Matrix.smul_apply, Matrix.one_apply, Matrix.of_apply,
        FriendshipTheoremOQ01.onesMatrix, SimpleGraph.adjMatrix_apply,
        smul_eq_mul]
      split_ifs <;> simp only [eq_intCast] <;> push_cast <;> ring
    dsimp only [A, B, J]
    rw [hzQ]
    abel
  change c * A.det ^ 2 = (d : ℚ) ^ 2 * B.det
  calc
    c * A.det ^ 2 = c * Matrix.det (A * A) := by
      rw [Matrix.det_mul, pow_two]
    _ = c * Matrix.det (B + J) := by rw [hsq]
    _ = (d : ℚ) ^ 2 * B.det := hrank

/-- After removing the principal direction, the positive-excess defect
resolvent determinant is `d-e-3` times a rational square. -/
theorem positiveExcess_defect_resolvent_is_square_mul
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) {d e : ℕ} (hd : 4 ≤ d)
    (he : e ≤ d - 4) (hreg : ∀ x, G.degree x = d)
    (hcard : Fintype.card V = d * (d - 1) + 3 + e) :
    ∃ q : ℚ,
      Matrix.det ((d - 1 : ℚ) • (1 : Matrix V V ℚ) -
        (secondOrderDefectGraph G).adjMatrix ℚ) =
          (d - e - 3 : ℚ) * q ^ 2 := by
  let a := Matrix.det (G.adjMatrix ℚ)
  let b := Matrix.det ((d - 1 : ℚ) • (1 : Matrix V V ℚ) -
    (secondOrderDefectGraph G).adjMatrix ℚ)
  have h := positiveExcess_defect_det_square G hfree hd he hreg hcard
  have hd0 : (d : ℚ) ≠ 0 := by positivity
  refine ⟨a / d, ?_⟩
  change b = (d - e - 3 : ℚ) * (a / d) ^ 2
  change (d - e - 3 : ℚ) * a ^ 2 = (d : ℚ) ^ 2 * b at h
  field_simp [hd0]
  nlinarith

end

end Erdos85
