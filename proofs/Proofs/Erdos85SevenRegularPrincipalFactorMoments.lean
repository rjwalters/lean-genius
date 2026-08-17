import Proofs.Erdos85CyclePrimaryQuadraticTerminals

/-! # Removing the principal eigenvalue from a 7-regular block -/

open Polynomial

namespace Erdos85

noncomputable section

theorem complexRootPowerSum_X_sub_C (a : ℂ) (m : ℕ) :
    complexRootPowerSum (X - C a) m = a ^ m := by
  rw [complexRootPowerSum, roots_X_sub_C]
  simp

/-- If a Hermitian characteristic polynomial factors as its principal
`X-7` factor, a selected factor `f`, and a residual factor `q`, then the
second moment of `f` is bounded by the total square trace minus `49`. -/
theorem complexRootPowerSum_factor_two_re_le_trace_sq_sub_principal_seven
    {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℂ) (hA : A.IsHermitian)
    {f q : ℂ[X]} (hf : f ≠ 0) (hq : q ≠ 0)
    (hfactor : A.charpoly = (X - C 7) * f * q) :
    (complexRootPowerSum f 2).re + 49 ≤
      (Matrix.trace (A ^ 2)).re := by
  have hp : (X - C (7 : ℂ)) ≠ 0 := X_sub_C_ne_zero 7
  have hpf : (X - C (7 : ℂ)) * f ≠ 0 := mul_ne_zero hp hf
  have hsumPrincipal := complexRootPowerSum_mul hp hf 2
  have hsumResidual := complexRootPowerSum_mul hpf hq 2
  have htrace := complexRootPowerSum_charpoly_eq_trace_pow A hA 2
  have hnonneg := complexRootPowerSum_two_re_nonnegative_of_charpoly_factor
    A hA hpf hq hfactor
  rw [← htrace, hfactor, hsumResidual, hsumPrincipal,
    complexRootPowerSum_X_sub_C] at ⊢
  norm_num at ⊢
  linarith

/-- In particular, square trace at most `112` leaves only `63` for every
nonprincipal characteristic factor. -/
theorem complexRootPowerSum_factor_two_re_le_sixtyThree_of_principal_seven
    {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℂ) (hA : A.IsHermitian)
    {f q : ℂ[X]} (hf : f ≠ 0) (hq : q ≠ 0)
    (hfactor : A.charpoly = (X - C 7) * f * q)
    (htraceSq : (Matrix.trace (A ^ 2)).re ≤ 112) :
    (complexRootPowerSum f 2).re ≤ 63 := by
  have h :=
    complexRootPowerSum_factor_two_re_le_trace_sq_sub_principal_seven
      A hA hf hq hfactor
  linarith

open SimpleGraph

/-- A 7-regular graph on sixteen vertices has adjacency square trace
`16·7 = 112`. -/
theorem trace_sq_complex_adjMatrix_eq_oneHundredTwelve_of_sevenRegular
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hcard : Fintype.card V = 16)
    (hreg : ∀ x : V, G.degree x = 7) :
    Matrix.trace ((G.adjMatrix ℂ) ^ 2) = 112 := by
  have hz : Matrix.trace ((G.adjMatrix ℤ) ^ 2) = 112 := by
    rw [pow_two, Matrix.trace]
    simp only [Matrix.diag_apply]
    simp_rw [G.adjMatrix_mul_self_apply_self, hreg]
    simp [hcard]
  rw [trace_complex_adjMatrix_pow_eq_intCast, hz]
  norm_num

/-- Graph-facing budget bridge.  If `f` divides the nonprincipal
characteristic factor of a 7-regular graph on sixteen vertices, then its raw
second root moment is at most `63`. -/
theorem nonprincipal_factor_secondMoment_le_sixtyThree_of_sevenRegular
    {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hcard : Fintype.card V = 16)
    (hreg : ∀ x : V, G.degree x = 7)
    {q f : ℚ[X]}
    (hchar : (G.adjMatrix ℚ).charpoly = (X - C 7) * q)
    (hf : f ≠ 0) (hfdvd : f ∣ q) :
    (complexRootPowerSum (f.map (algebraMap ℚ ℂ)) 2).re ≤ 63 := by
  obtain ⟨r, hr⟩ := hfdvd
  have hq : q ≠ 0 := by
    intro hzero
    rw [hzero, mul_zero] at hchar
    exact (G.adjMatrix ℚ).charpoly_monic.ne_zero hchar
  have hr0 : r ≠ 0 := by
    intro hrzero
    rw [hrzero, mul_zero] at hr
    exact hq hr
  have hfmap : f.map (algebraMap ℚ ℂ) ≠ 0 := by
    simpa using
      (Polynomial.map_injective _ (algebraMap ℚ ℂ).injective).ne hf
  have hrmap : r.map (algebraMap ℚ ℂ) ≠ 0 := by
    simpa using
      (Polynomial.map_injective _ (algebraMap ℚ ℂ).injective).ne hr0
  have hadj :
      (G.adjMatrix ℚ).map (algebraMap ℚ ℂ) = G.adjMatrix ℂ := by
    ext i j
    simp [SimpleGraph.adjMatrix_apply]
  have hfactor :
      (G.adjMatrix ℂ).charpoly =
        (X - C 7) * f.map (algebraMap ℚ ℂ) *
          r.map (algebraMap ℚ ℂ) := by
    rw [← hadj, Matrix.charpoly_map, hchar, hr, Polynomial.map_mul,
      Polynomial.map_mul]
    simp
    ring
  have hherm : (G.adjMatrix ℂ).IsHermitian := by
    exact SimpleGraph.isHermitian_adjMatrix ℂ G
  apply complexRootPowerSum_factor_two_re_le_sixtyThree_of_principal_seven
    (G.adjMatrix ℂ) hherm hfmap hrmap hfactor
  rw [trace_sq_complex_adjMatrix_eq_oneHundredTwelve_of_sevenRegular
    G hcard hreg]
  norm_num

/-- Integer cycle-factor consumer for the graph-facing nonprincipal budget. -/
theorem false_of_large_integer_nonprincipal_factor_of_sevenRegular
    {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hcard : Fintype.card V = 16)
    (hreg : ∀ x : V, G.degree x = 7)
    {q : ℚ[X]} {f : ℤ[X]} (hf : f.Monic)
    (hchar : (G.adjMatrix ℚ).charpoly = (X - C 7) * q)
    (hfdvd : f.map (Int.castRingHom ℚ) ∣ q)
    (hmoment : 63 <
      (complexRootPowerSum (f.map (Int.castRingHom ℂ)) 2).re) : False := by
  have hle := nonprincipal_factor_secondMoment_le_sixtyThree_of_sevenRegular
    G hcard hreg hchar (hf.map _).ne_zero hfdvd
  have hmap :
      (f.map (Int.castRingHom ℚ)).map (algebraMap ℚ ℂ) =
        f.map (Int.castRingHom ℂ) := by
    rw [Polynomial.map_map]
    congr 1
  rw [hmap] at hle
  linarith

theorem false_of_cycleDefectCubicSeven_nonprincipal_factor_sevenRegular
    {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hcard : Fintype.card V = 16) (hreg : ∀ x : V, G.degree x = 7)
    {q : ℚ[X]} (hchar : (G.adjMatrix ℚ).charpoly = (X - C 7) * q)
    (hfdvd : cycleDefectCubicSeven.map (Int.castRingHom ℚ) ∣ q) : False := by
  apply false_of_large_integer_nonprincipal_factor_of_sevenRegular
    G hcard hreg cycleDefectCubicSeven_monic hchar hfdvd
  rw [cycleDefectCubicSeven_complexRootPowerSum_two]
  norm_num

theorem false_of_cycleDefectCubicNine_nonprincipal_factor_sevenRegular
    {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hcard : Fintype.card V = 16) (hreg : ∀ x : V, G.degree x = 7)
    {q : ℚ[X]} (hchar : (G.adjMatrix ℚ).charpoly = (X - C 7) * q)
    (hfdvd : cycleDefectCubicNine.map (Int.castRingHom ℚ) ∣ q) : False := by
  apply false_of_large_integer_nonprincipal_factor_of_sevenRegular
    G hcard hreg cycleDefectCubicNine_monic hchar hfdvd
  rw [cycleDefectCubicNine_complexRootPowerSum_two]
  norm_num

theorem false_of_cycleDefectQuinticEleven_nonprincipal_factor_sevenRegular
    {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hcard : Fintype.card V = 16) (hreg : ∀ x : V, G.degree x = 7)
    {q : ℚ[X]} (hchar : (G.adjMatrix ℚ).charpoly = (X - C 7) * q)
    (hfdvd : cycleDefectQuinticEleven.map (Int.castRingHom ℚ) ∣ q) : False := by
  apply false_of_large_integer_nonprincipal_factor_of_sevenRegular
    G hcard hreg cycleDefectQuinticEleven_monic hchar hfdvd
  rw [cycleDefectQuinticEleven_complexRootPowerSum_two]
  norm_num

theorem false_of_cycleDefectSexticThirteen_nonprincipal_factor_sevenRegular
    {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hcard : Fintype.card V = 16) (hreg : ∀ x : V, G.degree x = 7)
    {q : ℚ[X]} (hchar : (G.adjMatrix ℚ).charpoly = (X - C 7) * q)
    (hfdvd : cycleDefectSexticThirteen.map (Int.castRingHom ℚ) ∣ q) : False := by
  apply false_of_large_integer_nonprincipal_factor_of_sevenRegular
    G hcard hreg cycleDefectSexticThirteen_monic hchar hfdvd
  rw [cycleDefectSexticThirteen_complexRootPowerSum_two]
  norm_num

end

end Erdos85
