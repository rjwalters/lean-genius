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

private theorem complex_sum_re_eq_sum_map_re_principal (s : Multiset ℂ) :
    s.sum.re = (s.map Complex.re).sum := by
  induction s using Multiset.induction_on with
  | empty => simp
  | @cons z s ih => simp [ih]

/-- The C16 quadratic is also impossible as a factor of the nonprincipal
characteristic polynomial of a 7-regular graph on sixteen vertices.  The
proof works in the full adjacency matrix: after the principal root `7` and
the quadratic consume their moments, the thirteen residual real roots would
have sum `-17` and square sum at most `9`. -/
theorem false_of_cycleDefectQuadraticSixteen_nonprincipal_factor_sevenRegular
    {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hcard : Fintype.card V = 16) (hreg : ∀ x : V, G.degree x = 7)
    {q : ℚ[X]} (hchar : (G.adjMatrix ℚ).charpoly = (X - C 7) * q)
    (hfdvd : cycleDefectQuadraticSixteen.map (Int.castRingHom ℚ) ∣ q) : False := by
  obtain ⟨r, hr⟩ := hfdvd
  let f : ℂ[X] := cycleDefectQuadraticSixteen.map (Int.castRingHom ℂ)
  let rc : ℂ[X] := r.map (algebraMap ℚ ℂ)
  have hf : f ≠ 0 := (cycleDefectQuadraticSixteen_monic.map _).ne_zero
  have hq : q ≠ 0 := by
    intro hzero
    rw [hzero, mul_zero] at hchar
    exact (G.adjMatrix ℚ).charpoly_monic.ne_zero hchar
  have hr0 : r ≠ 0 := by
    intro hzero
    rw [hzero, mul_zero] at hr
    exact hq hr
  have hrc : rc ≠ 0 := by
    dsimp [rc]
    simpa using (Polynomial.map_injective _ (algebraMap ℚ ℂ).injective).ne hr0
  have hadj : (G.adjMatrix ℚ).map (algebraMap ℚ ℂ) = G.adjMatrix ℂ := by
    ext i j
    simp [SimpleGraph.adjMatrix_apply]
  have hmapf :
      (cycleDefectQuadraticSixteen.map (Int.castRingHom ℚ)).map
          (algebraMap ℚ ℂ) = f := by
    dsimp [f]
    rw [Polynomial.map_map]
    congr 1
  have hfactor :
      (G.adjMatrix ℂ).charpoly = (X - C 7) * f * rc := by
    rw [← hadj, Matrix.charpoly_map, hchar, hr, Polynomial.map_mul,
      Polynomial.map_mul, hmapf]
    simp [rc]
    ring
  have hherm : (G.adjMatrix ℂ).IsHermitian :=
    SimpleGraph.isHermitian_adjMatrix ℂ G
  have hfdeg : f.natDegree = 2 := by
    dsimp [f]
    rw [Polynomial.natDegree_map_eq_of_injective Int.cast_injective,
      cycleDefectQuadraticSixteen_natDegree]
  have hrcdeg : rc.natDegree = 13 := by
    have hp : X - C (7 : ℂ) ≠ 0 := X_sub_C_ne_zero 7
    have hpf : (X - C (7 : ℂ)) * f ≠ 0 := mul_ne_zero hp hf
    have hdeg := Polynomial.natDegree_mul hpf hrc
    have hpfdeg := Polynomial.natDegree_mul hp hf
    rw [← hfactor, Matrix.charpoly_natDegree_eq_dim, hcard, hpfdeg,
      natDegree_X_sub_C, hfdeg] at hdeg
    omega
  have hrcrootcard : rc.roots.card = 13 := by
    rw [← (IsAlgClosed.splits rc).natDegree_eq_card_roots, hrcdeg]
  have hone := complexRootPowerSum_charpoly_eq_trace_pow
    (G.adjMatrix ℂ) hherm 1
  have hp : X - C (7 : ℂ) ≠ 0 := X_sub_C_ne_zero 7
  have hpf : (X - C (7 : ℂ)) * f ≠ 0 := mul_ne_zero hp hf
  have haddpfOne := complexRootPowerSum_mul hp hf 1
  have haddrcOne := complexRootPowerSum_mul hpf hrc 1
  rw [hfactor, haddrcOne, haddpfOne, complexRootPowerSum_X_sub_C,
    cycleDefectQuadraticSixteen_complexRootPowerSum_one] at hone
  have htrace : Matrix.trace (G.adjMatrix ℂ) = 0 := by
    rw [SimpleGraph.trace_adjMatrix]
  simp only [pow_one, htrace] at hone
  have hrcsum : complexRootPowerSum rc 1 = -17 := by
    linear_combination hone
  have htwo := complexRootPowerSum_charpoly_eq_trace_pow
    (G.adjMatrix ℂ) hherm 2
  have haddpfTwo := complexRootPowerSum_mul hp hf 2
  have haddrcTwo := complexRootPowerSum_mul hpf hrc 2
  have htraceSq := trace_sq_complex_adjMatrix_eq_oneHundredTwelve_of_sevenRegular
    G hcard hreg
  rw [hfactor, haddrcTwo, haddpfTwo, complexRootPowerSum_X_sub_C,
    cycleDefectQuadraticSixteen_complexRootPowerSum_two, htraceSq] at htwo
  have hrcSq : (complexRootPowerSum rc 2).re ≤ 9 := by
    have hre := congrArg Complex.re htwo
    norm_num at hre ⊢
    linarith
  have hrootReal : ∀ z ∈ rc.roots, z.im = 0 := by
    intro z hz
    have hzchar : z ∈ (G.adjMatrix ℂ).charpoly.roots := by
      rw [hfactor, roots_mul (mul_ne_zero hpf hrc), Multiset.mem_add]
      exact Or.inr hz
    rw [hherm.roots_charpoly_eq_eigenvalues] at hzchar
    obtain ⟨i, _hi, rfl⟩ := Multiset.mem_map.mp hzchar
    simp
  let s : Multiset ℝ := rc.roots.map Complex.re
  have scard : s.card = 13 := by simp [s, hrcrootcard]
  have ssum : s.sum = -17 := by
    dsimp [s]
    rw [← complex_sum_re_eq_sum_map_re_principal]
    have hre := congrArg Complex.re hrcsum
    rw [complexRootPowerSum] at hre
    simp only [pow_one] at hre
    change (rc.roots.map id).sum.re = (-17 : ℂ).re at hre
    simpa using hre
  have ssq : (s.map fun x ↦ x ^ 2).sum ≤ 9 := by
    dsimp [s]
    rw [Multiset.map_map]
    have hmap :
        rc.roots.map (fun z ↦ (z.re : ℝ) ^ 2) =
          rc.roots.map (fun z ↦ (z ^ 2).re) := by
      apply Multiset.map_congr rfl
      intro z hz
      have hzEq : z = (z.re : ℂ) := by
        apply Complex.ext
        · simp
        · simp [hrootReal z hz]
      rw [hzEq]
      simp only [pow_two, Complex.mul_re, Complex.ofReal_re,
        Complex.ofReal_im, mul_zero, sub_zero]
    change (rc.roots.map (fun z ↦ z.re ^ 2)).sum ≤ 9
    rw [hmap]
    change (rc.roots.map (Complex.re ∘ fun z ↦ z ^ 2)).sum ≤ 9
    rw [← Multiset.map_map, ← complex_sum_re_eq_sum_map_re_principal]
    exact hrcSq
  exact false_of_card_thirteen_sum_neg_seventeen_sq_sum_le_nine
    s scard ssum ssq

/-- The golden quadratic is impossible for the same full-matrix reason.  It
uses all `63` units left after the principal root, while the residual roots
must still sum to `-18`. -/
theorem false_of_cycleDefectQuadraticFive_nonprincipal_factor_sevenRegular
    {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hcard : Fintype.card V = 16) (hreg : ∀ x : V, G.degree x = 7)
    {q : ℚ[X]} (hchar : (G.adjMatrix ℚ).charpoly = (X - C 7) * q)
    (hfdvd : cycleDefectQuadraticFive.map (Int.castRingHom ℚ) ∣ q) : False := by
  obtain ⟨r, hr⟩ := hfdvd
  let f : ℂ[X] := cycleDefectQuadraticFive.map (Int.castRingHom ℂ)
  let rc : ℂ[X] := r.map (algebraMap ℚ ℂ)
  have hf : f ≠ 0 := (cycleDefectQuadraticFive_monic.map _).ne_zero
  have hq : q ≠ 0 := by
    intro hzero
    rw [hzero, mul_zero] at hchar
    exact (G.adjMatrix ℚ).charpoly_monic.ne_zero hchar
  have hr0 : r ≠ 0 := by
    intro hzero
    rw [hzero, mul_zero] at hr
    exact hq hr
  have hrc : rc ≠ 0 := by
    dsimp [rc]
    simpa using (Polynomial.map_injective _ (algebraMap ℚ ℂ).injective).ne hr0
  have hadj : (G.adjMatrix ℚ).map (algebraMap ℚ ℂ) = G.adjMatrix ℂ := by
    ext i j
    simp [SimpleGraph.adjMatrix_apply]
  have hmapf :
      (cycleDefectQuadraticFive.map (Int.castRingHom ℚ)).map
          (algebraMap ℚ ℂ) = f := by
    dsimp [f]
    rw [Polynomial.map_map]
    congr 1
  have hfactor :
      (G.adjMatrix ℂ).charpoly = (X - C 7) * f * rc := by
    rw [← hadj, Matrix.charpoly_map, hchar, hr, Polynomial.map_mul,
      Polynomial.map_mul, hmapf]
    simp [rc]
    ring
  have hherm : (G.adjMatrix ℂ).IsHermitian :=
    SimpleGraph.isHermitian_adjMatrix ℂ G
  have hp : X - C (7 : ℂ) ≠ 0 := X_sub_C_ne_zero 7
  have hpf : (X - C (7 : ℂ)) * f ≠ 0 := mul_ne_zero hp hf
  have hone := complexRootPowerSum_charpoly_eq_trace_pow
    (G.adjMatrix ℂ) hherm 1
  have haddpfOne := complexRootPowerSum_mul hp hf 1
  have haddrcOne := complexRootPowerSum_mul hpf hrc 1
  rw [hfactor, haddrcOne, haddpfOne, complexRootPowerSum_X_sub_C,
    cycleDefectQuadraticFive_complexRootPowerSum_one] at hone
  have htrace : Matrix.trace (G.adjMatrix ℂ) = 0 := by
    rw [SimpleGraph.trace_adjMatrix]
  simp only [pow_one, htrace] at hone
  have hrcsum : complexRootPowerSum rc 1 = -18 := by
    linear_combination hone
  have htwo := complexRootPowerSum_charpoly_eq_trace_pow
    (G.adjMatrix ℂ) hherm 2
  have haddpfTwo := complexRootPowerSum_mul hp hf 2
  have haddrcTwo := complexRootPowerSum_mul hpf hrc 2
  have htraceSq := trace_sq_complex_adjMatrix_eq_oneHundredTwelve_of_sevenRegular
    G hcard hreg
  rw [hfactor, haddrcTwo, haddpfTwo, complexRootPowerSum_X_sub_C,
    cycleDefectQuadraticFive_complexRootPowerSum_two, htraceSq] at htwo
  have hrcSq : (complexRootPowerSum rc 2).re ≤ 0 := by
    have hre := congrArg Complex.re htwo
    norm_num at hre ⊢
    linarith
  have hrootReal : ∀ z ∈ rc.roots, z.im = 0 := by
    intro z hz
    have hzchar : z ∈ (G.adjMatrix ℂ).charpoly.roots := by
      rw [hfactor, roots_mul (mul_ne_zero hpf hrc), Multiset.mem_add]
      exact Or.inr hz
    rw [hherm.roots_charpoly_eq_eigenvalues] at hzchar
    obtain ⟨i, _hi, rfl⟩ := Multiset.mem_map.mp hzchar
    simp
  let s : Multiset ℝ := rc.roots.map Complex.re
  have ssum : s.sum = -18 := by
    dsimp [s]
    rw [← complex_sum_re_eq_sum_map_re_principal]
    have hre := congrArg Complex.re hrcsum
    rw [complexRootPowerSum] at hre
    simp only [pow_one] at hre
    change (rc.roots.map id).sum.re = (-18 : ℂ).re at hre
    simpa using hre
  have ssq : (s.map fun x ↦ x ^ 2).sum ≤ 0 := by
    dsimp [s]
    rw [Multiset.map_map]
    have hmap :
        rc.roots.map (fun z ↦ (z.re : ℝ) ^ 2) =
          rc.roots.map (fun z ↦ (z ^ 2).re) := by
      apply Multiset.map_congr rfl
      intro z hz
      have hzEq : z = (z.re : ℂ) := by
        apply Complex.ext
        · simp
        · simp [hrootReal z hz]
      rw [hzEq]
      simp only [pow_two, Complex.mul_re, Complex.ofReal_re,
        Complex.ofReal_im, mul_zero, sub_zero]
    change (rc.roots.map (fun z ↦ z.re ^ 2)).sum ≤ 0
    rw [hmap]
    change (rc.roots.map (Complex.re ∘ fun z ↦ z ^ 2)).sum ≤ 0
    rw [← Multiset.map_map, ← complex_sum_re_eq_sum_map_re_principal]
    exact hrcSq
  exact false_of_sum_neg_eighteen_sq_sum_le_zero s ssum ssq

end

end Erdos85
