import Proofs.Erdos85CyclePrimaryHermitianMomentBridge

/-! # Quadratic cycle-primary terminals for the H16 defect spectrum -/

open Polynomial

namespace Erdos85

noncomputable section

private theorem sum_sq_sub_formula (a : ℝ) (s : Multiset ℝ) :
    (s.map fun x ↦ (a - x) ^ 2).sum =
      s.card * a ^ 2 - 2 * a * s.sum + (s.map fun x ↦ x ^ 2).sum := by
  induction s using Multiset.induction_on with
  | empty => simp
  | @cons b s ih =>
      simp only [Multiset.map_cons, Multiset.sum_cons, Multiset.card_cons]
      rw [ih]
      push_cast
      ring

theorem multiset_sq_sum_le_card_mul_sum_sq (s : Multiset ℝ) :
    s.sum ^ 2 ≤ s.card * (s.map fun x ↦ x ^ 2).sum := by
  induction s using Multiset.induction_on with
  | empty => simp
  | @cons a s ih =>
      have hdiff : 0 ≤ (s.map fun x ↦ (a - x) ^ 2).sum := by
        apply Multiset.sum_nonneg
        intro y hy
        obtain ⟨x, _hx, rfl⟩ := Multiset.mem_map.mp hy
        exact sq_nonneg (a - x)
      rw [sum_sq_sub_formula] at hdiff
      simp only [Multiset.sum_cons, Multiset.card_cons, Multiset.map_cons]
      push_cast
      nlinarith

/-- The Cauchy–Schwarz contradiction left after a C16 quadratic consumes
`54` of the `63` square-moment budget: thirteen remaining real roots cannot
have sum `-17` and square-sum at most `9`. -/
theorem false_of_card_thirteen_sum_neg_seventeen_sq_sum_le_nine
    (s : Multiset ℝ) (hcard : s.card = 13)
    (hsum : s.sum = -17) (hsq : (s.map fun x ↦ x ^ 2).sum ≤ 9) : False := by
  have hcs := multiset_sq_sum_le_card_mul_sum_sq s
  rw [hcard, hsum] at hcs
  norm_num at hcs
  nlinarith

theorem false_of_sum_neg_eighteen_sq_sum_le_zero
    (s : Multiset ℝ) (hsum : s.sum = -18)
    (hsq : (s.map fun x ↦ x ^ 2).sum ≤ 0) : False := by
  have hnonneg : 0 ≤ (s.map fun x ↦ x ^ 2).sum := by
    apply Multiset.sum_nonneg
    intro y hy
    obtain ⟨x, _hx, rfl⟩ := Multiset.mem_map.mp hy
    exact sq_nonneg x
  have hcs := multiset_sq_sum_le_card_mul_sum_sq s
  rw [hsum] at hcs
  nlinarith

/-- First Newton identity in the form parallel to the second-moment bridge. -/
theorem complexRootPowerSum_one_eq_coeff
    {p : ℂ[X]} (hp : p.Monic) (hdeg : 0 < p.natDegree) :
    complexRootPowerSum p 1 = -p.coeff (p.natDegree - 1) := by
  have hsplit : p.Splits := IsAlgClosed.splits p
  have hsum := hsplit.nextCoeff_eq_neg_sum_roots_of_monic hp
  rw [nextCoeff_of_natDegree_pos hdeg] at hsum
  rw [complexRootPowerSum]
  simp only [pow_one]
  change (p.roots.map id).sum = -p.coeff (p.natDegree - 1)
  rw [Multiset.map_id]
  rw [hsum]
  ring

theorem cycleDefectQuadraticSixteen_complexRootPowerSum_one :
    complexRootPowerSum
      (cycleDefectQuadraticSixteen.map (Int.castRingHom ℂ)) 1 = 10 := by
  rw [complexRootPowerSum_one_eq_coeff
    (cycleDefectQuadraticSixteen_monic.map _) (by
      rw [Polynomial.natDegree_map_eq_of_injective Int.cast_injective,
        cycleDefectQuadraticSixteen_natDegree]
      norm_num)]
  rw [Polynomial.natDegree_map_eq_of_injective Int.cast_injective,
    cycleDefectQuadraticSixteen_natDegree]
  norm_num [cycleDefectQuadraticSixteen, coeff_sub, coeff_add, coeff_C_mul,
    coeff_X_pow, coeff_C, coeff_X]

theorem cycleDefectQuadraticFive_complexRootPowerSum_one :
    complexRootPowerSum
      (cycleDefectQuadraticFive.map (Int.castRingHom ℂ)) 1 = 11 := by
  rw [complexRootPowerSum_one_eq_coeff
    (cycleDefectQuadraticFive_monic.map _) (by
      rw [Polynomial.natDegree_map_eq_of_injective Int.cast_injective,
        cycleDefectQuadraticFive_natDegree]
      norm_num)]
  rw [Polynomial.natDegree_map_eq_of_injective Int.cast_injective,
    cycleDefectQuadraticFive_natDegree]
  norm_num [cycleDefectQuadraticFive, coeff_sub, coeff_add, coeff_C_mul,
    coeff_X_pow, coeff_C, coeff_X]

theorem cycleDefectQuadraticSixteen_complexRootPowerSum_two :
    complexRootPowerSum
      (cycleDefectQuadraticSixteen.map (Int.castRingHom ℂ)) 2 = 54 := by
  rw [integerMonic_complexRootPowerSum_two
    cycleDefectQuadraticSixteen_monic (by
      rw [cycleDefectQuadraticSixteen_natDegree])]
  rw [cycleDefectQuadraticSixteen_natDegree,
    cycleDefectQuadraticSixteen_squareMoment]
  norm_num

theorem cycleDefectQuadraticFive_complexRootPowerSum_two :
    complexRootPowerSum
      (cycleDefectQuadraticFive.map (Int.castRingHom ℂ)) 2 = 63 := by
  rw [integerMonic_complexRootPowerSum_two
    cycleDefectQuadraticFive_monic (by
      rw [cycleDefectQuadraticFive_natDegree])]
  rw [cycleDefectQuadraticFive_natDegree,
    cycleDefectQuadraticFive_squareMoment]
  norm_num

private theorem complex_sum_re_eq_sum_map_re (s : Multiset ℂ) :
    s.sum.re = (s.map Complex.re).sum := by
  induction s using Multiset.induction_on with
  | empty => simp
  | @cons z s ih => simp [ih]

/-- The C16 quadratic cannot occur in the full 15-dimensional
nonprincipal Hermitian defect spectrum: it leaves thirteen real roots with
sum `-17` but only `9` units of square moment. -/
theorem false_of_cycleDefectQuadraticSixteen_charpoly_factor
    {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℂ) (hA : A.IsHermitian)
    (hcard : Fintype.card n = 15) {q : ℂ[X]} (hq : q ≠ 0)
    (hfactor : A.charpoly =
      cycleDefectQuadraticSixteen.map (Int.castRingHom ℂ) * q)
    (htrace : Matrix.trace A = -7)
    (htraceSq : (Matrix.trace (A ^ 2)).re ≤ 63) : False := by
  let f : ℂ[X] := cycleDefectQuadraticSixteen.map (Int.castRingHom ℂ)
  have hf : f ≠ 0 := (cycleDefectQuadraticSixteen_monic.map _).ne_zero
  have hfdeg : f.natDegree = 2 := by
    dsimp [f]
    rw [Polynomial.natDegree_map_eq_of_injective Int.cast_injective,
      cycleDefectQuadraticSixteen_natDegree]
  have hqdeg : q.natDegree = 13 := by
    have hdeg := Polynomial.natDegree_mul hf hq
    rw [← hfactor, Matrix.charpoly_natDegree_eq_dim, hcard, hfdeg] at hdeg
    omega
  have hqrootcard : q.roots.card = 13 := by
    rw [← (IsAlgClosed.splits q).natDegree_eq_card_roots, hqdeg]
  have htotalOne := complexRootPowerSum_charpoly_eq_trace_pow A hA 1
  have haddOne := complexRootPowerSum_mul hf hq 1
  rw [hfactor, haddOne, cycleDefectQuadraticSixteen_complexRootPowerSum_one]
      at htotalOne
  simp only [pow_one, htrace] at htotalOne
  have hqsum : complexRootPowerSum q 1 = -17 := by
    linear_combination htotalOne
  have htotalTwo := complexRootPowerSum_charpoly_eq_trace_pow A hA 2
  have haddTwo := complexRootPowerSum_mul hf hq 2
  have hqSq : (complexRootPowerSum q 2).re ≤ 9 := by
    rw [← htotalTwo, hfactor, haddTwo,
      cycleDefectQuadraticSixteen_complexRootPowerSum_two] at htraceSq
    norm_num at htraceSq ⊢
    linarith
  have hrootReal : ∀ z ∈ q.roots, z.im = 0 := by
    intro z hz
    have hzchar : z ∈ A.charpoly.roots := by
      rw [hfactor, roots_mul (mul_ne_zero hf hq), Multiset.mem_add]
      exact Or.inr hz
    rw [hA.roots_charpoly_eq_eigenvalues] at hzchar
    obtain ⟨i, _hi, rfl⟩ := Multiset.mem_map.mp hzchar
    simp
  let s : Multiset ℝ := q.roots.map Complex.re
  have scard : s.card = 13 := by simp [s, hqrootcard]
  have ssum : s.sum = -17 := by
    dsimp [s]
    rw [← complex_sum_re_eq_sum_map_re]
    have hre := congrArg Complex.re hqsum
    rw [complexRootPowerSum] at hre
    simp only [pow_one] at hre
    change (q.roots.map id).sum.re = (-17 : ℂ).re at hre
    rw [Multiset.map_id] at hre
    norm_num at hre
    exact hre
  have ssq : (s.map fun x ↦ x ^ 2).sum ≤ 9 := by
    dsimp [s]
    rw [Multiset.map_map]
    have hmap :
        q.roots.map (fun z ↦ (z.re : ℝ) ^ 2) =
          q.roots.map (fun z ↦ (z ^ 2).re) := by
      apply Multiset.map_congr rfl
      intro z hz
      have hzEq : z = (z.re : ℂ) := by
        apply Complex.ext
        · simp
        · simp [hrootReal z hz]
      rw [hzEq]
      simp only [pow_two, Complex.mul_re, Complex.ofReal_re,
        Complex.ofReal_im, mul_zero, sub_zero]
    change (q.roots.map (fun z ↦ z.re ^ 2)).sum ≤ 9
    rw [hmap]
    change (q.roots.map (Complex.re ∘ fun z ↦ z ^ 2)).sum ≤ 9
    rw [← Multiset.map_map]
    rw [← complex_sum_re_eq_sum_map_re]
    change (complexRootPowerSum q 2).re ≤ 9
    exact hqSq
  exact false_of_card_thirteen_sum_neg_seventeen_sq_sum_le_nine
    s scard ssum ssq

/-- Rational-divisibility form of the C16 terminal, ready for a rational
H16 defect matrix. -/
theorem false_of_cycleDefectQuadraticSixteen_dvd_rational_charpoly
    {n : Type*} [Fintype n] [DecidableEq n]
    (D : Matrix n n ℚ) (hcard : Fintype.card n = 15)
    (hdvd : cycleDefectQuadraticSixteen.map (Int.castRingHom ℚ) ∣ D.charpoly)
    (hD : (D.map (algebraMap ℚ ℂ)).IsHermitian)
    (htrace : Matrix.trace (D.map (algebraMap ℚ ℂ)) = -7)
    (htraceSq :
      (Matrix.trace ((D.map (algebraMap ℚ ℂ)) ^ 2)).re ≤ 63) : False := by
  obtain ⟨q, hqfactor⟩ := hdvd
  have hq : q ≠ 0 := by
    intro hzero
    rw [hzero, mul_zero] at hqfactor
    exact D.charpoly_monic.ne_zero hqfactor
  have hqmap : q.map (algebraMap ℚ ℂ) ≠ 0 := by
    simpa using
      (Polynomial.map_injective _ (algebraMap ℚ ℂ).injective).ne hq
  have hfactor :
      (D.map (algebraMap ℚ ℂ)).charpoly =
        cycleDefectQuadraticSixteen.map (Int.castRingHom ℂ) *
          q.map (algebraMap ℚ ℂ) := by
    rw [Matrix.charpoly_map, hqfactor, Polynomial.map_mul, Polynomial.map_map]
    congr 1
  exact false_of_cycleDefectQuadraticSixteen_charpoly_factor
    (D.map (algebraMap ℚ ℂ)) hD hcard hqmap hfactor htrace htraceSq

/-- The golden quadratic also cannot occur in the 15-dimensional
nonprincipal spectrum: its second moment is already the whole budget, while
the complementary first moment is forced to be `-18`. -/
theorem false_of_cycleDefectQuadraticFive_charpoly_factor
    {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℂ) (hA : A.IsHermitian)
    {q : ℂ[X]} (hq : q ≠ 0)
    (hfactor : A.charpoly =
      cycleDefectQuadraticFive.map (Int.castRingHom ℂ) * q)
    (htrace : Matrix.trace A = -7)
    (htraceSq : (Matrix.trace (A ^ 2)).re ≤ 63) : False := by
  let f : ℂ[X] := cycleDefectQuadraticFive.map (Int.castRingHom ℂ)
  have hf : f ≠ 0 := (cycleDefectQuadraticFive_monic.map _).ne_zero
  have htotalOne := complexRootPowerSum_charpoly_eq_trace_pow A hA 1
  have haddOne := complexRootPowerSum_mul hf hq 1
  rw [hfactor, haddOne, cycleDefectQuadraticFive_complexRootPowerSum_one]
      at htotalOne
  simp only [pow_one, htrace] at htotalOne
  have hqsum : complexRootPowerSum q 1 = -18 := by
    linear_combination htotalOne
  have htotalTwo := complexRootPowerSum_charpoly_eq_trace_pow A hA 2
  have haddTwo := complexRootPowerSum_mul hf hq 2
  have hqSq : (complexRootPowerSum q 2).re ≤ 0 := by
    rw [← htotalTwo, hfactor, haddTwo,
      cycleDefectQuadraticFive_complexRootPowerSum_two] at htraceSq
    norm_num at htraceSq ⊢
    linarith
  have hrootReal : ∀ z ∈ q.roots, z.im = 0 := by
    intro z hz
    have hzchar : z ∈ A.charpoly.roots := by
      rw [hfactor, roots_mul (mul_ne_zero hf hq), Multiset.mem_add]
      exact Or.inr hz
    rw [hA.roots_charpoly_eq_eigenvalues] at hzchar
    obtain ⟨i, _hi, rfl⟩ := Multiset.mem_map.mp hzchar
    simp
  let s : Multiset ℝ := q.roots.map Complex.re
  have ssum : s.sum = -18 := by
    dsimp [s]
    rw [← complex_sum_re_eq_sum_map_re]
    have hre := congrArg Complex.re hqsum
    rw [complexRootPowerSum] at hre
    simp only [pow_one] at hre
    change (q.roots.map id).sum.re = (-18 : ℂ).re at hre
    rw [Multiset.map_id] at hre
    norm_num at hre
    exact hre
  have ssq : (s.map fun x ↦ x ^ 2).sum ≤ 0 := by
    dsimp [s]
    rw [Multiset.map_map]
    have hmap :
        q.roots.map (fun z ↦ (z.re : ℝ) ^ 2) =
          q.roots.map (fun z ↦ (z ^ 2).re) := by
      apply Multiset.map_congr rfl
      intro z hz
      have hzEq : z = (z.re : ℂ) := by
        apply Complex.ext
        · simp
        · simp [hrootReal z hz]
      rw [hzEq]
      simp only [pow_two, Complex.mul_re, Complex.ofReal_re,
        Complex.ofReal_im, mul_zero, sub_zero]
    change (q.roots.map (fun z ↦ z.re ^ 2)).sum ≤ 0
    rw [hmap]
    change (q.roots.map (Complex.re ∘ fun z ↦ z ^ 2)).sum ≤ 0
    rw [← Multiset.map_map, ← complex_sum_re_eq_sum_map_re]
    change (complexRootPowerSum q 2).re ≤ 0
    exact hqSq
  exact false_of_sum_neg_eighteen_sq_sum_le_zero s ssum ssq

theorem false_of_cycleDefectQuadraticFive_dvd_rational_charpoly
    {n : Type*} [Fintype n] [DecidableEq n]
    (D : Matrix n n ℚ)
    (hdvd : cycleDefectQuadraticFive.map (Int.castRingHom ℚ) ∣ D.charpoly)
    (hD : (D.map (algebraMap ℚ ℂ)).IsHermitian)
    (htrace : Matrix.trace (D.map (algebraMap ℚ ℂ)) = -7)
    (htraceSq :
      (Matrix.trace ((D.map (algebraMap ℚ ℂ)) ^ 2)).re ≤ 63) : False := by
  obtain ⟨q, hqfactor⟩ := hdvd
  have hq : q ≠ 0 := by
    intro hzero
    rw [hzero, mul_zero] at hqfactor
    exact D.charpoly_monic.ne_zero hqfactor
  have hqmap : q.map (algebraMap ℚ ℂ) ≠ 0 := by
    simpa using
      (Polynomial.map_injective _ (algebraMap ℚ ℂ).injective).ne hq
  have hfactor :
      (D.map (algebraMap ℚ ℂ)).charpoly =
        cycleDefectQuadraticFive.map (Int.castRingHom ℂ) *
          q.map (algebraMap ℚ ℂ) := by
    rw [Matrix.charpoly_map, hqfactor, Polynomial.map_mul, Polynomial.map_map]
    congr 1
  exact false_of_cycleDefectQuadraticFive_charpoly_factor
    (D.map (algebraMap ℚ ℂ)) hD hqmap hfactor htrace htraceSq

end

end Erdos85
