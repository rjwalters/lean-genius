import Proofs.Erdos85ResultantFactorization
import Proofs.Erdos85DegreeEighteenNormCertificate

/-!
# Integral factorization of the cycle value `C_n(17) - 2` by conductor resultants

The executable certificate layer verifies numerically that
`C_n(17) - 2 = 15 * (19 if 2 ∣ n) * ∏_{k ∣ n, k ≥ 3} candidate(k)²` in the
range `3 ≤ n ≤ 309`.  This file proves the matching *algebraic* factorization
`C_n(17) - 2 = 15 * (19 if 2 ∣ n) * ∏_{k ∣ n, k ≥ 3} Res_k` where `Res_k` is
the integral cyclotomic resultant against the boundary quadratic
`17X - X² - 1`, and cancels the two by strong induction: every conductor
resultant in the exact boundary range is the square of the native-certified
candidate.

The generic engines (the norm-resultant identity, the signed product
collapse, and the divisor-filter combinatorics) are inherited from the
degree-fourteen chain; only the degree-eight quadratic and its evaluations
are new.
-/

open Polynomial

namespace Erdos85

noncomputable section

/-- Integral quadratic used in the degree-thirty-four resultant
construction. -/
def degreeEighteenCyclotomicQuadraticInt : Polynomial ℤ :=
  Polynomial.C 17 * Polynomial.X - Polynomial.X ^ 2 - 1

/-- The quadratic whose value at `z` is `z * (17 - (z + z⁻¹))`. -/
def degreeEighteenCyclotomicQuadratic : Polynomial ℚ :=
  degreeEighteenCyclotomicQuadraticInt.map (Int.castRingHom ℚ)

/-- Direct executable resultant replacing the Möbius quotient. -/
def degreeEighteenCyclotomicResultant (n : ℕ) : ℤ :=
  (Polynomial.cyclotomic n ℤ).resultant
    degreeEighteenCyclotomicQuadraticInt
    (Polynomial.cyclotomic n ℤ).natDegree
    degreeEighteenCyclotomicQuadraticInt.natDegree

theorem degreeEighteenCyclotomicQuadraticInt_map :
    degreeEighteenCyclotomicQuadraticInt.map (Int.castRingHom ℚ) =
      degreeEighteenCyclotomicQuadratic := by
  rfl

/-- The quadratic `17X - X² - 1` has degree two. -/
theorem degreeEighteenCyclotomicQuadraticInt_natDegree :
    degreeEighteenCyclotomicQuadraticInt.natDegree = 2 := by
  unfold degreeEighteenCyclotomicQuadraticInt
  compute_degree!

/-- The rational resultant in the norm theorem is the cast of the integral
resultant.  This isolates the remaining task as a purely integral product
factorization, with no field-extension API left. -/
theorem degreeEighteenCyclotomicResultant_rat_eq_intCast (n : ℕ) :
    (Polynomial.cyclotomic n ℚ).resultant
        degreeEighteenCyclotomicQuadratic
        (Polynomial.cyclotomic n ℚ).natDegree
        degreeEighteenCyclotomicQuadratic.natDegree =
      (degreeEighteenCyclotomicResultant n : ℚ) := by
  rw [← Polynomial.map_cyclotomic_int,
    ← degreeEighteenCyclotomicQuadraticInt_map]
  rw [Polynomial.natDegree_map_eq_of_injective
      Int.cast_injective (Polynomial.cyclotomic n ℤ),
    Polynomial.natDegree_map_eq_of_injective
      Int.cast_injective degreeEighteenCyclotomicQuadraticInt]
  simpa [degreeEighteenCyclotomicResultant] using
    Polynomial.resultant_map_map
      (Polynomial.cyclotomic n ℤ) degreeEighteenCyclotomicQuadraticInt
      (Polynomial.cyclotomic n ℤ).natDegree
      degreeEighteenCyclotomicQuadraticInt.natDegree (Int.castRingHom ℚ)

/-- Cyclotomic factorization turns the product of the conductor resultants
into one resultant against `X^n-1`.  This is the algebraic half of the
strong-induction comparison with the executable candidate product. -/
theorem prod_degreeEighteenCyclotomicResultant_eq_X_pow_sub_one_resultant
    {n : ℕ} (hn : 0 < n) :
    ∏ k ∈ n.divisors, degreeEighteenCyclotomicResultant k =
      (Polynomial.X ^ n - 1 : Polynomial ℤ).resultant
        degreeEighteenCyclotomicQuadraticInt
        (Polynomial.X ^ n - 1 : Polynomial ℤ).natDegree
        degreeEighteenCyclotomicQuadraticInt.natDegree := by
  rw [← Polynomial.prod_cyclotomic_eq_X_pow_sub_one hn ℤ]
  rw [Polynomial.resultant_prod_left]
  · simp [degreeEighteenCyclotomicResultant]
  · simp only [(Polynomial.cyclotomic.monic _ ℤ).leadingCoeff,
      Finset.prod_const_one]
    norm_num
  · exact le_rfl

theorem degreeEighteenCyclotomicQuadratic_aeval
    {L : Type*} [Field L] [CharZero L] {z : L} (hz : z ≠ 0) :
    Polynomial.aeval z degreeEighteenCyclotomicQuadratic =
      z * ((17 : L) - (z + z⁻¹)) := by
  simp [degreeEighteenCyclotomicQuadratic,
    degreeEighteenCyclotomicQuadraticInt, Polynomial.aeval_def,
    Polynomial.eval₂_map]
  norm_num
  field_simp [hz]
  ring

/-- **Direct resultant bridge.**  For a primitive root of order at least
three, the square of the real-trace minimal-polynomial value at `17` is the
executable cyclotomic resultant with the quadratic above. -/
theorem primitiveTrace_minpoly_eval_seventeen_sq_eq_cyclotomic_resultant
    {L : Type*} [Field L] [CharZero L]
    {n : ℕ} {z : L} (hz : IsPrimitiveRoot z n) (hn : 3 ≤ n)
    [IsCyclotomicExtension {n} ℚ L] :
    (minpoly ℚ (z + z⁻¹)).eval 17 *
        (minpoly ℚ (z + z⁻¹)).eval 17 =
      (Polynomial.cyclotomic n ℚ).resultant
        degreeEighteenCyclotomicQuadratic
        (Polynomial.cyclotomic n ℚ).natDegree
        degreeEighteenCyclotomicQuadratic.natDegree := by
  have hn0 : n ≠ 0 := Nat.ne_of_gt (lt_of_lt_of_le (by norm_num) hn)
  letI : NeZero n := ⟨hn0⟩
  have hirr : Irreducible (Polynomial.cyclotomic n ℚ) :=
    Polynomial.cyclotomic.irreducible_rat (NeZero.pos n)
  have hnormZ : Algebra.norm ℚ z = 1 :=
    hz.norm_eq_one (by omega) hirr
  have hresultant :=
    norm_aeval_primitiveRoot_eq_cyclotomic_resultant
      hz hn0 degreeEighteenCyclotomicQuadratic
  rw [degreeEighteenCyclotomicQuadratic_aeval (hz.ne_zero hn0),
    map_mul, hnormZ, one_mul] at hresultant
  have hnormTrace := norm_rat_sub_primitiveTrace_eq_minpoly_eval_sq
    hz hn (17 : ℚ)
  have hnormTrace' :
      Algebra.norm ℚ ((17 : L) - (z + z⁻¹)) =
        (minpoly ℚ (z + z⁻¹)).eval 17 *
          (minpoly ℚ (z + z⁻¹)).eval 17 := by
    simpa using hnormTrace
  exact hnormTrace'.symm.trans hresultant

/-- **Resultant of `X^n - 1` with the boundary quadratic.**  Over the
algebraic closure the quadratic factors through `z, z⁻¹` with
`z + z⁻¹ = 17`, giving the Chebyshev value `C_n(17) - 2` up to sign. -/
theorem X_pow_sub_one_resultant_seventeen {n : ℕ} (hn : 0 < n) :
    (Polynomial.X ^ n - 1 : Polynomial ℤ).resultant
        degreeEighteenCyclotomicQuadraticInt n 2 =
      (-1) ^ (n + 1) * ((Chebyshev.C ℤ (n : ℤ)).eval 17 - 2) := by
  have hd2 := degreeEighteenCyclotomicQuadraticInt_natDegree
  haveI : NeZero ((n : ℕ) : AlgebraicClosure ℚ) := ⟨Nat.cast_ne_zero.mpr hn.ne'⟩
  obtain ⟨ζ, hζroot⟩ := IsAlgClosed.exists_root
    (Polynomial.cyclotomic n (AlgebraicClosure ℚ))
    (Polynomial.degree_cyclotomic_pos n _ hn).ne'
  have hζ : IsPrimitiveRoot ζ n := Polynomial.isRoot_cyclotomic_iff.mp hζroot
  obtain ⟨z, hzq⟩ := exists_quadratic_split (17 : AlgebraicClosure ℚ)
  have hz0 : z ≠ 0 := quadratic_root_ne_zero hzq
  have h17 : (17 : AlgebraicClosure ℚ) = z + z⁻¹ := quadratic_root_add_inv hzq
  set Q' : Polynomial (AlgebraicClosure ℚ) :=
    degreeEighteenCyclotomicQuadraticInt.map
      (Int.castRingHom (AlgebraicClosure ℚ)) with hQ'
  have hQdeg : Q'.natDegree = 2 := by
    rw [hQ', Polynomial.natDegree_map_eq_of_injective Int.cast_injective, hd2]
  have hQeval : ∀ w : AlgebraicClosure ℚ, Q'.eval w = 17 * w - w ^ 2 - 1 := by
    intro w
    simp only [hQ', degreeEighteenCyclotomicQuadraticInt, Polynomial.map_sub,
      Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_one,
      Polynomial.map_X, Polynomial.map_C, Polynomial.eval_sub,
      Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_one,
      Polynomial.eval_X, Polynomial.eval_C]
    norm_num
  have hfac : ∀ w : AlgebraicClosure ℚ,
      Q'.eval w = (-1) * ((w - z) * (w - z⁻¹)) := by
    intro w
    rw [hQeval w, h17]
    have hzz : z * z⁻¹ = 1 := mul_inv_cancel₀ hz0
    linear_combination hzz
  have hprod : (Polynomial.X ^ n - 1 : Polynomial (AlgebraicClosure ℚ)) =
      ∏ w ∈ Polynomial.nthRootsFinset n (1 : AlgebraicClosure ℚ),
        (Polynomial.X - Polynomial.C w) :=
    Polynomial.X_pow_sub_one_eq_prod hn hζ
  have hcard : (Polynomial.nthRootsFinset n (1 : AlgebraicClosure ℚ)).card = n :=
    hζ.card_nthRootsFinset
  have hprodeval : ∀ y : AlgebraicClosure ℚ,
      ∏ w ∈ Polynomial.nthRootsFinset n (1 : AlgebraicClosure ℚ), (y - w) =
        y ^ n - 1 := by
    intro y
    have := congrArg (Polynomial.eval y) hprod
    simpa [Polynomial.eval_prod] using this.symm
  -- the mapped resultant as a product of evaluations
  have hmapped : Polynomial.resultant
      ((Polynomial.X ^ n - 1 : Polynomial ℤ).map
        (Int.castRingHom (AlgebraicClosure ℚ))) Q' n 2 =
      ∏ w ∈ Polynomial.nthRootsFinset n (1 : AlgebraicClosure ℚ),
        Q'.eval w := by
    have hmapXn : (Polynomial.X ^ n - 1 : Polynomial ℤ).map
        (Int.castRingHom (AlgebraicClosure ℚ)) =
        (Polynomial.X ^ n - 1 : Polynomial (AlgebraicClosure ℚ)) := by
      simp
    have hdeg : (∏ w ∈ Polynomial.nthRootsFinset n (1 : AlgebraicClosure ℚ),
        (Polynomial.X - Polynomial.C w)).natDegree = n := by
      rw [← hprod, ← Polynomial.C_1, Polynomial.natDegree_X_pow_sub_C]
    have hlead : ∏ w ∈ Polynomial.nthRootsFinset n (1 : AlgebraicClosure ℚ),
        (Polynomial.X - Polynomial.C w).leadingCoeff ≠ 0 := by
      have hone : ∀ w ∈ Polynomial.nthRootsFinset n (1 : AlgebraicClosure ℚ),
          (Polynomial.X - Polynomial.C w).leadingCoeff = 1 :=
        fun w _ => Polynomial.monic_X_sub_C w
      rw [Finset.prod_congr rfl hone]
      simp
    have hres := Polynomial.resultant_prod_left
      (Polynomial.nthRootsFinset n (1 : AlgebraicClosure ℚ))
      (fun w => Polynomial.X - Polynomial.C w) Q' 2 hlead (le_of_eq hQdeg)
    rw [hdeg] at hres
    rw [hmapXn, hprod, hres]
    refine Finset.prod_congr rfl fun w _ => ?_
    rw [Polynomial.natDegree_X_sub_C]
    exact Polynomial.resultant_X_sub_C_left Q' 2 w (le_of_eq hQdeg)
  -- evaluate the product
  have h1 : ∏ w ∈ Polynomial.nthRootsFinset n (1 : AlgebraicClosure ℚ),
      (w - z) = (-1) ^ n * (z ^ n - 1) := by
    calc ∏ w ∈ Polynomial.nthRootsFinset n (1 : AlgebraicClosure ℚ), (w - z)
        = ∏ w ∈ Polynomial.nthRootsFinset n (1 : AlgebraicClosure ℚ),
            (-1) * (z - w) := Finset.prod_congr rfl fun w _ => by ring
      _ = (-1) ^ n * (z ^ n - 1) := by
          rw [Finset.prod_mul_distrib, Finset.prod_const, hcard, hprodeval z]
  have h2 : ∏ w ∈ Polynomial.nthRootsFinset n (1 : AlgebraicClosure ℚ),
      (w - z⁻¹) = (-1) ^ n * ((z⁻¹) ^ n - 1) := by
    calc ∏ w ∈ Polynomial.nthRootsFinset n (1 : AlgebraicClosure ℚ), (w - z⁻¹)
        = ∏ w ∈ Polynomial.nthRootsFinset n (1 : AlgebraicClosure ℚ),
            (-1) * (z⁻¹ - w) := Finset.prod_congr rfl fun w _ => by ring
      _ = (-1) ^ n * ((z⁻¹) ^ n - 1) := by
          rw [Finset.prod_mul_distrib, Finset.prod_const, hcard, hprodeval z⁻¹]
  have hstep : ∏ w ∈ Polynomial.nthRootsFinset n (1 : AlgebraicClosure ℚ),
      Q'.eval w = (-1) ^ n *
        ((∏ w ∈ Polynomial.nthRootsFinset n (1 : AlgebraicClosure ℚ), (w - z)) *
          ∏ w ∈ Polynomial.nthRootsFinset n (1 : AlgebraicClosure ℚ),
            (w - z⁻¹)) := by
    rw [Finset.prod_congr rfl fun w _ => hfac w, Finset.prod_mul_distrib,
      Finset.prod_mul_distrib, Finset.prod_const, hcard]
  have hzn : z ^ n * (z⁻¹) ^ n = 1 := by
    rw [← mul_pow, mul_inv_cancel₀ hz0, one_pow]
  have hcheb : (Chebyshev.C (AlgebraicClosure ℚ) (n : ℤ)).eval 17 =
      z ^ n + (z⁻¹) ^ n := by
    rw [h17]
    exact chebyshev_C_eval_add_inv n hz0
  have hneg : ((-1 : AlgebraicClosure ℚ)) ^ n * (-1) ^ n = 1 := by
    rw [← mul_pow]; norm_num
  have hK : Polynomial.resultant
      ((Polynomial.X ^ n - 1 : Polynomial ℤ).map
        (Int.castRingHom (AlgebraicClosure ℚ))) Q' n 2 =
      (-1) ^ (n + 1) *
        ((Chebyshev.C (AlgebraicClosure ℚ) (n : ℤ)).eval 17 - 2) := by
    rw [hmapped, hstep, h1, h2, hcheb, pow_succ]
    exact signed_triple_product_collapse _ _ _ hneg hzn
  -- transfer along the injective cast
  have hevalcast : (((Chebyshev.C ℤ (n : ℤ)).eval 17 : ℤ) : AlgebraicClosure ℚ) =
      (Chebyshev.C (AlgebraicClosure ℚ) (n : ℤ)).eval 17 := by
    rw [← Polynomial.Chebyshev.map_C (Int.castRingHom (AlgebraicClosure ℚ)) (n : ℤ),
      Polynomial.eval_map,
      show (17 : AlgebraicClosure ℚ) = (Int.castRingHom (AlgebraicClosure ℚ)) 17 by
        simp,
      Polynomial.eval₂_at_apply]
    simp
  apply Int.cast_injective (α := AlgebraicClosure ℚ)
  calc ((Polynomial.resultant (Polynomial.X ^ n - 1 : Polynomial ℤ)
        degreeEighteenCyclotomicQuadraticInt n 2 : ℤ) : AlgebraicClosure ℚ)
      = Polynomial.resultant
          ((Polynomial.X ^ n - 1 : Polynomial ℤ).map
            (Int.castRingHom (AlgebraicClosure ℚ))) Q' n 2 :=
        (Polynomial.resultant_map_map (Polynomial.X ^ n - 1 : Polynomial ℤ)
          degreeEighteenCyclotomicQuadraticInt n 2
          (Int.castRingHom (AlgebraicClosure ℚ))).symm
    _ = (-1) ^ (n + 1) *
          ((Chebyshev.C (AlgebraicClosure ℚ) (n : ℤ)).eval 17 - 2) := hK
    _ = (((-1) ^ (n + 1) * ((Chebyshev.C ℤ (n : ℤ)).eval 17 - 2) : ℤ) :
          AlgebraicClosure ℚ) := by
        rw [← hevalcast]; push_cast; ring

/-- The same statement with the `natDegree` arguments of the surrounding
factorization theorem. -/
theorem X_pow_sub_one_resultant_seventeen' {n : ℕ} (hn : 0 < n) :
    (Polynomial.X ^ n - 1 : Polynomial ℤ).resultant
        degreeEighteenCyclotomicQuadraticInt
        (Polynomial.X ^ n - 1 : Polynomial ℤ).natDegree
        degreeEighteenCyclotomicQuadraticInt.natDegree =
      (-1) ^ (n + 1) * ((Chebyshev.C ℤ (n : ℤ)).eval 17 - 2) := by
  rw [natDegree_X_pow_sub_one_int, degreeEighteenCyclotomicQuadraticInt_natDegree]
  exact X_pow_sub_one_resultant_seventeen hn

/-- Joint recurrence invariant for the executable Chebyshev evaluator:
the loop stays at least `2` and tracks `C_k(17)`. -/
theorem chebyshevSeventeenLoop_spec (m : ℕ) :
    ∀ (k : ℤ) (a b : ℕ), 2 ≤ a → a ≤ b →
      (a : ℤ) = (Chebyshev.C ℤ k).eval 17 →
      (b : ℤ) = (Chebyshev.C ℤ (k + 1)).eval 17 →
      2 ≤ chebyshevSeventeenLoop m a b ∧
        ((chebyshevSeventeenLoop m a b : ℕ) : ℤ) =
          (Chebyshev.C ℤ (k + m)).eval 17 := by
  induction m with
  | zero =>
      intro k a b h2 hab ha hb
      exact ⟨h2, by simpa [chebyshevSeventeenLoop] using ha⟩
  | succ m IH =>
      intro k a b h2 hab ha hb
      have hb2 : 2 ≤ b := h2.trans hab
      have hle : b ≤ 17 * b - a := by omega
      have hcast : ((17 * b - a : ℕ) : ℤ) = 17 * (b : ℤ) - (a : ℤ) := by omega
      have hnext : ((17 * b - a : ℕ) : ℤ) =
          (Chebyshev.C ℤ (k + 1 + 1)).eval 17 := by
        rw [hcast, ha, hb, show k + 1 + 1 = k + 2 from by ring,
          Polynomial.Chebyshev.C_add_two]
        simp only [Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_X]
      have hstep := IH (k + 1) b (17 * b - a) hb2 hle hb hnext
      refine ⟨hstep.1, ?_⟩
      rw [show chebyshevSeventeenLoop (m + 1) a b =
          chebyshevSeventeenLoop m b (17 * b - a) from rfl,
        show ((m + 1 : ℕ) : ℤ) = (m : ℤ) + 1 from by push_cast; ring,
        show k + ((m : ℤ) + 1) = k + 1 + (m : ℤ) from by ring]
      exact hstep.2

theorem chebyshevSeventeen_spec (n : ℕ) :
    2 ≤ chebyshevSeventeen n ∧
      (chebyshevSeventeen n : ℤ) = (Chebyshev.C ℤ (n : ℤ)).eval 17 := by
  have h := chebyshevSeventeenLoop_spec n 0 2 17 (by norm_num) (by norm_num)
    (by simp [Polynomial.Chebyshev.C_zero])
    (by simp [Polynomial.Chebyshev.C_one])
  simpa [chebyshevSeventeen] using h

theorem two_le_chebyshevSeventeen (n : ℕ) : 2 ≤ chebyshevSeventeen n :=
  (chebyshevSeventeen_spec n).1

theorem chebyshevSeventeen_cast (n : ℕ) :
    (chebyshevSeventeen n : ℤ) = (Chebyshev.C ℤ (n : ℤ)).eval 17 :=
  (chebyshevSeventeen_spec n).2

theorem cycleChebyshevSeventeen_cast (n : ℕ) :
    (cycleChebyshevSeventeen n : ℤ) = (Chebyshev.C ℤ (n : ℤ)).eval 17 - 2 := by
  unfold cycleChebyshevSeventeen
  rw [Nat.cast_sub (two_le_chebyshevSeventeen n), chebyshevSeventeen_cast]
  norm_num

/-- The conductor-one block: `Res(Φ₁, 17X - X² - 1) = 15`. -/
theorem degreeEighteenCyclotomicResultant_one :
    degreeEighteenCyclotomicResultant 1 = 15 := by
  unfold degreeEighteenCyclotomicResultant
  rw [Polynomial.cyclotomic_one ℤ, degreeEighteenCyclotomicQuadraticInt_natDegree,
    show (Polynomial.X - 1 : Polynomial ℤ) = Polynomial.X - Polynomial.C 1 by
      rw [Polynomial.C_1],
    Polynomial.natDegree_X_sub_C,
    Polynomial.resultant_X_sub_C_left degreeEighteenCyclotomicQuadraticInt 2 1
      (le_of_eq degreeEighteenCyclotomicQuadraticInt_natDegree)]
  simp only [degreeEighteenCyclotomicQuadraticInt, Polynomial.eval_sub,
    Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_one,
    Polynomial.eval_X, Polynomial.eval_C]
  norm_num

/-- The conductor-two block: `Res(Φ₂, 17X - X² - 1) = -19`. -/
theorem degreeEighteenCyclotomicResultant_two :
    degreeEighteenCyclotomicResultant 2 = -19 := by
  unfold degreeEighteenCyclotomicResultant
  rw [Polynomial.cyclotomic_two ℤ, degreeEighteenCyclotomicQuadraticInt_natDegree,
    show (Polynomial.X + 1 : Polynomial ℤ) = Polynomial.X + Polynomial.C 1 by
      rw [Polynomial.C_1],
    Polynomial.natDegree_X_add_C,
    Polynomial.resultant_X_add_C_left degreeEighteenCyclotomicQuadraticInt 2 1
      (le_of_eq degreeEighteenCyclotomicQuadraticInt_natDegree)]
  simp only [degreeEighteenCyclotomicQuadraticInt, Polynomial.eval_sub,
    Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_one,
    Polynomial.eval_X, Polynomial.eval_C]
  norm_num

/-- **Integral divisor-product factorization.**  The rational frequency
factor times the product of the conductor resultants over the divisors of
`n` at least three recovers the integral cycle value `C_n(17) - 2`. -/
theorem freq_factor_mul_prod_resultant_seventeen {n : ℕ} (hn : 0 < n) :
    (rationalCycleFrequencyFactorSeventeen n : ℤ) *
        ∏ k ∈ n.divisors.filter (fun k => 3 ≤ k),
          degreeEighteenCyclotomicResultant k =
      (cycleChebyshevSeventeen n : ℤ) := by
  have hsplit := Finset.prod_filter_mul_prod_filter_not n.divisors
    (fun k => 3 ≤ k) degreeEighteenCyclotomicResultant
  have hmain := prod_degreeEighteenCyclotomicResultant_eq_X_pow_sub_one_resultant hn
  rw [X_pow_sub_one_resultant_seventeen' hn] at hmain
  rw [cycleChebyshevSeventeen_cast]
  by_cases heven : 2 ∣ n
  · rw [divisors_filter_not_three_even hn heven,
      Finset.prod_pair (by norm_num : (1 : ℕ) ≠ 2),
      degreeEighteenCyclotomicResultant_one,
      degreeEighteenCyclotomicResultant_two] at hsplit
    have hmod : n % 2 = 0 := by
      obtain ⟨c, rfl⟩ := heven
      omega
    have hpow : ((-1 : ℤ)) ^ (n + 1) = -1 :=
      Odd.neg_one_pow (Nat.odd_iff.mpr (by omega))
    rw [hpow] at hmain
    have hfac : (rationalCycleFrequencyFactorSeventeen n : ℤ) = 285 := by
      simp [rationalCycleFrequencyFactorSeventeen, hmod]
    rw [hfac]
    linarith [hsplit, hmain]
  · rw [divisors_filter_not_three_odd hn heven, Finset.prod_singleton,
      degreeEighteenCyclotomicResultant_one] at hsplit
    have hmod : n % 2 = 1 := by
      rcases Nat.mod_two_eq_zero_or_one n with h | h
      · exact absurd (Nat.dvd_of_mod_eq_zero h) heven
      · exact h
    have hpow : ((-1 : ℤ)) ^ (n + 1) = 1 :=
      Even.neg_one_pow (Nat.even_iff.mpr (by omega))
    rw [hpow, one_mul] at hmain
    have hfac : (rationalCycleFrequencyFactorSeventeen n : ℤ) = 15 := by
      simp [rationalCycleFrequencyFactorSeventeen, hmod]
    rw [hfac]
    linarith [hsplit, hmain]

/-- The certified candidate is positive throughout the boundary range. -/
theorem primitiveRealNormCandidateSeventeen_ne_zero {n : ℕ} (h3 : 3 ≤ n)
    (h309 : n ≤ 309) : primitiveRealNormCandidateSeventeen n ≠ 0 :=
  (primitiveRealNormCandidateSeventeen_pos_upto_309 n
    (Finset.mem_Icc.mpr ⟨h3, h309⟩)).ne'

/-- **Strong-induction cancellation.**  In the exact boundary range every
integral conductor resultant equals the square of the native-certified
candidate. -/
theorem degreeEighteenCyclotomicResultant_eq_sq :
    ∀ n : ℕ, 3 ≤ n → n ≤ 309 →
      degreeEighteenCyclotomicResultant n =
        (primitiveRealNormCandidateSeventeen n : ℤ) ^ 2 := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n IH =>
    intro h3 h309
    have hn0 : 0 < n := by omega
    have hF := freq_factor_mul_prod_resultant_seventeen hn0
    rw [divisors_filter_three_eq_Icc_filter hn0] at hF
    have hcert := cycleChebyshevSeventeen_primitive_factorization_upto_309 n
      (Finset.mem_Icc.mpr ⟨h3, h309⟩)
    have hcert' : (cycleChebyshevSeventeen n : ℤ) =
        (rationalCycleFrequencyFactorSeventeen n : ℤ) *
          ∏ k ∈ (Finset.Icc 3 n).filter (fun k => k ∣ n),
            (primitiveRealNormCandidateSeventeen k : ℤ) ^ 2 := by
      unfold primitiveRealNormDivisorProductSeventeen at hcert
      have hc := congrArg (fun m : ℕ => (m : ℤ)) hcert
      push_cast at hc
      exact hc
    have hFne : (rationalCycleFrequencyFactorSeventeen n : ℤ) ≠ 0 := by
      rcases Nat.mod_two_eq_zero_or_one n with h | h <;>
        simp [rationalCycleFrequencyFactorSeventeen, h]
    have hprods : ∏ k ∈ (Finset.Icc 3 n).filter (fun k => k ∣ n),
        degreeEighteenCyclotomicResultant k =
        ∏ k ∈ (Finset.Icc 3 n).filter (fun k => k ∣ n),
          (primitiveRealNormCandidateSeventeen k : ℤ) ^ 2 :=
      mul_left_cancel₀ hFne (by rw [hF, hcert'])
    have hnmem : n ∈ (Finset.Icc 3 n).filter (fun k => k ∣ n) :=
      Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨h3, le_refl n⟩, dvd_refl n⟩
    rw [← Finset.mul_prod_erase _ _ hnmem,
      ← Finset.mul_prod_erase _ _ hnmem] at hprods
    have herase : ∏ k ∈ ((Finset.Icc 3 n).filter (fun k => k ∣ n)).erase n,
        degreeEighteenCyclotomicResultant k =
        ∏ k ∈ ((Finset.Icc 3 n).filter (fun k => k ∣ n)).erase n,
          (primitiveRealNormCandidateSeventeen k : ℤ) ^ 2 := by
      refine Finset.prod_congr rfl fun k hk => ?_
      obtain ⟨hkne, hkA⟩ := Finset.mem_erase.mp hk
      obtain ⟨hkIcc, hkdvd⟩ := Finset.mem_filter.mp hkA
      obtain ⟨hk3, hkn⟩ := Finset.mem_Icc.mp hkIcc
      exact IH k (lt_of_le_of_ne hkn hkne) hk3 (le_trans hkn h309)
    rw [herase] at hprods
    have hne : ∏ k ∈ ((Finset.Icc 3 n).filter (fun k => k ∣ n)).erase n,
        (primitiveRealNormCandidateSeventeen k : ℤ) ^ 2 ≠ 0 := by
      rw [Finset.prod_ne_zero_iff]
      intro k hk
      obtain ⟨hkne, hkA⟩ := Finset.mem_erase.mp hk
      obtain ⟨hkIcc, hkdvd⟩ := Finset.mem_filter.mp hkA
      obtain ⟨hk3, hkn⟩ := Finset.mem_Icc.mp hkIcc
      exact pow_ne_zero 2 (Nat.cast_ne_zero.mpr
        (primitiveRealNormCandidateSeventeen_ne_zero hk3 (le_trans hkn h309)))
    exact mul_right_cancel₀ hne hprods

end

end Erdos85
