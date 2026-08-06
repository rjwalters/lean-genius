import Proofs.Erdos85CyclotomicResultantNorm
import Proofs.Erdos85ChebyshevConductor
import Mathlib.RingTheory.Polynomial.Cyclotomic.Roots
import Mathlib.Tactic.ComputeDegree

/-!
# Integral factorization of the cycle value `C_n(13) - 2` by conductor resultants

The executable certificate layer verifies numerically that
`C_n(13) - 2 = 11 * (15 if 2 ∣ n) * ∏_{k ∣ n, k ≥ 3} candidate(k)²` in the
range `3 ≤ n ≤ 185`.  This file proves the matching *algebraic* factorization
`C_n(13) - 2 = 11 * (15 if 2 ∣ n) * ∏_{k ∣ n, k ≥ 3} Res_k` where `Res_k` is
the integral cyclotomic resultant, and cancels the two by strong induction:
every conductor resultant in the exact boundary range is the square of the
native-certified candidate.

The engine is the evaluation formula for the resultant of `X^n - 1` against
the quadratic `13X - X² - 1`: over the algebraic closure the roots of the
quadratic are `z, z⁻¹` with `z + z⁻¹ = 13`, so the resultant collapses to
`(-1)^(n+1) * (z^n + z⁻ⁿ - 2) = (-1)^(n+1) * (C_n(13) - 2)` by the Chebyshev
trace identity.
-/

open Polynomial

namespace Erdos85

noncomputable section

/-- The quadratic `13X - X² - 1` has degree two. -/
theorem degreeFourteenCyclotomicQuadraticInt_natDegree :
    degreeFourteenCyclotomicQuadraticInt.natDegree = 2 := by
  unfold degreeFourteenCyclotomicQuadraticInt
  compute_degree!

theorem natDegree_X_pow_sub_one_int (n : ℕ) :
    (Polynomial.X ^ n - 1 : Polynomial ℤ).natDegree = n := by
  rw [← Polynomial.C_1, Polynomial.natDegree_X_pow_sub_C]

/-- Scalar cancellation engine: `u² = 1` and `A·B = 1` collapse the signed
triple product. -/
theorem signed_triple_product_collapse {K : Type*} [CommRing K]
    (u A B : K) (hu : u * u = 1) (hAB : A * B = 1) :
    u * ((u * (A - 1)) * (u * (B - 1))) = u * -1 * (A + B - 2) := by
  linear_combination u ^ 3 * hAB + u * (2 - A - B) * hu

/-- **Resultant of `X^n - 1` with the boundary quadratic.**  Over the
algebraic closure the quadratic factors through `z, z⁻¹` with
`z + z⁻¹ = 13`, giving the Chebyshev value `C_n(13) - 2` up to sign. -/
theorem X_pow_sub_one_resultant_thirteen {n : ℕ} (hn : 0 < n) :
    (Polynomial.X ^ n - 1 : Polynomial ℤ).resultant
        degreeFourteenCyclotomicQuadraticInt n 2 =
      (-1) ^ (n + 1) * ((Chebyshev.C ℤ (n : ℤ)).eval 13 - 2) := by
  have hd2 := degreeFourteenCyclotomicQuadraticInt_natDegree
  haveI : NeZero ((n : ℕ) : AlgebraicClosure ℚ) := ⟨Nat.cast_ne_zero.mpr hn.ne'⟩
  obtain ⟨ζ, hζroot⟩ := IsAlgClosed.exists_root
    (Polynomial.cyclotomic n (AlgebraicClosure ℚ))
    (Polynomial.degree_cyclotomic_pos n _ hn).ne'
  have hζ : IsPrimitiveRoot ζ n := Polynomial.isRoot_cyclotomic_iff.mp hζroot
  obtain ⟨z, hzq⟩ := exists_quadratic_split (13 : AlgebraicClosure ℚ)
  have hz0 : z ≠ 0 := quadratic_root_ne_zero hzq
  have h13 : (13 : AlgebraicClosure ℚ) = z + z⁻¹ := quadratic_root_add_inv hzq
  set Q' : Polynomial (AlgebraicClosure ℚ) :=
    degreeFourteenCyclotomicQuadraticInt.map
      (Int.castRingHom (AlgebraicClosure ℚ)) with hQ'
  have hQdeg : Q'.natDegree = 2 := by
    rw [hQ', Polynomial.natDegree_map_eq_of_injective Int.cast_injective, hd2]
  have hQeval : ∀ w : AlgebraicClosure ℚ, Q'.eval w = 13 * w - w ^ 2 - 1 := by
    intro w
    simp only [hQ', degreeFourteenCyclotomicQuadraticInt, Polynomial.map_sub,
      Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_one,
      Polynomial.map_X, Polynomial.map_C, Polynomial.eval_sub,
      Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_one,
      Polynomial.eval_X, Polynomial.eval_C]
    norm_num
  have hfac : ∀ w : AlgebraicClosure ℚ,
      Q'.eval w = (-1) * ((w - z) * (w - z⁻¹)) := by
    intro w
    rw [hQeval w, h13]
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
  have hcheb : (Chebyshev.C (AlgebraicClosure ℚ) (n : ℤ)).eval 13 =
      z ^ n + (z⁻¹) ^ n := by
    rw [h13]
    exact chebyshev_C_eval_add_inv n hz0
  have hneg : ((-1 : AlgebraicClosure ℚ)) ^ n * (-1) ^ n = 1 := by
    rw [← mul_pow]; norm_num
  have hK : Polynomial.resultant
      ((Polynomial.X ^ n - 1 : Polynomial ℤ).map
        (Int.castRingHom (AlgebraicClosure ℚ))) Q' n 2 =
      (-1) ^ (n + 1) *
        ((Chebyshev.C (AlgebraicClosure ℚ) (n : ℤ)).eval 13 - 2) := by
    rw [hmapped, hstep, h1, h2, hcheb, pow_succ]
    exact signed_triple_product_collapse _ _ _ hneg hzn
  -- transfer along the injective cast
  have hevalcast : (((Chebyshev.C ℤ (n : ℤ)).eval 13 : ℤ) : AlgebraicClosure ℚ) =
      (Chebyshev.C (AlgebraicClosure ℚ) (n : ℤ)).eval 13 := by
    rw [← Polynomial.Chebyshev.map_C (Int.castRingHom (AlgebraicClosure ℚ)) (n : ℤ),
      Polynomial.eval_map,
      show (13 : AlgebraicClosure ℚ) = (Int.castRingHom (AlgebraicClosure ℚ)) 13 by
        simp,
      Polynomial.eval₂_at_apply]
    simp
  apply Int.cast_injective (α := AlgebraicClosure ℚ)
  calc ((Polynomial.resultant (Polynomial.X ^ n - 1 : Polynomial ℤ)
        degreeFourteenCyclotomicQuadraticInt n 2 : ℤ) : AlgebraicClosure ℚ)
      = Polynomial.resultant
          ((Polynomial.X ^ n - 1 : Polynomial ℤ).map
            (Int.castRingHom (AlgebraicClosure ℚ))) Q' n 2 :=
        (Polynomial.resultant_map_map (Polynomial.X ^ n - 1 : Polynomial ℤ)
          degreeFourteenCyclotomicQuadraticInt n 2
          (Int.castRingHom (AlgebraicClosure ℚ))).symm
    _ = (-1) ^ (n + 1) *
          ((Chebyshev.C (AlgebraicClosure ℚ) (n : ℤ)).eval 13 - 2) := hK
    _ = (((-1) ^ (n + 1) * ((Chebyshev.C ℤ (n : ℤ)).eval 13 - 2) : ℤ) :
          AlgebraicClosure ℚ) := by
        rw [← hevalcast]; push_cast; ring

/-- The same statement with the `natDegree` arguments of the surrounding
factorization theorem. -/
theorem X_pow_sub_one_resultant_thirteen' {n : ℕ} (hn : 0 < n) :
    (Polynomial.X ^ n - 1 : Polynomial ℤ).resultant
        degreeFourteenCyclotomicQuadraticInt
        (Polynomial.X ^ n - 1 : Polynomial ℤ).natDegree
        degreeFourteenCyclotomicQuadraticInt.natDegree =
      (-1) ^ (n + 1) * ((Chebyshev.C ℤ (n : ℤ)).eval 13 - 2) := by
  rw [natDegree_X_pow_sub_one_int, degreeFourteenCyclotomicQuadraticInt_natDegree]
  exact X_pow_sub_one_resultant_thirteen hn

/-- Joint recurrence invariant for the executable Chebyshev evaluator:
the loop stays at least `2` and tracks `C_k(13)`. -/
theorem chebyshevThirteenLoop_spec (m : ℕ) :
    ∀ (k : ℤ) (a b : ℕ), 2 ≤ a → a ≤ b →
      (a : ℤ) = (Chebyshev.C ℤ k).eval 13 →
      (b : ℤ) = (Chebyshev.C ℤ (k + 1)).eval 13 →
      2 ≤ chebyshevThirteenLoop m a b ∧
        ((chebyshevThirteenLoop m a b : ℕ) : ℤ) =
          (Chebyshev.C ℤ (k + m)).eval 13 := by
  induction m with
  | zero =>
      intro k a b h2 hab ha hb
      exact ⟨h2, by simpa [chebyshevThirteenLoop] using ha⟩
  | succ m IH =>
      intro k a b h2 hab ha hb
      have hb2 : 2 ≤ b := h2.trans hab
      have hle : b ≤ 13 * b - a := by omega
      have hcast : ((13 * b - a : ℕ) : ℤ) = 13 * (b : ℤ) - (a : ℤ) := by omega
      have hnext : ((13 * b - a : ℕ) : ℤ) =
          (Chebyshev.C ℤ (k + 1 + 1)).eval 13 := by
        rw [hcast, ha, hb, show k + 1 + 1 = k + 2 from by ring,
          Polynomial.Chebyshev.C_add_two]
        simp only [Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_X]
      have hstep := IH (k + 1) b (13 * b - a) hb2 hle hb hnext
      refine ⟨hstep.1, ?_⟩
      rw [show chebyshevThirteenLoop (m + 1) a b =
          chebyshevThirteenLoop m b (13 * b - a) from rfl,
        show ((m + 1 : ℕ) : ℤ) = (m : ℤ) + 1 from by push_cast; ring,
        show k + ((m : ℤ) + 1) = k + 1 + (m : ℤ) from by ring]
      exact hstep.2

theorem chebyshevThirteen_spec (n : ℕ) :
    2 ≤ chebyshevThirteen n ∧
      (chebyshevThirteen n : ℤ) = (Chebyshev.C ℤ (n : ℤ)).eval 13 := by
  have h := chebyshevThirteenLoop_spec n 0 2 13 (by norm_num) (by norm_num)
    (by simp [Polynomial.Chebyshev.C_zero])
    (by simp [Polynomial.Chebyshev.C_one])
  simpa [chebyshevThirteen] using h

theorem two_le_chebyshevThirteen (n : ℕ) : 2 ≤ chebyshevThirteen n :=
  (chebyshevThirteen_spec n).1

theorem chebyshevThirteen_cast (n : ℕ) :
    (chebyshevThirteen n : ℤ) = (Chebyshev.C ℤ (n : ℤ)).eval 13 :=
  (chebyshevThirteen_spec n).2

theorem cycleChebyshevThirteen_cast (n : ℕ) :
    (cycleChebyshevThirteen n : ℤ) = (Chebyshev.C ℤ (n : ℤ)).eval 13 - 2 := by
  unfold cycleChebyshevThirteen
  rw [Nat.cast_sub (two_le_chebyshevThirteen n), chebyshevThirteen_cast]
  norm_num

/-- The conductor-one block: `Res(Φ₁, 13X - X² - 1) = 11`. -/
theorem degreeFourteenCyclotomicResultant_one :
    degreeFourteenCyclotomicResultant 1 = 11 := by
  unfold degreeFourteenCyclotomicResultant
  rw [Polynomial.cyclotomic_one ℤ, degreeFourteenCyclotomicQuadraticInt_natDegree,
    show (Polynomial.X - 1 : Polynomial ℤ) = Polynomial.X - Polynomial.C 1 by
      rw [Polynomial.C_1],
    Polynomial.natDegree_X_sub_C,
    Polynomial.resultant_X_sub_C_left degreeFourteenCyclotomicQuadraticInt 2 1
      (le_of_eq degreeFourteenCyclotomicQuadraticInt_natDegree)]
  simp only [degreeFourteenCyclotomicQuadraticInt, Polynomial.eval_sub,
    Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_one,
    Polynomial.eval_X, Polynomial.eval_C]
  norm_num

/-- The conductor-two block: `Res(Φ₂, 13X - X² - 1) = -15`. -/
theorem degreeFourteenCyclotomicResultant_two :
    degreeFourteenCyclotomicResultant 2 = -15 := by
  unfold degreeFourteenCyclotomicResultant
  rw [Polynomial.cyclotomic_two ℤ, degreeFourteenCyclotomicQuadraticInt_natDegree,
    show (Polynomial.X + 1 : Polynomial ℤ) = Polynomial.X + Polynomial.C 1 by
      rw [Polynomial.C_1],
    Polynomial.natDegree_X_add_C,
    Polynomial.resultant_X_add_C_left degreeFourteenCyclotomicQuadraticInt 2 1
      (le_of_eq degreeFourteenCyclotomicQuadraticInt_natDegree)]
  simp only [degreeFourteenCyclotomicQuadraticInt, Polynomial.eval_sub,
    Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_one,
    Polynomial.eval_X, Polynomial.eval_C]
  norm_num

theorem divisors_filter_not_three_odd {n : ℕ} (hn : 0 < n) (hodd : ¬ 2 ∣ n) :
    n.divisors.filter (fun k => ¬ 3 ≤ k) = {1} := by
  ext k
  simp only [Finset.mem_filter, Nat.mem_divisors, Finset.mem_singleton]
  constructor
  · rintro ⟨⟨hdvd, -⟩, h3⟩
    have hk0 : k ≠ 0 := by
      rintro rfl
      exact hn.ne' (Nat.eq_zero_of_zero_dvd hdvd)
    have hk2 : k ≠ 2 := by
      rintro rfl
      exact hodd hdvd
    omega
  · rintro rfl
    exact ⟨⟨one_dvd n, hn.ne'⟩, by norm_num⟩

theorem divisors_filter_not_three_even {n : ℕ} (hn : 0 < n) (heven : 2 ∣ n) :
    n.divisors.filter (fun k => ¬ 3 ≤ k) = {1, 2} := by
  ext k
  simp only [Finset.mem_filter, Nat.mem_divisors, Finset.mem_insert,
    Finset.mem_singleton]
  constructor
  · rintro ⟨⟨hdvd, -⟩, h3⟩
    have hk0 : k ≠ 0 := by
      rintro rfl
      exact hn.ne' (Nat.eq_zero_of_zero_dvd hdvd)
    omega
  · rintro (rfl | rfl)
    · exact ⟨⟨one_dvd n, hn.ne'⟩, by norm_num⟩
    · exact ⟨⟨heven, hn.ne'⟩, by norm_num⟩

/-- **Integral divisor-product factorization.**  The rational frequency
factor times the product of the conductor resultants over the divisors of
`n` at least three recovers the integral cycle value `C_n(13) - 2`. -/
theorem freq_factor_mul_prod_resultant {n : ℕ} (hn : 0 < n) :
    (rationalCycleFrequencyFactor n : ℤ) *
        ∏ k ∈ n.divisors.filter (fun k => 3 ≤ k),
          degreeFourteenCyclotomicResultant k =
      (cycleChebyshevThirteen n : ℤ) := by
  have hsplit := Finset.prod_filter_mul_prod_filter_not n.divisors
    (fun k => 3 ≤ k) degreeFourteenCyclotomicResultant
  have hmain := prod_degreeFourteenCyclotomicResultant_eq_X_pow_sub_one_resultant hn
  rw [X_pow_sub_one_resultant_thirteen' hn] at hmain
  rw [cycleChebyshevThirteen_cast]
  by_cases heven : 2 ∣ n
  · rw [divisors_filter_not_three_even hn heven,
      Finset.prod_pair (by norm_num : (1 : ℕ) ≠ 2),
      degreeFourteenCyclotomicResultant_one,
      degreeFourteenCyclotomicResultant_two] at hsplit
    have hmod : n % 2 = 0 := by
      obtain ⟨c, rfl⟩ := heven
      omega
    have hpow : ((-1 : ℤ)) ^ (n + 1) = -1 :=
      Odd.neg_one_pow (Nat.odd_iff.mpr (by omega))
    rw [hpow] at hmain
    have hfac : (rationalCycleFrequencyFactor n : ℤ) = 165 := by
      simp [rationalCycleFrequencyFactor, hmod]
    rw [hfac]
    linarith [hsplit, hmain]
  · rw [divisors_filter_not_three_odd hn heven, Finset.prod_singleton,
      degreeFourteenCyclotomicResultant_one] at hsplit
    have hmod : n % 2 = 1 := by
      rcases Nat.mod_two_eq_zero_or_one n with h | h
      · exact absurd (Nat.dvd_of_mod_eq_zero h) heven
      · exact h
    have hpow : ((-1 : ℤ)) ^ (n + 1) = 1 :=
      Even.neg_one_pow (Nat.even_iff.mpr (by omega))
    rw [hpow, one_mul] at hmain
    have hfac : (rationalCycleFrequencyFactor n : ℤ) = 11 := by
      simp [rationalCycleFrequencyFactor, hmod]
    rw [hfac]
    linarith [hsplit, hmain]

theorem divisors_filter_three_eq_Icc_filter {n : ℕ} (hn : 0 < n) :
    n.divisors.filter (fun k => 3 ≤ k) =
      (Finset.Icc 3 n).filter (fun k => k ∣ n) := by
  ext k
  simp only [Finset.mem_filter, Nat.mem_divisors, Finset.mem_Icc]
  constructor
  · rintro ⟨⟨hdvd, -⟩, h3⟩
    exact ⟨⟨h3, Nat.le_of_dvd hn hdvd⟩, hdvd⟩
  · rintro ⟨⟨h3, -⟩, hdvd⟩
    exact ⟨⟨hdvd, hn.ne'⟩, h3⟩

/-- The certified candidate is positive throughout the boundary range. -/
theorem primitiveRealNormCandidate_ne_zero {n : ℕ} (h3 : 3 ≤ n)
    (h185 : n ≤ 185) : primitiveRealNormCandidate n ≠ 0 := by
  intro h0
  have h := primitiveRealNormCandidate_sqrt_ne_upto_185 n
    (Finset.mem_Icc.mpr ⟨h3, h185⟩)
  rw [h0] at h
  simp at h

/-- **Strong-induction cancellation.**  In the exact boundary range every
integral conductor resultant equals the square of the native-certified
candidate. -/
theorem degreeFourteenCyclotomicResultant_eq_sq :
    ∀ n : ℕ, 3 ≤ n → n ≤ 185 →
      degreeFourteenCyclotomicResultant n =
        (primitiveRealNormCandidate n : ℤ) ^ 2 := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n IH =>
    intro h3 h185
    have hn0 : 0 < n := by omega
    have hF := freq_factor_mul_prod_resultant hn0
    rw [divisors_filter_three_eq_Icc_filter hn0] at hF
    have hcert := cycleChebyshevThirteen_primitive_factorization_upto_185 n
      (Finset.mem_Icc.mpr ⟨h3, h185⟩)
    have hcert' : (cycleChebyshevThirteen n : ℤ) =
        (rationalCycleFrequencyFactor n : ℤ) *
          ∏ k ∈ (Finset.Icc 3 n).filter (fun k => k ∣ n),
            (primitiveRealNormCandidate k : ℤ) ^ 2 := by
      unfold primitiveRealNormDivisorProduct at hcert
      have hc := congrArg (fun m : ℕ => (m : ℤ)) hcert
      push_cast at hc
      exact hc
    have hFne : (rationalCycleFrequencyFactor n : ℤ) ≠ 0 := by
      rcases Nat.mod_two_eq_zero_or_one n with h | h <;>
        simp [rationalCycleFrequencyFactor, h]
    have hprods : ∏ k ∈ (Finset.Icc 3 n).filter (fun k => k ∣ n),
        degreeFourteenCyclotomicResultant k =
        ∏ k ∈ (Finset.Icc 3 n).filter (fun k => k ∣ n),
          (primitiveRealNormCandidate k : ℤ) ^ 2 :=
      mul_left_cancel₀ hFne (by rw [hF, hcert'])
    have hnmem : n ∈ (Finset.Icc 3 n).filter (fun k => k ∣ n) :=
      Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨h3, le_refl n⟩, dvd_refl n⟩
    rw [← Finset.mul_prod_erase _ _ hnmem,
      ← Finset.mul_prod_erase _ _ hnmem] at hprods
    have herase : ∏ k ∈ ((Finset.Icc 3 n).filter (fun k => k ∣ n)).erase n,
        degreeFourteenCyclotomicResultant k =
        ∏ k ∈ ((Finset.Icc 3 n).filter (fun k => k ∣ n)).erase n,
          (primitiveRealNormCandidate k : ℤ) ^ 2 := by
      refine Finset.prod_congr rfl fun k hk => ?_
      obtain ⟨hkne, hkA⟩ := Finset.mem_erase.mp hk
      obtain ⟨hkIcc, hkdvd⟩ := Finset.mem_filter.mp hkA
      obtain ⟨hk3, hkn⟩ := Finset.mem_Icc.mp hkIcc
      exact IH k (lt_of_le_of_ne hkn hkne) hk3 (le_trans hkn h185)
    rw [herase] at hprods
    have hne : ∏ k ∈ ((Finset.Icc 3 n).filter (fun k => k ∣ n)).erase n,
        (primitiveRealNormCandidate k : ℤ) ^ 2 ≠ 0 := by
      rw [Finset.prod_ne_zero_iff]
      intro k hk
      obtain ⟨hkne, hkA⟩ := Finset.mem_erase.mp hk
      obtain ⟨hkIcc, hkdvd⟩ := Finset.mem_filter.mp hkA
      obtain ⟨hk3, hkn⟩ := Finset.mem_Icc.mp hkIcc
      exact pow_ne_zero 2 (Nat.cast_ne_zero.mpr
        (primitiveRealNormCandidate_ne_zero hk3 (le_trans hkn h185)))
    exact mul_right_cancel₀ hne hprods

end

end Erdos85
